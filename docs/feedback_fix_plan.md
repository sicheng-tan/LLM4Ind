# 错误反馈算法：待修复问题与修改方案

本文合并两轮审查：

1. 对话开始时指出的 **会直接算错 / 整条信号丢光** 的实现问题；
2. 对齐论文成本之后仍然存在的 **采集、打分、写回 prompt/routing** 问题。

**已经做完、本文不再当作待修项：**

- 有用性失败后不再做 singleton/pair 子集证明搜索；
- Vampire 有用性失败后不再第二次满超时 plain prove；
- 入口不再单独跑 3s 诊断，stats / difficulty / induction 挂在首次 60s prove 上；
- 子目标失败优先复用子目标自己的 `baseline_diag`。

下面都是 **仍会让反馈算错、空白或误导下一轮 LLM** 的项。改动按 P0 → P2 排；P0 建议先做。

---

## P0：信号根本读不到，或读到就是错的

### P0-1 CVC `get-difficulty` 解析几乎读不了真实 SMT

**现状：** `parse_cvc_difficulty` 用一层括号正则：

```python
r"\(\s*(\((?:[^()]|\([^()]*\))*\))\s+(\d+)\s*\)"
```

只允许「内部再套一层、且那一层里不再有括号」。真实断言例如

```text
((forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m)))) 10)
```

里 `(plus (succ n) m)` 已是两层，匹配失败。

**后果：** `hard_axioms` 常为空；`goal_difficulty_drop` / `axiom_difficulty_drop` 从不触发。CVC 最有特色的信号在真实题上等于没接上。

**改法：**

- 丢掉这层正则，对 `(get-difficulty)` 输出做 **括号平衡扫描**：外层 `( ... )` 里每一项是 `( <s-expr> <int> )`。
- 用 SMT-LIB 的 s-expr 切分，不要假设 forall 体只有一层应用。
- 单测至少覆盖：嵌套 `plus/succ`、`(not (forall ...))`、named assertion。

### P0-2 目标难度用子串碰运气

**现状：**

```python
if "(not" in term and "forall" in term:
    return s
```

取 difficulty 列表里 **第一条** 同时含子串的项。列表按分数降序，高难度否定公理会抢在真正目标前面；公理体内的嵌套 `(not` / `forall` 也会误中。

公理 drop 还要求 **term 字符串完全一致**。公理因变容易而掉出 top-12 时，这本来是最强进展信号，现在完全不计。

**改法：**

- 目标项：用问题文件里 **proof-goal 块**（`(assert (not (forall ...)))` 或模板里标记的 goal）做规范化后精确/α 等价匹配，禁止子串。
- 公理项：从 goal 以外的 `(assert …)` 里匹配。
- 公理从 baseline 的 difficulty 列表 **消失**（candidate 的 top-K 里不再出现）应记为 drop，而不是要求同一字符串仍在列表里且分数下降。
- `derive_repair_hints` 的 `hard_axioms` / `goal_fragments` 用同一套分类，不要再用 `"forall" in t and "(not" not in t`。

### P0-3 Vampire `User error` 检测写错

**现状：** `classify_status` 判断 `"user:" in text`。Vampire 常见是 `User error:`，小写后是 `user error:`，**不包含** `user:`（`user` 后是空格不是冒号）。

**后果：** 语法/文件/策略错误被标成 `unknown`/`timeout`，progress 不走 `solver_error` 负分，repair 当成普通卡住。

**改法：** 匹配 `user error`（以及 `User error:` / `error: ...` 里明确的输入错误）。单测用真实 Vampire 报错片段。不要用 `"user:"`。

### P0-4 `is_relative_gain` 把计数地板用在 per-second rate 上

**现状：** 非 rare 事件要求 `(cand - ref) > max(1.0, 0.02 * ref)`。`1.0` 是按 **计数 +1** 设计的，progress 比较的是 **次/秒**。

**后果：** `0.4/s → 0.9/s` 这种相对很明显的增益被丢掉；高流量 `50/s → 60/s` 又很容易过线。相对化做了一半，单位错了。`pct_label` 里对 rate 用 `max(ref, 1)` 也会把小于 1 的分母撑大，百分比显示偏小。

**改法：**

- `is_relative_gain` 增加 `kind="count"|"rate"`，或对 rate **取消 `max(1.0, …)`**，只保留相对 log-gain 和 `NOISE_FRAC * ref`。
- 若坚持「至少多 1 次事件」：用 `(rate_c - rate_r) * elapsed > 1` 把地板换算回计数。
- `pct_label` 对 rate 用 `max(ref, ε)`，不要 `max(ref, 1)`。

### P0-5 `STAT_KEY_PATTERNS` 是死代码，且模式会双计

**现状：** `cvc5_runner.py` 顶部 `STAT_KEY_PATTERNS` 里 `INST_E_MATCHING(?:_SIMPLE)?` 会把 `E_MATCHING_SIMPLE` 计进 `INST_E_MATCHING`，再和下一行相加。实际 `parse_cvc_stats` 走精确 key 列表，这组 pattern **从未使用**。probe 无 reference 分支还在兼容 `SKOLEMIZE` 与 `QUANTIFIERS_SKOLEMIZE` 两套键。

**改法：** 删除 `STAT_KEY_PATTERNS`（或若要用必须改成互斥、非重叠的 key）。全仓库统一用 `parse_cvc_stats` 的全名键。

---

## P1：相对化之后判定语义被拧歪

### P1-1 Vampire / CVC mix 条件叠了两个不等式，真正生效的不是「份额」

| hint | 现在的条件 | 实际含义 |
|---|---|---|
| Vampire `need_rewrite` | `ind_share ≥ 0.08` **且** `dem/ind < 8` | 后者已蕴含 `ind_share > 1/9`，0.08 从不单独生效 |
| Vampire `need_induction` | `dem_share ≥ 0.85` **且** `ind/dem < 0.02` | 后者要求归纳不到重写的 2%，即 demod 份额约 ≥ 98%；`ind=8, dem=400` 这种「几乎没归纳」**不会**提示缺归纳 |
| CVC `need_rewrite` | `skol_share ≥ 0.01` **且** `inst/skol < 10` | `skol=100, inst=900` 仍会被说成「实例化稀疏」 |
| CVC `need_stronger` | `conj_share ≥ 0.25` **且** `skol/conj ≤ 0.05` | 与 `need_rewrite` 抢同一条失败路径 |

**改法：** 每条 hint **只保留一个有语义的不等式**（份额 **或** 比，不要两个叠着还声称是份额）。大计数时不要把 `inst/skol < 10` 当成稀疏：改为相对 baseline 的 mix **变化**，或对绝对活动量设「足够大才诊断 mix」。`need_rewrite` 与 `need_stronger` 允许同时给出，但 prompt 里要标优先级，不要 `if/elif` 把另一条掐掉却不说明。

### P1-2 进度分把相关计数当成独立证据

Vampire 上 `Fw demodulations` 与 `Fw demodulations to eq. taut.` 几乎总是一起涨；CVC 上 INST 与 CONJ 也高度相关。评分各算一条 `strong`，轻易避开 `weak_single_signal` 打折。

爆炸惩罚不对称：Vampire 看 generated clauses，且 **demod 增加不算有产出**；CVC 用 conjecture-gen 当体积，**INST 暴涨不罚**。只把搜索撑大的引理在 CVC 上仍可能靠 `more_instantiations` 拿到正分。

整数归纳计数已解析，却不进 `compute_progress_score`。整数题上结构归纳为 0、区间归纳很高时，进度面是瞎的。

**改法：**

- 相关计数合成一组信号（demod 家族一条，induction 家族一条含 integer interval）。
- 爆炸：有体积暴涨且 **对应产出组没有相对增益** 才罚；CVC 的 INST 暴涨无 skolem/difficulty drop 应罚。
- Vampire progress 加入 `Integer*Induction`，与结构归纳同一 `ind_*` 通道或单独 `rare` 通道。

### P1-3 60s baseline 与 3s sidecar 不可比（对齐成本后新暴露）

baseline 来自入口 60s prove；candidate/control 来自 3s diagnostic。CVC diagnostic 在 `collect_difficulty=True` 时仍是 **两次进程**。Vampire 入口 prove 开 `--show_induction`，sidecar 候选常关。

**改法（选一，推荐 A）：**

- **A（推荐）：** sidecar 与 baseline **同一 profile、同一超时量级** 不现实；改为 sidecar 也只比 **同一次 3s 协议**：baseline 若来自 60s，则 **再跑一条 3s 的 goal-only diagnostic 当 progress 的 baseline**（可缓存为 `baseline_diag_short`），与 control/candidate 对齐。60s prove 的 difficulty/induction **只用于 repair hint**，不用于 progress 分。
- **B：** sidecar 取消 difficulty 对比，只比 rate；hint 仍用 60s 结果。
- CVC `run_cvc_diagnostic`：把 `produce-difficulty` + `get-difficulty` **注入同一次** `--stats` 进程，去掉第二次 `run_cvc_difficulty`。

### P1-4 有用性 60s 默认不采 stats，却从空结果衍生 hint / routing utility

`verify_combined_lemmas` 调用 `run_cvc_routed` 未开 `collect_stats`。`record_solver_attempt` 仍对这份结果 `derive_repair_hints` 和 `profile_utility_from_stats`，写出空洞 timeout hint，并污染 pair/profile 历史。

**改法：** 有用性失败时 **不要** 从空 stats 的 portfolio 结果衍生 repair/utility；hint 只来自首次 prove 缓存 + sidecar。若需要有用性 run 的 status，只记录 `status/elapsed/strategy`，`signals` 留空。

---

## P2：闭环里功劳、提示窗口、控制流

### P2-1 progress 与 useless 对 LLM 说法相反

sidecar 仍按 **singleton** 记功。整组写入 `useless_lemma_groups`（「不要再生成这一组」），同时组成员进入 `progress_lemmas`（「优先 refine 这些」）。只在组合里才有用的桥接引理评不到；单独好看、整组无用的 lemma 会被强化进下一轮。

平凡引理只跳过 `(= t t)` 一类，`(=> P P)`、交换律恒真、control 同型的 `(forall ((x T)) (= x x))` 仍可能进诊断。

**改法：**

- progress 记在 **组** 上，或只把「相对 control 有增益且不在 useless 矛盾叙事里」的 lemma 标为 refine。
- prompt 明确：useless 的是 **这一组搭配**，progress 是 **单条相对 control 的搜索变化**，不要两条指令对着同一批公式打架。
- 扩展 trivial 检测：α 等价恒真、与 control lemma 同型。

### P2-2 repair hint 只保留最后 4 条，按插入序截断

去重键是 `(kind, detail[:80])`。入口 60s 的 `high_difficulty` / `induction_stuck` 会被后面的 `no_progress` / `timeout` 挤掉。不同 context 的同类 timeout 各占一格。

**改法：** 按 **kind 去重保留最新**，并 **固定保留一类「问题结构」hint**（difficulty / induction_focus）不被 timeout 挤掉。窗口按 kind 配额（例如结构 2 + 本轮进展 2），不要 `existing[-4:]`。

### P2-3 空 LLM 输出每次 attempt 立刻 100s 再证原目标

调用抛错：不加时，下一 attempt。返回空列表：立刻 `RETRY_CVC_TIMEOUT`（100s）。不是等 2×3 轮生成用完，也不是超时累积。

**改法：** 空输出与调用失败一样进入下一 attempt；**该节点全部 LLM attempt 失败后最多加时一次**。不要每轮空列表都付 100s。

### P2-4 子目标失败把父组所有 lemma 记成 unproved

挡住的可能只是一条。LLM 会以为整组都「有用但不可证」。

**改法：** 只标记 **blocking_subgoal 对应的那条**（文件名/引理名能对上的）；其余保持 useful 或不再写入 unproved。

### P2-5 Probe 无 reference 时退回绝对阈值

`gen > 2000`、`conj > 400 and skol ≤ 1` 等正是相对化要消掉的门槛。第一次 probe 没有对照时，大题/小题排序回到旧偏差。

**改法：** 无 reference 时只用理论静态分 + status，或用 **同一题上其它 profile 的 probe 当 reference**（seed 里其实已经有 reference，要保证所有调用都传入）。禁止绝对 `> 2000 / > 400`。

### P2-6 `produce-difficulty` 只插在 `(set-logic` 之后

没有 `(set-logic …)` 的 SMT 不会打开 difficulty，`get-difficulty` 可能报错，整条 difficulty 信号为空（与 P0-1 叠加）。

**改法：** 若没有 `set-logic`，在首条非注释命令后插入 `(set-option :produce-difficulty true)`；`get-difficulty` 仍紧跟第一条 `(check-sat)`。

---

## 建议实施顺序

| 批次 | 项 | 目的 |
|---|---|---|
| 1 | P0-1, P0-2, P0-3, P0-5 | 先让 difficulty / 错误状态真的存在 |
| 2 | P0-4, P1-1, P1-2 | 让相对化门槛和 mix hint 语义与文档一致 |
| 3 | P1-3, P1-4 | 让 progress 与 hint 来源可比、不写空 hint |
| 4 | P2-1–P2-6 | 闭环与预算：prompt 不打架、空 LLM 不加时、probe 不再用绝对爆炸阈值 |

批次 1 不改控制流，只改解析和分类，适合先补单测再改评分。

## 单测建议（批次 1 最低集）

1. `parse_cvc_difficulty`：嵌套 `plus/succ` forall 能读出分数。
2. `goal_diff`：高难度否定公理排在前面时，仍选中 proof-goal 对应项。
3. `classify_status`：`User error: ...` → `error`；`user:` 子串不作为唯一条件。
4. `is_relative_gain`：rate `0.4 → 0.9` 为增益；count `100 → 101` 非 rare 不为增益。
5. 确认 `STAT_KEY_PATTERNS` 删除后 `parse_cvc_stats` 与 progress 键一致。
