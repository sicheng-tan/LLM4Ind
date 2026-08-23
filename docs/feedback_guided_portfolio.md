# Feedback-Guided Theory Portfolio

本文记录当前 Feedback-Guided 设计（引理生成 + 求解器路由）、按优先级落地的代码改动，以及后续实验方案。当前阶段三已经支持两种可配置决策模式：默认的相对/静态路由，以及由 LLM 选择 profile。

相关信号细节：

- Vampire 统计 / 归纳焦点 / unsat core：[vampire_feedback.md](vampire_feedback.md)
- CVC5 stats / difficulty：[cvc5_feedback.md](cvc5_feedback.md)
- 相对进度度量：[relative_metrics.md](relative_metrics.md)

---

## 1. 目前 Feedback-Guided 设计分析

### 1.1 原文算法没有做求解器路由

论文 Algorithm 1 / 2 的闭环是：

```text
ProveRun(P)
  若 SMT 直接证出 → 成功
  对每个 prompt（等式推理 / 项重写）重复最多 3 次:
      LLM 生成猜想 C
      filter: 语法 / 与目标相同 / 与公理矛盾
      verify: A ∧ C → P ?
      若有用: 把 C 作为子目标递归 ProveRun
```

这里会根据**子目标失败**改变控制流（继续下一次 LLM 尝试），但不会根据 solver 反馈改变：

- Vampire schedule / CVC5 量词配置；
- prompt 的优先级；
- 归纳 vs 重写 vs 算术的搜索方向。

论文里 CVC5 始终并行跑 4 个固定配置；Vampire 始终 `--mode portfolio --schedule induction`。

### 1.2 先前已落地的“失败反馈 → 引理生成”

在接入 routing 之前，两边已经有：

| 环节 | Vampire | CVC5 |
|---|---|---|
| 初始诊断 | `show_induction` + 统计 | `--stats` + `get-difficulty` |
| 有用性失败 | 子集证明、progress score、repair hints | 子集证明、stats/difficulty、repair hints |
| 写入 prompt | invalid / useless / progress / hints | 同类，外加 high-difficulty assertions |
| 子目标失败 | 诊断 + `subgoal_failed` hint | 同类 |

问题：

1. 反馈只进入 LLM prompt，不进入 solver 配置。
2. 诊断策略固定（Vampire 结构归纳；CVC5 `--quant-ind --conjecture-gen`）。
3. portfolio 失败时丢掉各策略的独立结果。
4. 子目标超时把父引理记为 `invalid_lemmas`，语义过严。

### 1.3 现在的双层 Feedback-Guided 设计

保留原文证明树，在每个目标节点增加局部搜索状态：

```text
静态理论特征
    +
短 probe（2s）各候选 profile
    +
repair hints / progress signals
        ↓
   GoalSearchState
        ├─ 下一轮 LLM：prompt 重排 + routing 说明
        └─ 下一轮 solver：top-k profile，失败再回退论文 portfolio
```

原则：

- 反馈只影响**搜索顺序与预算分配**，不改变证明成立条件（仍要求 `A ∧ L → P` 且每个 `L` 可递归证明）。
- 不在每个成功子引理后无条件换策略。
- 父目标与子目标允许使用不同 profile；子目标可继承父 profile 作为优先候选。
- 子目标失败记为 `useful_but_unproved`，不记为 invalid。

关闭路由时（`SOLVER_ROUTING=off`）行为回到论文 portfolio。

---

## 2. 实现优先级与落地情况

| 阶段 | 内容 | 状态 |
|---|---|---|
| Phase 1 | 可观测理论 profile；每策略独立结果；SMT 静态分流 | 已实现 |
| Phase 2 | 失败反馈驱动 top-k 路由 + 论文 portfolio 回退 | 已实现 |
| Phase 3 | 联合 prompt/profile 状态；按 attempt 记录结果；relative 或 LLM profile selector；profile 注入引理 prompt | 已实现 |
| Phase 4 | CVC5 ↔ Vampire 跨后端 routing | 未实现，见实验方案 |

---

## 3. 代码改动

### 3.1 新增文件

| 文件 | 作用 |
|---|---|
| `theory_features.py` | 从 SMT-LIB2 抽取 `has_adt` / `has_int` / `mixed_adt_lia` 等 |
| `solver_routing.py` | `GoalSearchState`、profile 推荐、probe utility、prompt 重排与 prompt 文本 |
| `profile_selector.py` | backend-specific LLM selector、JSON 校验、profile/prompt 白名单回退 |
| `prompts_routing/vampire/` | Vampire profile selector 的 system/user prompt |
| `prompts_routing/cvc5/` | CVC5/CVC4 profile selector 的 system/user prompt |
| `tests/test_solver_routing.py` | 分流、hint 重排、utility、prompt 片段 |
| `tests/test_profile_selector.py` | relative/LLM 模式、非法输出、backend prompt 隔离 |

### 3.2 Vampire profiles（`vampire_runner.py`）

本仓库 Vampire 没有独立 `--alasca` 开关。`alasca_arith` 用当前二进制上的 ALASCA 相关选项近似：

```text
--induction both
--theory_instantiation all
--unification_with_abstraction interpreted_only
--arithmetic_subterm_generalizations cautious
```

| profile | 含义 |
|---|---|
| `induction_portfolio` | 论文默认：`--schedule induction` |
| `struct_induction` | `--schedule struct_induction` |
| `struct_induction_tip` | TIP 结构归纳 schedule |
| `integer_induction` | `--schedule integer_induction` |
| `smtcomp` | SMT-COMP 算术/混合理论 schedule |
| `struct_single` / `int_single` | 单策略诊断 |
| `alasca_arith` | ALASCA 风格算术 superposition |

新增：

- `VampireResult.strategy`、`portfolio_results`
- `run_vampire(..., profile=)`
- `run_vampire_probe` / `run_vampire_routed`
- 诊断按 profile 映射到可比较的单策略（portfolio → `struct_single` / `int_single`）

### 3.3 CVC5 profiles（`cvc5_runner.py`）

论文 4 路 portfolio 仍是默认回退：

```text
cvc5_simple
cvc5_inductive
cvc5_inductive_no_ematching
cvc4_default
```

新增：

| profile | 选项要点 |
|---|---|
| `adt_structural` | `--quant-ind --dt-stc-ind` |
| `integer_recursive` | `--quant-ind --int-wf-ind` |
| `controlled_conjecture` | `--conjecture-gen-max-depth=2 --conjecture-gen-per-round=5` |

`run_cvc` 失败时把各策略的 status 写入 `portfolio_results`。`run_cvc_routed` 先跑推荐 profile，再跑未尝试的论文配置，并为 fallback 预留预算。阶段三还修复了 CVC5 runner 的导入和并行结果处理路径的缩进问题，使相对指标测试可以实际导入 CVC5。

### 3.4 静态分流 → 候选 profile

**Vampire**

- 纯 ADT → `struct_induction`, `induction_portfolio`
- 纯 Int → `integer_induction`, `alasca_arith`, `smtcomp`
- ADT+LIA → `induction_portfolio`, `smtcomp`, `alasca_arith`

**CVC5**

- 纯 ADT → `adt_structural`, `cvc5_inductive`
- 纯 Int → `integer_recursive`, `cvc5_inductive`
- 混合 → `cvc5_inductive`, `cvc5_inductive_no_ematching`, `integer_recursive`

hint 再提升：

- `need_arithmetic_lemma` → Vampire `alasca_arith` / CVC5 `integer_recursive`
- `need_rewrite` / `induction_stuck` → 结构归纳或 no-ematching
- `need_stronger_lemma` / `need_induction_lemma` → 归纳 + 一般化 prompt
- `search_explosion` → Vampire 收窄到 `struct_induction`；CVC5 `controlled_conjecture`

### 3.5 Mate 闭环（`Mate_new.py` / `Mate_new_vampire.py`）

1. `ProveRun` 进入节点时 `seed_baseline_repair_hints`：理论分析 + relative 模式下最多 `SOLVER_ROUTING_PROBE_MAX_PROFILES` 个 probe；LLM 模式跳过 probe utility。
2. 初始验证 / 有用性验证 / 重试超时走 `run_*_routed`，并保留 fallback 预算。
3. 诊断 progress score 使用当前 `active_profile` 对应的单策略，保证 baseline/control/candidate 可比。
4. 每个 LLM 生成 attempt 重新选择 prompt/profile；prompt 注入 `SOLVER ROUTING` 段，并按 hint 或 selector 结果选择两种论文 prompt，不删除候选。
5. 子目标失败：`unproved_lemmas` + repair hints，不再写入 `invalid_lemmas`。
6. 子目标 `ProveRun(..., parent_goal_name=)` 可继承父 profile。
7. 有用性验证、子集验证和重试结果写入 `routing.pair_history`，包括 status、elapsed、winner/fallback 信息。

`failed_lemmas.json` 新增字段：

```json
{
  "unproved_lemmas": [
    {"lemma": "(forall ...)", "status": "useful_but_unproved", "blocking_subgoal": "template_1"}
  ],
  "progress_lemmas": [
    {"lemma": "...", "score": 2.1, "signals": ["more_demodulations(+40%)"], "best_profile": "struct_induction"}
  ],
  "routing": {
    "backend": "vampire",
    "active_profile": "struct_induction",
    "candidate_profiles": ["struct_induction", "induction_portfolio"],
    "fallback_profiles": ["induction_portfolio"],
    "routing_reasons": ["static:adt"],
    "prompt_guidance": "...",
    "profile_history": []
  }
}
```

### 3.6 环境变量

见 `.env_template`：

| 变量 | 默认 | 含义 |
|---|---|---|
| `SOLVER_ROUTING` | `on` | 关闭则完全回到论文 portfolio |
| `SOLVER_ROUTING_FALLBACK` | `on` | top-k 失败后跑论文配置 |
| `SOLVER_PROBE_TIMEOUT` | `2` | 每个候选 profile 的 probe 秒数 |
| `SOLVER_ROUTING_TOP_K` | `2` | 正式证明并行的 profile 数 |
| `SOLVER_ROUTING_DECIDER` | `relative` | `relative` 使用反馈/相对分数；`llm` 使用 profile selector |
| `SOLVER_ROUTING_LLM_MIN_CONFIDENCE` | `0.55` | LLM JSON 决策的最低置信度 |
| `SOLVER_ROUTING_PROBES` | `on` | relative 模式是否运行短 probe |
| `SOLVER_ROUTING_PROBE_MAX_PROFILES` | `3` | relative 模式最多观测多少个 profile |
| `SOLVER_ROUTING_FALLBACK_FRACTION` | `0.25` | 为论文 fallback 预留的时间比例 |
| `SOLVER_ROUTING_FALLBACK_MIN_SECONDS` | `5` | fallback 的最小预留秒数 |

`baseline_only` 模式仍调用原始 `run_cvc` / `run_vampire`，便于和论文 Table 1/5 的 solver-only 基线对齐。

### 3.7 阶段三：联合 prompt/profile 选择

现有的 `short probe + top-k` 不是阶段三的最终决策。它仍可作为 `relative` 模式的初始先验，但存在两个限制：不同 Vampire/CVC5 profile 的原始计数不可直接比较，且 probe 只应影响搜索顺序，不能改变证明判定。因此现在每个目标节点都保存：

```json
{
  "active_profile": "struct_induction",
  "active_prompt": "prove_prompt_equational_reasoning",
  "decision_mode": "llm",
  "decision_source": "llm",
  "decision_confidence": 0.84,
  "candidate_profiles": ["struct_induction"],
  "pair_history": [
    {
      "prompt_strategy": "prove_prompt_equational_reasoning",
      "profile": "struct_induction",
      "winner_profile": "",
      "status": "timeout",
      "proved": false,
      "fallback_used": false,
      "decision_source": "llm"
    }
  ]
}
```

`SOLVER_ROUTING_DECIDER=relative` 时：

1. 静态理论特征和 repair hints 产生 profile 先验；
2. 已有 probe/profile history 用于有限候选排序；
3. 当前 hint 决定 prompt 顺序；
4. 每次正式验证把 `(prompt_strategy, profile)` 和结果写入 `pair_history`。

`SOLVER_ROUTING_DECIDER=llm` 时：

1. 跳过 probe utility 对 profile 的排序，避免短 probe 的绝对计数偏差；
2. 使用 `prompts_routing/vampire/` 或 `prompts_routing/cvc5/` 中不同的 selector prompt；
3. selector 会看到理论特征、失败反馈、历史 pair 结果，以及候选 profile 的预期影响；
4. LLM 只能返回候选 profile/prompt ID、置信度和简短理由；
5. 返回值经过 JSON 解析、候选白名单和置信度校验；失败时退回静态理论顺序；
6. 选出的 profile 进入后续引理生成 prompt，形成 prompt/profile 联动；
7. solver 的 `unsat` 仍是唯一证明成功条件，LLM 不参与逻辑有效性判断。

Vampire selector 会区分结构归纳、整数归纳、SMT-COMP schedule 和 ALASCA-inspired 配置；CVC5 selector 会区分 datatype structural induction、integer well-founded induction、E-matching 和 controlled conjecture generation。`alasca_arith` 仍是当前二进制上的近似配置，不应在实验中表述为独立的 Vampire `--alasca` 开关。

正式 routed run 为论文 portfolio 保留明确时间预算：当选中的 profile 不是 fallback 时，默认预留总 timeout 的 25% 且至少 5 秒给 fallback；因此不会再出现 primary profile 消耗完整 timeout 后 fallback 没有预算的情况。

---

## 4. 引理生成 vs 求解器路由：如何配合

同一条 hint 同时影响两边，但语义不同。

| hint | 引理生成 | Vampire 路由 | CVC5 路由 |
|---|---|---|---|
| `induction_stuck` | 针对 focus 项的等式桥 | 保持/提升 `struct_induction` | `adt_structural` |
| `need_rewrite` | 左侧匹配目标子项的重写引理 | 结构归纳 + 重写活跃的 schedule | `cvc5_inductive_no_ematching` |
| `need_induction_lemma` / `need_stronger_lemma` | 优先 `term_rewrite` 一般化 | `induction_portfolio` | `cvc5_inductive` |
| `need_arithmetic_lemma` | 递推/单调性/界 | `alasca_arith`, `integer_induction` | `integer_recursive` |
| `search_explosion` | 更小、更局部的桥 | 收窄 schedule | `controlled_conjecture` |
| `high_difficulty_assertions` | 连接高难度公理与目标 | （Vampire 无 difficulty） | `adt_structural` |
| `useful_but_unproved` | 弱化该引理或补桥，而不是丢掉 | 子节点可单独再路由 | 同左 |

路由触发点（不是“每个子引理成功后切换”）：

1. 节点首次访问（relative 为静态 + probe，llm 为静态候选 + selector）；
2. 有用性检查失败（hints 更新，下一轮 LLM + 可沿用当前 top-k）；
3. 子目标失败（父节点得到 `subgoal_failed`，子节点自己的 routing 独立保存）。

---

## 5. 实验设计

目标：在**不破坏原文证明语义**的前提下，量化 Phase 1–3 对 Vampire / CVC5 路径的贡献，并诊断 routing 是否把预算用在正确的理论上。

### 5.1 不变的实验约束

与论文 §4 对齐：

- 基准：StandardDT (`vmcai15-dt`)、StandardDTLIA (`dtt`)、AutoProofBM (`autoproof`)、IndBen (`ind-ben`)，共 706 题。
- 墙钟 `TASK_TIMEOUT=1200`；初始/有用性检查 60s；filter 1s；最大深度 3；每 prompt 最多 3 次。
- 默认 LLM 与论文主实验一致（记录 `MODEL_TYPE` 与温度）。
- 每种配置跑 3 次，报告均值、range、std（对应论文 Table 3/4）。

### 5.2 配置矩阵

| ID | 名称 | 设置 |
|---|---|---|
| B0 | solver-only | `baseline_only=True`（论文 cvc5/Vampire 基线） |
| P0 | PaperMate | `SOLVER_ROUTING=off`，仅保留原 query-filter-validate |
| F1 | Feedback lemmas | routing off，但保留 repair hints / progress score（当前反馈引理生成） |
| R1 | Routed | `SOLVER_ROUTING=on`，`FALLBACK=on`（**主推荐配置**） |
| R2 | Routed no-fallback | `FALLBACK=off`，只跑 top-k，测量路由是否过窄 |
| R3 | Static-only | `SOLVER_ROUTING_PROBES=off`，只用静态理论/hint 顺序，不运行短 probe |
| R4 | LLM selector | `SOLVER_ROUTING_DECIDER=llm`，Vampire/CVC5 使用各自 selector prompt |

建议主对比：

```text
B0 vs P0     论文贡献（已有）
P0 vs F1     失败反馈对引理生成的贡献
F1 vs R1     在反馈引理生成之上，routing 的额外贡献
R1 vs R2     fallback 是否必要（保护论文已能解的题）
R1 vs R4     相对路由与 LLM profile 决策的效果/开销
```

Vampire 与 CVC5 **分开**报，不要混成一个数字。论文 Table 5 已表明 Vampire 在 AutoProofBM / DTLIA 上弱于 CVC5。

### 5.3 分数据集假设

| 数据集 | 预期 routing 行为 | 成功判据 |
|---|---|---|
| StandardDT / IndBen | 多数 `struct_induction` / `adt_structural` | R1 ≥ F1，且不显著慢于 P0 |
| StandardDTLIA | Vampire 更常选 `alasca_arith`/`smtcomp`；CVC5 `integer_recursive` 或 `no_ematching` | Vampire R1 相对 Table 5 的 80/168 应有提升 |
| AutoProofBM | CVC5 为主；Vampire 仍受 SMT-LIB tester 限制 | 主要看 CVC5 R1；Vampire 报 parse/error 率 |

### 5.4 必报指标

**任务级**

- 1200s / 360s 内求解数（对齐 Table 1）
- 已解题平均墙钟、中位数
- token 消耗（input/output）

**路由级（新）**

- 每个 profile 作为 `active_profile` 的次数、作为 winner 的次数
- probe 选出的第一名 vs 最终证出用的 profile（是否一致）
- fallback 触发率：top-k 失败后由论文 portfolio 救回的题数（R1 相对 R2）
- `portfolio_results` 中 timeout / error / unsat 分布

**反馈级**

- repair hint 种类直方图（`need_rewrite`, `need_arithmetic_lemma`, …）
- progress lemma 被后续轮次“沿用/强化”的比例
- `useful_but_unproved` 相对旧 `invalid` 误杀的减少（可用抽样人工看 20 题）

**开销**

- probe 墙钟占整题时间的比例（预期每节点 ≤ 6s）
- 因 probe 导致 1200s 边界失败的题（应接近 0；若高则把 probe 降为 1s 或只在 depth=0 做）

### 5.5 日志与结果文件

每题目录的 `failed_lemmas.json` 已含 `routing`。批量实验 CSV 建议额外列：

```text
active_profile, candidate_profiles, winner_profile, fallback_used,
hint_kinds, progress_lemma_count, unproved_count, probe_seconds
```

实现方式：在 `run_exp_folder*.py` 读每个 folder 的 `failed_lemmas.json` 的 `routing` 字段汇总（可第二阶段加，不阻塞当前 runner）。

### 5.6 消融与对照实验细节

1. **Prompt 重排消融**：R1 但 `order_prompt_strategies` 固定为论文顺序。
2. **诊断 profile 消融**：progress score 始终用论文默认诊断，不跟 `active_profile`。
3. **子目标 invalid 误杀消融**：对比把 `unproved_lemmas` 改回 `invalid_lemmas` 的旧行为。
4. **跨后端（Phase 4，可选）**：仅对 `mixed_adt_lia` 且 Vampire R1 失败的题，把同一引理集交给 CVC5 routed。这是新实验，不进入与论文 Table 1 的直接对比。
5. **决策器消融**：固定总预算，对比 `SOLVER_ROUTING_DECIDER=relative` 与 `SOLVER_ROUTING_DECIDER=llm`；LLM 模式应报告 selector token/调用开销及静态回退率。

### 5.7 运行命令草案

```bash
# 论文行为（对照）
SOLVER_ROUTING=off python3 run_exp_folder.py --strategy_mode default ...
SOLVER_ROUTING=off python3 run_exp_folder_vampire.py --strategy_mode default ...

# 主配置
SOLVER_ROUTING=on SOLVER_ROUTING_FALLBACK=on \
  python3 run_exp_folder.py --strategy_mode default ...

SOLVER_ROUTING=on SOLVER_ROUTING_FALLBACK=on \
  python3 run_exp_folder_vampire.py --strategy_mode default ...

# LLM profile selector
SOLVER_ROUTING=on SOLVER_ROUTING_DECIDER=llm SOLVER_ROUTING_FALLBACK=on \
  python3 run_exp_folder.py --strategy_mode default ...

SOLVER_ROUTING=on SOLVER_ROUTING_DECIDER=llm SOLVER_ROUTING_FALLBACK=on \
  python3 run_exp_folder_vampire.py --strategy_mode default ...

# 无回退
SOLVER_ROUTING=on SOLVER_ROUTING_FALLBACK=off \
  python3 run_exp_folder_vampire.py --strategy_mode default ...
```

先在 IndBen 的 `nat/` 子集（含 `crafted_mul_comm`）做 1 小时冒烟，确认：

- `failed_lemmas.json` 出现 `routing.active_profile`
- ADT 题多为 `struct_induction` / `adt_structural`
- `SOLVER_ROUTING=off` 仍能解原先能解的简单题

再上 706 全量。

### 5.8 风险

- **预算被 probe 吃掉**：depth=3 的证明树可能多次 probe。若 360s 曲线变差，只在 `depth==0` 做 probe，子节点只继承父 profile。
- **profile 统计不可比**：不同 schedule 的 `Generated clauses` 量级不同。utility 只用于排序，证明仍靠 unsat；progress score 仍在**同一诊断策略**上比。
- **ALASCA 近似依赖 Z3**：`theory_instantiation` 失败则该 profile utility 为负，自动降权。
- **AutoProofBM + Vampire**：tester 重写已存在；routing 不能修复 Vampire 不支持的 SMT-LIB 构造。

---

## 6. 本地检查

```bash
python3 tests/test_relative_metrics.py
python3 tests/test_solver_routing.py
```

在 `crafted_mul_comm` 上，2s probe 观察到：

- Vampire：`struct_induction` 与 `induction_portfolio` 均有归纳/解调活动；
- CVC5：`adt_structural` 与 `cvc5_inductive` 均有 skolem / datatype / instantiation 信号。

阶段三额外检查：

```bash
python3 tests/test_profile_selector.py
SOLVER_ROUTING_DECIDER=llm python3 tests/test_profile_selector.py
```

真实实验时还应从每题 `failed_lemmas.json.routing.pair_history` 汇总：
`decision_source`、`decision_confidence`、`winner_profile`、`fallback_used`、selector token 和 selector 失败原因。
