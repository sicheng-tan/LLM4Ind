# M2 default vs FULL llmhint-v2：失败题与诊断闭环分析

口径：skip-20，N=686，`result=unsat` 计证出。  
- **M2 default**：`ours_full706_deepseekv4flash_cvc5_module2_nothink`（591）  
  `LEMMA_LIBRARY` + `ANCESTOR` + `OBLIGATION_TREE`；`FEEDBACK_REPAIR_HINTS=off`；`FEEDBACK_LLM_HINTS=off`。  
- **FULL v2**：`ours_full706_deepseekv4flash_cvc5_full_default_hd_llmhint_v2_noadv_p40_nothink`（585）  
  同上模块二，外加 `FEEDBACK_REPAIR_HINTS=on`、`FEEDBACK_LLM_HINTS=on`、`PROMPT_ADVICE=off`。  
生成端 `temperature=0.9`。策略均为 `--strategy-mode=default`（`prompts_ours`）。

本文回答三件事：

1. 两边失败题在**预期证明思路 / 所需引理 / 实际生成轨迹**上差在哪。  
2. 若 **unproved 池正常维护**，政策化的 LLM hint（三模式诊断）能不能把缺口补上。  
3. 诊断提示词若加例子，应如何从缺失引理**提炼共性**（避免点名基准引理），以及基于当前体系该改什么。

---

## 1. 结论先行

| 问题 | 判断 |
|---|---|
| v2 比 M2 少 6 题，是 hint 写错吗？ | **否。** v2 全量诊断成功调用 **0 次**，生成 prompt 0 处 `SOLVER HINTS`。 |
| 那 −6 全是随机性？ | **不完全是。** 对换（13 vs 7）里有 0.9 抽样；但 v2 仍采集 HD、skip 后禁止程序 HD 回退，失败集里 timeout 偏多。 |
| 修好 unproved 写入后，hint 能救 M2 独有的那几题吗？ | **能救一类，不能当银弹。** 最匹配的是「证出但不够 → 需要换形状」的 NEW_DIRECTION（`goal4` / `amortize-queue-goal6`）。对 autoproof 排序/正则/三元乘法这类双方都失败的题，hint 最多换方向，过不了 60s 有用性墙。 |
| 诊断提示词加形状例子？ | **可以，但只能放编码层共性，不能点名基准引理。** 从失败题里提炼的是「ADT–算术接口 / 缺侧幺元 / 双谓词序桥」三类缺口，不是某条 `len>=0` 或 rotate 名引理。主修复仍是 **unproved 写入 + skip/NO_ACTION 时 HD 回退**；不修门控则例子 0 次调用。 |
| 88 道双边失败怎么办？ | 主体不是缺 hint。autoproof 65/88：排序等价、正则、`mul3` 交换结合，典型是 usefulness 60s timeout 或证明链太长。hint 不是第一刀。 |

---

## 2. 分数与集合

| 集合 | 题数 | 含义 |
|---|---:|---|
| 双方都证出 | 578 | 主路径一致 |
| **双方都失败** | **88** | 当前体系的硬核失败 |
| 仅 M2 证出 / v2 失败 | 13 | 本文重点：hint 本该发挥作用的对照 |
| 仅 v2 证出 / M2 失败 | 7 | 对换；含 `len>=0` 帮 v2 翻盘的 `amortize-queue-goal7` |

direct 几乎相同（M2 288 / v2 289）。差距在 LLM 路径。

v2 诊断门控全量统计（per-task 日志）：

| 事件 | 次数 |
|---|---:|
| `llm_feedback_hints` 成功 | **0** |
| skip | 2475 |
| └ `need_useless_group` | 1372（第一轮，设计如此） |
| └ `no_opportunity` | 1103（**全部 `n_unproved=0`**） |
| `no_opportunity` 且 `library_new=true` | 467（库已经变了，仍因空池跳过） |
| `failed_lemmas.json` 中 unproved 非空 | **0 / 686** |
| `n_prompt_with_hints` | **0 / 2550** |

对照 v1（旧门控 `no_difficulty`）：诊断成功 1062 次、239 题注入过 hints。  
所以 v2 不是「诊断效果差」，是 **诊断没接通**。

根因与代码对齐：`UNPROVED_NOT_INVALID=on` 时 `_record_blocking_lemma` 直接 `return`；CVC5 生产路径 **从不调用** `add_unproved_lemma`。复活池只读 `unproved_lemmas`，机会门「unproved ∧ 库增量」左边恒假。与此同时 `FEEDBACK_LLM_HINTS=on` 禁止把程序 HD/repair 回退进生成 prompt。生成端比 noadv **更盲**，还继续付 usefulness HD dump 的时间。

---

## 3. 失败分桶

### 3.1 仅 v2 失败（M2 证出）13 题

按「修好 hint 闭环后是否对症」分：

**A. 显然前提 / 换形状（hint 高相关）**

| 题 | 目标（压缩） | 预期关键引理 | M2 实际 | v2 实际 |
|---|---|---|---|---|
| `dtt-clam/goal4` | `len(append x x) = double(len x)` | `len(append)=+` **且** `(>= (len x) 0)` | 第 1 次 `len-append`（usefulness timeout）→ 第 2 次提出 `len>=0`，0.06s 证出父目标（2 LLM / 156s） | 同样先 `len-append`；之后改去证 `double n = n+n`；7 LLM 耗尽。库里只有 `len-append` |
| `dtt-leon/amortize-queue-goal6` | `qlen(enqueue q n) = 1 + qlen q` | `len(append)`、`len(qreva)`、`len>=0`、`plus` 后继 | 4 LLM，库 4 条，含 `len>=0`（pin） | 6 次 useless 耗尽；库只剩 `plus` 与一条 `qlen(enqueue)` 改写 |
| `dtt-clam/goal21` | `rotate(len x)(append x y) = append y x` | `append` 结合/右幺、`len>=0`、rotate 与 append 交换 | 多次把 `len>=0` 做成子目标，22 LLM / 15 条库，1004s 证出 | 从未提出 `len>=0`；append 结合律上打转，1200s。noadv/v1 都证出 |
| `dtt-isa/goal85` | `zip(append xs ys, zs) = zappend(zip xs (take (len xs) zs), zip ys (drop (len xs) zs))` | `zappend` 构造子展开；`take`/`drop` 与 `len` 的整数非负 | 第 1 次 zappend 子句 timeout → 第 2 次过有用性（2 LLM） | zip/drop/take 展开 18 LLM；无 `len>=0` 子目标 |

这四题的共同形态：**已经有一条证出但不够的恒等式，需要换形状（非负、rotate 交换、zip 与 take 的衔接），而不是把同一 C 再 refine。** 这正是 `NEW_DIRECTION` 的设计意图。v2 因为池空从未进入诊断，LAST ATTEMPT 只展示 kept lemma → 模型继续 refine 同一形状。

**B. 构造子 / 序事实（hint 中等相关）**

| 题 | 目标 | M2 关键库 | v2 |
|---|---|---|---|
| `nat_pow_times` | `pow x (plus y z) = mult (pow x y) (pow x z)` | `plus n Z = n`、plus 交换结合、mult 结合 | 13 LLM 耗尽；无 plus-zero。HD 时间税 + 抽样 |
| `isa/goal50` | `butlast xs = take (minus (len xs) (succ 0)) xs` | 一条 `take (len y) (cons x y)` 分情况 | v2 库只剩 `minus (succ n) (succ 0) = n`，6 次失败 |
| `isa/goal80`、`nosg/goal14` | `sorted (sort l)` | `insort ≠ nil`、`less→leq`、insort 保序 | v2 timeout；缺 `cons-not-nil` 类引理，子树膨胀 |
| `nosg/rotate-goal9` | `rotate (len x) x = x` | `append-nil`、`rotate(len x)(append x w)=append w x` | v2 堆了 10 条 append 引理，没收敛到 rotate 恒等式；1200s。noadv 第 1 次 LLM 就过 |

**C. 结构搜索 / 时间税（hint 弱相关，或单条 hint 不够）**

| 题 | 说明 |
|---|---|
| `weird_nat_mul3acc_comm23` | noadv/v1/v2 全失败，仅 M2 证出。需要 `add3acc` 交换族。开 HD 的 default 都没过，不是空池独有 |
| `heap-goal8` | 目标 `hsize(hinsert x n)=1+hsize x`（leftist）。v2 **已经有** `hsize>=0`，仍 timeout。M2 还补了 `plus(hsize,hsize)>=0` 等闭包 |
| `bsearch-tree-goal5` | M2 3 LLM：`less` 反自反/传递、`leq` 传递。v2 有传递但掺进 `tsize(tremove)`，1200s |
| `nosg/goal33` | `fac x = qfac x (succ 0)`。两边库都有 `mult n 0 = 0`、`plus` 交换；v2 超时，差在证明链长度而非缺一条 ge0 |

### 3.2 仅 M2 失败（v2 证出）7 题

对换，说明同一套模块二 + 0.9 会左右摇摆。其中 `dtt-leon/amortize-queue-goal7` 的 v2 库含 `(>= (len l) 0)`——与 goal4 同一枚硬币：抽到非负就过。其余多为 M2 timeout、v2 更短路径（`tsort_sort`、`bsearch-tree-goal2`、`crafted_even/2`）。

### 3.3 双方都失败 88 题

按数据集：autoproof **65**、dtt 8、ind-ben 7、vmcai 8。  
退出：双方 `attempts_exhausted` 41；双方 timeout 20；交叉 27。  
两边失败题平均约 14–15 次 LLM、6–8 组 useless、库约 4 条——不是「没调用 LLM」，是 **调用了但过不了有用性或证不完子目标**。

簇：

| 簇 | 代表 | 预期思路 | 日志里常见情况 | 修好 hint 的期望 |
|---|---|---|---|---|
| 排序等价 / 计数 | `sort_*IsSort`、`*Count` | 插入/归并/快排与 isort 的标准桥（count 保持、相对序） | 常 6 次 LLM 就耗尽；或一边 40+ 次仍 timeout。早期分析里同类题连「猜对的 C」也在 60s 有用性被扔掉 | **低。** 缺的是有用性超时处理 / 更强 solver profile，不是一句 NEW_DIRECTION |
| 正则代数 | `regexp_PlusAssociative` 等 | 语言等价的代数引理；易把语法 `plus` 当成语义结合律（invalid） | 长搜索或 invalid | 低；hint 可能减少明显假引理，但过不了核心 |
| `mul3` / `mul3acc` / `weird_nat_op` | `weird_nat_mul3_*` | `add3`/`mul3` 交换结合族，证明很深 | 大量 timeout | 低–中：revive 有用若能保住「证到一半的 add3 交换」 |
| 二进制数 | `bin_plus*`、`bin_times*` | `s`/`plus`/`times` 在 `Bin` 上的交换结合 | 有用性 timeout 为主 | 低 |
| dtt heap / BST 尺寸 | `heap-goal9/10/12/13`、`bsearch-tree-goal3` | SMT **注释里就有** `len>=0`、`hsize>=0`、`tsize>=0`；目标是 `hsize(hinsert-all)=plus(hsize,len)` 等 | 两边都很少把 ge0 做成子目标（或做成了仍不够） | **中：播种 ge0 比等诊断举例更稳**；hint 是第二刀 |
| rotate / 生成加法 | `crafted_rotate/*`、`generated_add_24sym/0` | rotate 融合、加法交换 | 短 attempt 耗尽 | 中：NEW_DIRECTION 可能换形状 |

双边失败的主因与旧文档 `docs/cvc5_full706_failure_case_analysis.md` 一致：**有用性 60s timeout 把整组 C 扔掉，从未变成子目标。** LLM hint 改的是「下一轮生成什么」，改不了「这一组 C 是否在 60s 内让 `A∧C⊢G` 返回 unsat」。

---

## 4. 案例：`goal4`（hint 最对症的模板）

**目标：** `(forall ((x Lst)) (= (len (append x x)) (double (len x))))`  
公理已有 `len nil = 0`、`len (cons x y) = 1 + len y`、`double` 在 `>= n 0` 下等于 `* 2 n`。整数算术需要 **`len` 非负**，否则 `double(len x)` 的定义域对不上。

**预期链：**

1. `len(append x y) = len x + len y`（归纳，易证）  
2. `(>= (len x) 0)`（对 `len` 的构造子归纳，易证）  
3. 代入 `y=x` 得 `len(append x x) = 2·len x = double(len x)`

**M2 日志：**

- LLM-1：提出 `len-append`；usefulness **timeout**（单独不够）；harvest 把该引理收入库（local）。  
- LLM-2：提出 `len>=0`；usefulness **0.06s unsat**（库里已有 `len-append`）。  
- 子目标 `template_1` 的 goal 就是 `len>=0`，随后 pin 入库。

**v2 日志：**

- 同样先 `len-append`，usefulness 变成 `unknown`（HD dump 改变了 usefulness 跑法/状态）。  
- 之后子目标改成 `double n = n+n`，与原目标的整数侧擦边但缺非负。  
- 诊断：`need_useless_group` / `no_opportunity n_unproved=0`。LAST ATTEMPT 只有 kept 的 `len-append`，无 repair、无 SOLVER HINTS。

若 unproved 维护正常：第一轮 `len-append` 若被标成「证出但对父目标无用」，严格说它 **不是 unproved**（已证）。诊断的正确模式是 **NEW_DIRECTION**（「别再 refine length-of-append，改证测度非负 / 与 double 的衔接」），而不是 REVISE_CANDIDATE 把 `len-append` 再塞回去。  
因此：只把「有用但子目标失败」写入 unproved **还不够**覆盖 goal4；还需要 **useless-but-proved 组也能触发 NEW_DIRECTION**（不依赖复活池非空）。这与当前 `has_hint_opportunity` 要求 revival 池非空是冲突的。

---

## 5. 政策化 LLM hint 修好之后，能改善什么

三模式的设计意图：

| 模式 | 何时用 | 对失败集 |
|---|---|---|
| `NO_ACTION` | 生成已在正确形状上 | 避免乱steer |
| `NEW_DIRECTION` | 复活池里没有该用的形状；或只有证出但不够的 C | **A 类题的主路径** |
| `REVISE_CANDIDATE` | 子目标失败留下的未证公式，库变了之后值得再引用 | 双边失败里「证到一半」的 `add3`/`merge` 链；**当前池恒空，此模式从未发生** |

**修好 unproved 写入（`add_unproved_lemma` 接到 blocking 子目标）之后：**

- REVISE 开始有输入：子目标 timeout/attempts 的公式进入复活池。对 `heap-goal8`、`goal80`、`mul3` 这种「有局部真引理、父目标仍失败」可能有用。  
- **仍救不了 goal4 这一型**，除非门控改为：useless group 之后即使 `n_unproved=0` 也允许 NEW_DIRECTION（只看 LAST CANDIDATE + 库增量）。  
- 若不加 HD 回退：诊断 `NO_ACTION` / skip 时生成端仍然全盲，noadv 那种「HD 指向 rotate / cons」的快赢（goal21）回不来。

**预估（单次 seed，量级而非承诺）：**

| 改动 | 更可能动到的题 | 对 585/591 的粗预期 |
|---|---|---|
| 仅写入 unproved，门控不变 | 几乎仍 0 次 NEW_DIRECTION（A 类不进池） | ~0 |
| 写入 unproved **或** useless 后允许 NEW_DIRECTION | A 类 3–4 题、部分 B | 有机会抹平甚至超过 M2 的 −6 |
| 再加 skip/NO_ACTION → HD 回退 | 接近 noadv 的快赢（goal21） | 减少「比 M2 更盲」 |
| 句法播种 `len/hsize/tsize>=0` | A 类 + 部分 heap/BST 双边失败 | 比等 LLM 举例子更稳 |
| 只改诊断提示词加例子、不修门控 | **0**（诊断仍不调用） | 0 |

v1 的教训：hint **真注入**时也不稳（长自然语言 stuck-point、个别题 noadv 更快）。修好闭环后仍要限制 note 长度、禁止 REVISE 编造池外公式；NEW_DIRECTION 只描述**形状类**，示意公式用元变量。

---

## 6. NEW_DIRECTION 例子：从缺失引理抽共性，不点名基准

### 6.1 为什么不能把失败题的「标准引理」写进提示词

§3 的案例分析需要点名公式（否则无法对照日志）。**诊断提示词不能照搬那些公式。**  
`rotate(len x)(append x w)=append w x`、`insort ≠ nil`、`sorted(insort)`、`take(len xs)(append xs ys)=xs` 都是 TIP/IsaPlanner 族上的名引理；写进政策等于对着结果调 prompt，审稿人有理由怀疑过拟合。

提示词只放能从 **ADT + 递归定义 + 目标逻辑** 推出来的缺口类型。论文叙事应是「编码层启发式」，不是 lemma 词典。

### 6.2 失败日志里反复出现的共同特点（分析层）

把 §3.1 A/B 与部分双边失败的「M2 有、v2 没有 / 双方都缺」收成三条**编码缺口**，不绑定函数名：

| 共性 | 日志里长什么样 | 编码原因（可公开辩护） |
|---|---|---|
| **测度编进无约束算术后，缺定义域引理** | LAST 已是「对 combine 的同态」（计数在拼接上可加），父目标仍 timeout；或目标把计数送进 `+` / 仅在 `n≥0` 才展开的函数 | SMT 把 ADT 计数编成 `Int`，构造子归纳的非负**不是**背景公理 |
| **公理只写了构造子展开的那一侧幺元** | LAST 全是结合律/交换律；缺的是「第二个参数是单位」或对称的右幺 | 结构归纳公理习惯写 `f(e,x)=x`；另一侧要另证，形状不同于再来一条 assoc |
| **同一数学关系被编成两个谓词，缺桥** | 文件里同时有严格序与非严格序（或 `head` 需要「结果非空」），生成却只 refine 其中一侧 | 双谓词是编码选择；桥引理是接口，不是某算法的正确性陈述 |

这三类覆盖了「证出但不够 → 该换形状」的主模式（§4：同态已在库中，缺的是测度进入算术的前提；以及幺元/序桥相对「再堆 assoc」）。  
**覆盖不到的：** 排序算法互等、正则代数、三元乘法深交换——那是有用性 60s / 证明深度，不应靠提示词举例。

同态本身（`m(combine x y) = m(x)+m(y)`）是生成器从递归定义能写的形状，**不要单独做成第四条点名例子**。诊断里一句政策即可：LAST 已是同态且 GOAL 仍用该测度做算术 → 转定义域引理，不要再加强同一条同态。

### 6.3 建议写入诊断 system 的示意（示意用元变量）

当前 NEW_DIRECTION 只说 *explain a different lemma shape*，没有形状类，模型容易写长散文或乱换算术改写（§4 中把同态换成「与乘法定义等价的算术恒等式」即此类偏移）。

放进提示词的应是下面这档（可整段粘贴）。**不要**在此块出现具体基准函数名或题号。

```text
NEW_DIRECTION: describe a different lemma SHAPE from the encoding,
not a named benchmark identity. Pick at most one family; adapt
symbols to this SMT. If LAST or the library already has that shape,
pick another family or NO_ACTION.

1) Measure-into-arithmetic.
   If m is defined by recursion on constructors and returns Int/Real
   (base ~ 0, step ~ 1 + m(tail) or plus of child measures), a typical
   missing lemma is the domain fact
     (forall ((x T)) (>= (m x) 0))
   If LAST is already a homomorphism for m over a combiner and GOAL
   still feeds m into arithmetic, prefer this domain fact — do not
   strengthen the same homomorphism.

2) Missing unit of a recursive binary operator.
   Axioms often give the constructor-side unit (f(e, y) = y). The
   other side is a different shape, not more associativity:
     (forall ((x T)) (= (f x e) x))

3) Bridging two encodings of the same order — only if BOTH
   comparison symbols occur in the file:
     (=> (not (R a b)) (Q b a))
   Transitivity of an encoded order is the same class.
   Skip if the file has only one comparison symbol.

Quote at most one adapted formula in the note (shape example, not an axiom).
Do not suggest algorithm equivalences, language-algebra identities,
or other named benchmark lemmas from this menu.
```

REVISE 仍禁止用此菜单发明池外公式。NEW_DIRECTION 允许 0–1 条改写后的示意公式，标明 example。

### 6.4 和句法播种的分工

定义域事实（`m` 递归到 `Int` 且基例为 0）用解析器提出，比 prompt 举例更干净，也更不怕被说成对着 list 题调参。  
提示词三类负责播种规则不好写的情况：缺侧幺元、双序桥、以及「LAST 已是同态 → 转定义域」的**转向政策**。  
单独改提示词、不修门控：v2 已证明调用次数为 0，无效。

---

## 7. 基于当前体系的优化（按优先级）

### P0 — 让诊断名实相符

1. **写入 unproved：** `_record_blocking_lemma` 在 `UNPROVED_NOT_INVALID=on` 时调用 `add_unproved_lemma`，而不是 `return`。子目标失败的公式进入复活池。  
2. **放宽机会门：** `has_hint_opportunity` 在「≥1 useless group」时，若池空但 LAST CANDIDATE 为证出-无用，仍允许跑诊断，且默认倾向 NEW_DIRECTION。否则 goal4 永远进不了 hint。  
3. **Fallback：** skip / `NO_ACTION` 时允许程序 HD/repair 回到生成 prompt（回到 noadv 的可见性）。现在「flag 开则永不回退」对全量是净负。  
4. **采集与注入分离：** `FEEDBACK_REPAIR_HINTS` 继续给诊断观察包；生成端是否展示程序块由 fallback 决定。讨论是否对无注入的 HD dump 减负（60s 税）。

### P1 — 便宜、确定性的前提

5. **测度定义域播种（优先于 prompt 点名）：** 检测「递归到 `Int`、基例为 0、步长为 1 或 child-measure 之和」的函数，自动提出 `(forall ((x T)) (>= (m x) 0))`。按定义形状触发，不按函数名白名单。  
6. **可选同构规则：** 二元递归算子若公理只有一侧幺元，提出另一侧——同样按定义形状，不写死具体函数。

### P2 — 提示词与生成契约

7. NEW_DIRECTION 只加 §6.3 的三类编码示意（元变量），禁止把案例分析中的名引理写进政策。限制 note 长度。  
8. LAST ATTEMPT 在无 SOLVER HINTS 时保留「kept 已在库中，请换形状」；换形状的含义指向 §6.2，而不是再 refine 同一公式。

### P3 — 双边 88 题（hint 不是主攻）

9. 有用性 timeout：progress sidecar / 更短 HD dump / 对已证 C 做 harvest-retry（M2 的 timeout 收获路径）。这是旧失败分析的主因。  
10. 不要用「再叠一个关 HD 诊断的开关」代替 P0；要关用已有总闸 `FEEDBACK_LLM_HINTS=off`。

### 实验建议

- 在 n_unproved 恒 0 的配置上 **不要解读 LLM hint 效果**；先 P0 再开 hint 全量。  
- 对照：M2（现状） vs M2+播种 ge0 vs FULL（P0+fallback，hint 开）。  
- 形状菜单应在原则（§6.2）上定稿，用 held-out 或有/无菜单消融报告，避免「先看失败再写例子」。  
- A 类短证明做小集多 seed，分清随机与机制。

---

## 8. 附录：88 道双边失败清单

格式：`dataset/task`，M2 退出，v2 退出，两边 LLM 次数。

```
autoproof/standard/bin_distrib                    att/att    14/6
autoproof/standard/bin_plus                       att/att    6/6
autoproof/standard/bin_plus_assoc                 to/att     6/6
autoproof/standard/bin_plus_comm                  to/att     18/18
autoproof/standard/bin_times                      to/att     21/6
autoproof/standard/bin_times_assoc                att/to     6/12
autoproof/standard/bin_times_comm                 to/to      26/34
autoproof/standard/int_left_distrib               att/att    6/6
autoproof/standard/list_Select                    att/att    6/6
autoproof/standard/list_return_2                  att/att    6/6
autoproof/standard/nicomachus_theorem             att/att    6/6
autoproof/standard/regexp_Deeps                   to/att     25/14
autoproof/standard/regexp_PlusAssociative         to/att     63/13
autoproof/standard/regexp_PlusCommutative         att/att    11/12
autoproof/standard/regexp_PlusIdempotent          att/att    9/7
autoproof/standard/regexp_RecPlus                 att/att    6/14
autoproof/standard/regexp_RecSeq                  att/to     9/16
autoproof/standard/regexp_RecStar                 to/to      14/14
autoproof/standard/regexp_Reverse                 to/to      10/15
autoproof/standard/regexp_SeqAssociative          att/att    6/7
autoproof/standard/regexp_SeqDistrPlus            att/att    6/12
autoproof/standard/regexp_Star                    to/to      15/17
autoproof/standard/relaxedprefix_correct          to/to      10/13
autoproof/standard/rotate_mod                     att/to     6/34
autoproof/standard/rotate_snoc                    to/att     11/5
autoproof/standard/rotate_structural_mod          to/att     19/6
autoproof/standard/sort_BubSortCount              to/att     24/6
autoproof/standard/sort_BubSortIsSort             att/to     6/38
autoproof/standard/sort_HSortCount                att/att    21/6
autoproof/standard/sort_HSortIsSort               att/att    6/6
autoproof/standard/sort_MSortBU2Count             att/att    26/18
autoproof/standard/sort_MSortBU2IsSort            to/to      20/12
autoproof/standard/sort_MSortBUCount              att/att    6/6
autoproof/standard/sort_MSortBUIsSort             att/att    6/6
autoproof/standard/sort_MSortTDCount              att/att    6/6
autoproof/standard/sort_MSortTDIsSort             att/att    6/6
autoproof/standard/sort_NMSortTDCount             att/att    6/6
autoproof/standard/sort_NMSortTDIsSort            att/att    11/12
autoproof/standard/sort_QSortCount                att/to     6/41
autoproof/standard/sort_QSortIsSort               to/att     43/6
autoproof/standard/sort_SSortCount                att/to     6/27
autoproof/standard/sort_SSortIsSort               to/to      14/21
autoproof/standard/sort_TSortCount                att/att    6/6
autoproof/standard/sort_TSortIsSort               att/att    6/6
autoproof/standard/tree_Flatten1List              att/att    6/6
autoproof/standard/tree_Flatten3                  to/to      12/21
autoproof/standard/weird_nat_mul3_assoc1          to/att     31/18
autoproof/standard/weird_nat_mul3_assoc2          to/att     21/9
autoproof/standard/weird_nat_mul3_assoc3          att/to     29/22
autoproof/standard/weird_nat_mul3_comm12          to/to      28/36
autoproof/standard/weird_nat_mul3_comm13          to/to      55/40
autoproof/standard/weird_nat_mul3_comm23          att/att    6/6
autoproof/standard/weird_nat_mul3_rot             att/att    19/6
autoproof/standard/weird_nat_mul3_rrot            to/att     30/20
autoproof/standard/weird_nat_mul3_same            to/att     12/6
autoproof/standard/weird_nat_mul3acc_assoc1       att/att    13/12
autoproof/standard/weird_nat_mul3acc_assoc2       att/att    6/6
autoproof/standard/weird_nat_mul3acc_assoc3       to/att     20/6
autoproof/standard/weird_nat_mul3acc_comm12       att/att    6/16
autoproof/standard/weird_nat_mul3acc_comm13       to/to      37/20
autoproof/standard/weird_nat_mul3acc_rot          att/att    16/30
autoproof/standard/weird_nat_mul3acc_rrot         att/att    12/11
autoproof/standard/weird_nat_op_assoc             to/to      7/22
autoproof/standard/weird_nat_op_assoc2            att/att    5/21
autoproof/standard/weird_nat_op_comm_comm         att/att    23/11
dtt/dtt-isa/goal19                                att/att    6/6
dtt/dtt-isa/goal64                                att/att    6/12
dtt/dtt-isa/goal87                                to/att     29/26
dtt/dtt-leon/bsearch-tree-goal3                   att/att    6/17
dtt/dtt-leon/heap-goal10                          to/att     23/6
dtt/dtt-leon/heap-goal12                          to/to      24/22
dtt/dtt-leon/heap-goal13                          att/to     6/31
dtt/dtt-leon/heap-goal9                           to/to      22/34
ind-ben/crafted_assorted/18                       att/att    11/6
ind-ben/crafted_rotate/0                          att/att    6/6
ind-ben/crafted_rotate/1                          to/to      17/14
ind-ben/crafted_rotate/4                          to/to      16/18
ind-ben/crafted_rotate/5                          att/att    6/6
ind-ben/crafted_rotate/8                          att/to     27/13
ind-ben/generated_add_24sym/0                     att/att    6/6
vmcai15-dt/isa/goal76                             to/att     24/6
vmcai15-dt/leon/amortize-queue-goal7              att/att    6/6
vmcai15-dt/leon/bsearch-tree-goal4                to/att     20/6
vmcai15-dt/leon/heap-goal10                       to/to      24/17
vmcai15-dt/leon/heap-goal12                       to/to      29/33
vmcai15-dt/leon/heap-goal13                       to/to      23/19
vmcai15-dt/nosg/goal62                            to/to      14/19
vmcai15-dt/nosg/nichomachus-goal9                 att/att    6/8
```

`att` = `attempts_exhausted`，`to` = `timeout`。

---

## 9. 一句话

FULL v2 相对 M2 的缺口，**首先是诊断闭环没接通（空 unproved + 禁 HD 回退）再叠加抽样和 HD 时间税**；不是诊断文本写错。把 unproved 接上，并让「证出但无用」也能走 NEW_DIRECTION。提示词若加例子，只放 §6 从缺失引理抽象出的三类编码缺口（测度–算术定义域、缺侧幺元、双谓词序桥），不要点名具体基准引理。88 道双边失败要以有用性超时和按定义播种为主，不要指望诊断散文单独翻盘。
