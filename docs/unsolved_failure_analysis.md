# 未成功证明问题：代表性描述与失败原因分析

本文基于仓库内 **LLM4Ind-V**（Vampire 后端、default 提示、墙钟 1200s）在 2025-12-04 的四份结果 CSV，整理各数据集中仍未证明成功的问题。相似题只取代表；并结合当前方法（LLM 引理生成 + 有效性/有用性过滤 + 子目标递归证明）分析可能失败原因。

**数据来源**

| 仓库目录 | 论文名称 | 总数 | 已证 | 未证 | CSV |
|---|---|---:|---:|---:|---|
| `vmcai15-dt` | StandardDT | 241 | 214 | 27 | `vampire/results_20251204_150533_vmcai15-dt_default.csv` |
| `dtt` | StandardDTLIA | 168 | 80 | 88 | `vampire/results_20251204_134755_dtt_default.csv` |
| `autoproof` | AutoProofBM | 141 | 19 | 122 | `vampire/results_20251204_121145_autoproof_default.csv` |
| `ind-ben` | IndBen | 156 | 140 | 16 | `vampire/results_20251204_141750_ind-ben_default.csv` |
| **合计** | | **706** | **453** | **253** | 与论文 Table 5 一致 |

> 说明：仓库目前没有 CVC5 主实验（论文 Table 1，Qwen ≈525/706）的逐题 CSV。下文分析针对 **Vampire 后端**；部分原因在 CVC5 路径上不成立（尤其是 AutoProofBM 的 `is-*` tester）。

---

## 1. 当前方法回顾（与失败相关的环节）

LLM4Ind / ProofMate 的核心流程：

1. **初始验证**：后端求解器在短超时内尝试直接证明目标。
2. **LLM 生成猜想**：两种结构化提示交替使用  
   - Strategy 1：等式归纳推理（`prove_prompt_equational_reasoning`）  
   - Strategy 2：项重写与一般化（`prove_prompt_term_rewrite`）  
   每种策略最多尝试 `MAX_ATTEMPTS_PER_PROMPT`（默认 3）次。
3. **过滤**：短时检查引理是否与公理矛盾（无效）；再用求解器判断是否有助于证明目标（有用性 / progress）。
4. **联合验证**：把保留引理插入 proof-goal 块，请求解器证明原目标。
5. **子目标递归**：未证的引理本身再作为新目标递归调用（深度上限 `MAX_RECURSION_DEPTH`，默认 3）。
6. **任务墙钟**：整题 `TASK_TIMEOUT=1200s`；任一子目标失败或超时会导致整题失败。

因此，未证通常落在以下几类机制上：

| 机制代号 | 含义 |
|---|---|
| **S1** | 后端求解器对输入/理论支持不足（Vampire 不吃某些 SMT-LIB2 构造） |
| **S2** | 目标语义正确，但需要多步桥接引理；LLM 生成质量不足或过滤过严 |
| **S3** | 引理子目标本身更难，递归深度/时间预算不够 |
| **S4** | ADT + 线性算术（LIA）混合，Vampire 归纳/算术能力弱 |
| **S5** | 数据结构不变量 / 存在量词 / 多函数耦合，超出当前「等式归纳 + 重写」提示覆盖面 |

---

## 2. StandardDT（`vmcai15-dt`，未证 27/241）

整体成功率高。失败集中在 **堆 / 搜索树不变量**、少数 **列表旋转与 zip**、以及 **Nicomachus 算术恒等式**。amortize-queue 全部成功。

### 2.1 左偏堆不变量（代表：`leon/heap-goal1`）

**同类：** heap-goal1, 3, 4, 7, 10–13（共约 8–10 题）

**问题描述：**  
若堆 `x` 满足左偏性质 `hasLeftistProperty`，则插入元素后仍保持该性质：

```text
∀ x:Heap, n:Nat. hasLeftistProperty(x) ⇒ hasLeftistProperty(hinsert(x, n))
```

涉及 `rank`、`merge`、`hinsert` 等多个递归定义，目标是**保持结构不变量**，不是单纯等式重写。

**可能失败原因：**  
- **S5**：提示词主要引导「等式化简 / 公共子项一般化」，很少要求生成「不变量保持」类引理。  
- **S2/S3**：需要关于 `merge` 保持 leftist、`rank` 与树高关系等中间引理；子引理往往仍依赖同类不变量，递归易超时。  
- Vampire 对复杂 ADT 不变量的结构归纳实例化空间大，即使有部分正确引理也难在预算内饱和。

### 2.2 搜索树删除与规模（代表：`leon/bsearch-tree-goal5`）

**同类：** bsearch-tree-goal4, 5

**问题描述：**  
从树中按列表删除元素后，树大小不增：

```text
∀ l:Lst, t:Tree. tsize(tremove-all(t, l)) ≤ tsize(t)
```

**可能失败原因：**  
- 需要「单次删除减小（或不增）规模」+「对列表归纳」的组合引理。  
- 比较函数 `less`/`leq` 与树序耦合，属于 **S5**；LLM 易生成过弱或无关的交换/结合律式引理。

### 2.3 列表与 zip / take（代表：`isa/goal84`）

**同类：** isa/goal22, 31, 52, 74–76, 84, 87

**问题描述（goal84）：**

```text
∀ n, xs, ys. ztake(n, zip(xs, ys)) = zip(take(n, xs), take(n, ys))
```

**可能失败原因：**  
- 多参数同时归纳（`n` 与两个列表），需要「双/三归纳」或精心一般化；Strategy 1/2 对此覆盖弱（**S2**）。  
- 超时题（goal22/31/52/84/87）多为搜索未收敛而非明显语法不支持。

### 2.4 CLAM：half/len/append（代表：`clam/nosg/goal23`）

```text
∀ x,y. half(len(append(x,y))) = half(len(append(y,x)))
```

**同类：** goal23, 32, 35, 62, 82

**可能失败原因：**  
- 依赖 `len(append)=plus(len,len)`、`plus` 交换、以及 `half` 对偶偶性的引理链（**S2/S3**）。  
- `half` 与奇偶相关，单一等式重写不够。

### 2.5 rotate 与 Nicomachus（代表：`rotate-goal9`，`nichomachus-goal7`）

```text
∀ x. rotate(len(x), x) = x
∀ x,y. mult(tri(x), plus(y,y)) = mult(x, mult(y, succ(x)))
```

**可能失败原因：**  
- `rotate(len x, x)=x` 需要「旋转 n 次」与长度的桥接引理，经典难例（**S2**）。  
- Nicomachus 依赖三角数 `tri` 与乘法分配律链，算术归纳步骤多，Vampire 在 ADT-Nat 上不如在纯整数理论上顺（偏 **S4/S2**）。

---

## 3. StandardDTLIA（`dtt`，未证 88/168）

由 StandardDT 把 `Nat` 及相关运算改写成 `Int` + LIA 守卫（`>= 0` 等）得到。Vampire 对 **ADT+LIA** 支持有限（论文 Table 5 亦指出 LLM4Ind-V 在此弱于 cvc5）。同构目标在 `vmcai15-dt` 上常能证、在 `dtt` 上失败，说明主因是 **理论混合 / 后端能力**，而非题目本身不真。

### 3.1 drop 交换（代表：`dtt-clam/goal9`）

```text
∀ x,y,w≥0, z:Lst.
  drop(w, drop(x, drop(y,z))) = drop(y, drop(x, drop(w,z)))
```

**同类：** 大量 clam goal（如 7–9, 20–21, 27–32, …）涉及 `drop`/`take`/`count`/`rotate` 与 `Int` 参数。

**可能失败原因：**  
- **S4**：归纳在列表上，但递归参数是整数；Vampire 结构归纳与整数区间归纳配合差。  
- LLM 易生成「Nat 风格」引理，却忽略 `>=0` 守卫，导致无效或无用（过滤掉后只剩弱引理，**S2**）。

### 3.2 与 StandardDT 同构的堆/树题（代表：`dtt-leon/heap-goal1`）

目标与 §2.1 相同，仅 `n:Int`。未证数量多于 Nat 版。

**可能失败原因：** **S4 + S5** 叠加；不变量证明在 LIA 编码下更难做结构归纳。

### 3.3 累积反转等价（代表：`dtt-hipspec/rev-equiv-goal4`）

```text
∀ x,y. qreva(qreva(x,y), nil) = qreva(y, x)
```

**同类：** rev-equiv-goal4–8；rotate-goal3,4,7

**可能失败原因：**  
- 需要关于 `qreva` 的结合/累积引理；一般化后的子目标仍难（**S2/S3**）。  
- 在 LIA 数据集中，列表函数本身不依赖 Int，但文件逻辑为 `UFDTLIA`，求解器策略被算术碎片干扰。

---

## 4. AutoProofBM（`autoproof`，未证 122/141）

这是未证最多、且原因最「硬」的数据集。

### 4.1 SMT-LIB2 ADT tester（`standard/` 几乎全部，约 119 题）

**代表：**

| 代表题 | 目标（直觉） |
|---|---|
| `standard/bin_plus` | `toNat(plus(x,y)) = plus2(toNat(x), toNat(y))`（二进制加法正确性） |
| `standard/int_mul_comm` | 自定义整数 `Z` 上乘法交换 |
| `standard/sort_QSortIsSort` | `qsort(x) = isort(x)` |
| `standard/regexp_RecStar` | `recognise(Star(p), s) ↔ …` |
| `standard/weird_nat_mul3_assoc1` | 三元乘法结合律 |

这些文件普遍使用 `(is-Cons …)`、`(is-ZeroAnd …)`、`(ite (is-S x) …)` 等 **SMT-LIB2 标准 datatype tester**。论文明确指出：Vampire 不支持该片段；cvc5 支持。因此 `standard/` 在 LLM4Ind-V 下几乎全军覆没，19 道成功全在 `extend/`。

**可能失败原因：**  
- **S1（主导）**：后端无法正确解释输入；LLM 生成再多引理也无法弥补。  
- 部分题即便换成 cvc5，本身也难（排序正确性、正则语言、weird_nat 多元运算），但仍应优先视为 **求解器前端限制**，而非引理策略失败。

### 4.2 `extend/` 中仍失败的 3 题（代表：`extend/count_tsort_flatten`）

**同类：** `count_tsort_flatten`，`len_tsort_flatten`，`tsort_sort`（均超时 ~1200s）

```text
∀ t:Tree. count(tsort(t)) = count(flatten(t))
```

（`len`/`tsort_sort` 类似：树排序后长度/有序性与 flatten 一致。）

**可能失败原因：**  
- 这里 **不是** tester 问题（`extend/` 可被 Vampire 处理，且同目录多数题已证）。  
- 需要「tsort 是排序」「排序保持 count/len」「flatten 与 to-list 关系」等多层引理（**S2/S3**）。  
- 树归纳 + 排序算法定义深，递归子目标易耗尽 1200s。

---

## 5. IndBen（`ind-ben`，未证 16/156）

生成类题（concat / pref / add / leq）几乎全部成功。失败集中在少数 **crafted** 组合性质。

### 5.1 列表前缀与存在量词（代表：`list/crafted_assorted/8`）

**同类：** crafted_assorted/2,3,6,8,9,15,17,18,19

```text
∀ x,y. pref(x,y) ∧ len(y)=s(len(x))
      ⇒ ∃ e. app(x, cons(e,nil)) = y
```

**可能失败原因：**  
- **S5**：目标含 **存在量词**；当前提示与过滤默认产出全称等式引理，很少构造「见证」或消去 ∃ 的引理。  
- Vampire 对 ADT 上 ∃ 的归纳实例化代价高；超时与提前失败皆有。

### 5.2 镜像与 flatten（代表：`tree/crafted_mirror/0`）

**同类：** crafted_mirror/0–3（整组失败）

```text
∀ x,y. mirror(x,y) ⇒ rev(flatten0(x)) = flatten0(y)
```

**可能失败原因：**  
- `mirror` 是关系而非函数，需同时对两棵树归纳，或先证函数式镜像定义的等价（**S2/S5**）。  
- 需桥接 `flatten0`、`rev`、`app` 的标准引理；若 LLM 只生成单侧引理，有用性过滤可能全部丢掉（**S2**）。

### 5.3 树旋转互逆（代表：`tree/crafted_rotate/10`）

```text
∀ x. rotateLeft(rotateRight(x)) = x
```

**同类：** crafted_rotate/10, 11

**可能失败原因：**  
- 需按树构造器分情形 + 旋转定义展开；看似局部，但依赖「所有形状」的完备 case 分析。  
- 引理过粗（直接复述目标）会被有效性/有用性卡住；过细则子目标爆炸（**S3**）。

### 5.4 偶性与乘法（代表：`nat/crafted_even/1`）

```text
∀ x,y. even(x) ∨ even(y) ⇒ even(mul(x,y))
```

**可能失败原因：**  
- 析取前提 + 需要 `even`/`mul` 的多个分配引理；Strategy 1 偏等式，对逻辑析取案例覆盖弱（**S2**）。  
- 超时（~1200s）说明搜索在推进但未完成，属于预算/引理链长度问题（**S3**）。

---

## 6. 跨数据集的失败模式归纳

按「根因」归类（一题可多因）：

### A. 后端不支持（优先修求解器路径 / 预处理）

- AutoProofBM `standard/*` 的 `is-*` / `ite(is-…)`（约 119 题）。  
- **建议**：Vampire 路径上改写为显式 constructor 匹配；或此类题强制走 CVC5 后端。

### B. ADT + LIA 混合（Vampire 弱项）

- `dtt` 中绝大多数未证（相对 `vmcai15-dt` 同构题）。  
- **建议**：LIA 题优先 CVC5；或对 `Int` 递归参数加强整数归纳相关提示与后端选项。

### C. 不变量 / 算法正确性（提示覆盖不足）

- leftist heap、BST 删除、排序正确性、正则 `recognise`。  
- **建议**：增加「不变量保持」「算法–规范双模拟」类 prompt；对 `hasLeftistProperty` 等谓词显式要求生成保持性引理。

### D. 存在量词与关系型定义

- IndBen `crafted_assorted`（∃）、`crafted_mirror`（关系 `mirror`）。  
- **建议**：提示中允许 Skolem/见证引理；对关系定义先生成函数化等价引理。

### E. 长引理链与递归预算

- `rotate(len,x)=x`、Nicomachus、`count_tsort_flatten`、部分 isa/clam 超时题。  
- **建议**：提高难例子目标超时或深度；利用 Vampire induction focus / repair hints（见 `docs/vampire_feedback.md`）做定向补引理；对已显示 progress 的引理子集加大保留。

### F. 过滤误杀

- 有用性过滤依赖短时求解器信号；对「暂时无用但后续关键」的引理可能过早丢弃。  
- **建议**：对 progress score 中等的引理做延迟保留；结合 unsat core / 归纳焦点写回下一轮 prompt（已有雏形，可加强）。

---

## 7. 代表性问题速查表

| 数据集 | 代表题 | 一句话性质 | 主因 |
|---|---|---|---|
| StandardDT | `leon/heap-goal1` | 插入保持 leftist 不变量 | S5, S2 |
| StandardDT | `leon/bsearch-tree-goal5` | 删除后树规模不增 | S5 |
| StandardDT | `isa/goal84` | zip 与 take 交换 | S2 |
| StandardDT | `clam/nosg/goal23` | half∘len∘append 交换 | S2, S3 |
| StandardDT | `rotate-goal9` | 旋转长度次回到自身 | S2 |
| StandardDTLIA | `dtt-clam/goal9` | Int 参数下 drop 交换 | S4 |
| StandardDTLIA | `dtt-hipspec/rev-equiv-goal4` | 累积反转等价 | S2, S4 |
| AutoProofBM | `standard/bin_plus` | 二进制加法 toNat 同态 | **S1** |
| AutoProofBM | `standard/sort_QSortIsSort` | 快排=插入排序 | S1 (+难证) |
| AutoProofBM | `extend/count_tsort_flatten` | 树排序保持 count | S2, S3 |
| IndBen | `list/crafted_assorted/8` | 前缀差 1 ⇒ ∃ 单元素扩展 | S5 |
| IndBen | `tree/crafted_mirror/0` | 镜像 ⇒ flatten 反转 | S5, S2 |
| IndBen | `tree/crafted_rotate/10` | 左右旋互逆 | S2, S3 |
| IndBen | `nat/crafted_even/1` | 因子偶 ⇒ 积偶 | S2, S3 |

---

## 8. 小结

1. **253** 道未证中，约 **一半（~119）** 可归因于 Vampire 不支持 AutoProofBM `standard/` 的 SMT-LIB2 ADT tester（**S1**），换后端或改写输入即可大幅下降未证数。  
2. **StandardDTLIA（88）** 主要暴露 Vampire 在 ADT+LIA 上的短板（**S4**），与方法的引理策略关系次之。  
3. 真正考验当前 LLM 引理流程的，是 **堆/树不变量、旋转与 Nicomachus、IndBen 的 ∃/关系题、以及 extend 中少数树排序题**（**S2/S3/S5**）。  
4. 后续改进应分三条线并行：**(i)** Vampire 输入规范化 / 分流到 CVC5；**(ii)** 扩展提示覆盖不变量与存在量词；**(iii)** 加强求解器引导的 repair（归纳焦点、progress、ucore）以降低长链超时。

完整逐题列表见对话产物 canvas：`canvases/unsolved-proof-tasks.canvas.tsx`（若本地存在）。
