# 根节点 `INVALID_GOAL` 声称核实（全量 skip 跑 + 失败重测）

- **对象实验**
  - 全量：`experiments/results/ours_full706_deepseekv4flash_cvc5_local_skip`（2026-09-11）
  - 失败重测：`experiments/results/failed89_ancestor_hints_on`（2026-09-15，hints on）
- **背景**：自提交 `1349a8b` 起，根节点即使输出 `; INVALID_GOAL:` 也不会被标成 `node_outcome=invalid`，而是按 **`空引理输出` 做 parse retry**。因此这里核实的是 **LLM 在根上的诊断是否说对**，不是系统是否宣判整题 invalid。
- **方法**：读 SMT 公理 → 按模型给出的实例逐步重写/赋值 → 检查是否与定义性公理矛盾。不以「原文件直接丢给 CVC5」的 `unknown`/`timeout` 为最终裁决（全称目标上常见）。
- **范围**：两轮日志里，根上出现过 `llm_raw goal=template` + `INVALID_GOAL` 的题目共 **6** 道（失败重测里仍出现的是其中 4 道 dtt-isa）。

---

## 0. 结论一览

| 题 | 根 `INVALID` 次数（全量） | 重测是否仍声称 | 模型反例是否算对 | 当前公理下目标是不是定理 | 总评 |
|---|---:|---|---|---|---|
| `dtt/dtt-isa/goal74` | 14 | 是 | **对** | **不是**（`drop`/`minus` 在负数上自由） | 诊断正确 |
| `dtt/dtt-isa/goal76` | 13 | 是 | **对** | **不是**（`take`/`minus` 在负数上自由） | 诊断正确 |
| `dtt/dtt-isa/goal79` | 9 | 是 | **对** | **不是**（`less` 仅约束非负） | 诊断正确 |
| `dtt/dtt-isa/goal80` | 15 | 是 | **对** | **不是**（同上） | 诊断正确 |
| `vmcai15-dt/leon/bsearch-tree-goal11` | 6 | 否（已证出，不在 89 失败集） | **结构有洞，但作废判定过强** | 意图上是定理；`less (succ x) zero` 缺公理是编码味道 | **假阳性根诊断**（同 run 后来证出） |
| `autoproof/standard/tree_Flatten1List` | 1 | 否（重测未再报） | **错** | 定义性方程已唯一确定 `flatten1`；所给赋值违反定义 | **假阳性根诊断** |

**可能有错误的根诊断：2 道**（`bsearch-tree-goal11`、`tree_Flatten1List`）。  
**诊断正确、目标在当前编码下确实不是定理：4 道**（`dtt-isa/goal74/76/79/80`）。

这 4 道 dtt-isa **不在** `skip_nontheorems.txt` 的 16 题名单里，但与文档 `root-invalid-goal-counterexamples.md` 中的「部分 `less` / soft-risk」同类，建议视作编码缺陷而非方法失败。

---

## 1. 诊断正确：`dtt-isa/goal74`

**目标**

```smt
(forall ((i Int) (xs Lst))
  (= (rev (drop i xs))
     (take (minus (len xs) i) (rev xs))))
```

**相关公理（只约束非负）**

- `minus`：仅当 `(>= n 0) ∧ (>= m 0)` 时等于截断减法  
- `drop`：`drop 0`、`drop _ nil`，以及 `(>= x 0)` 时的 `drop (x+1) (cons …)`  
- `take`：对称地只约束非负下标  

**模型 CE（日志）**

- `i = -1`，`xs = (cons 0 nil)`  
- 令 `drop (-1) (cons 0 nil) = (cons 0 nil)`（无公理约束）  
- 令 `minus 1 (-1) = 0`（无公理约束）  

**逐步计算**

| 项 | 值 | 依据 |
|---|---|---|
| `len xs` | `1` | `len` 全定义 |
| `drop (-1) xs` | `[0]` | 赋值（公理未覆盖） |
| LHS `rev (drop …)` | `[0]` | `rev` 全定义 |
| `minus 1 (-1)` | `0` | 赋值 |
| RHS `take 0 (rev xs)` | `nil` | `take 0` 公理 |
| LHS = RHS? | 否 | |

**结论**：反例成立。目标在当前公理下不是定理。根因是 **Int 下标函数只公理化了非负分支**，目标却量化全体 `Int`。

---

## 2. 诊断正确：`dtt-isa/goal76`

**目标**

```smt
(forall ((i Int) (xs Lst))
  (= (rev (take i xs))
     (drop (minus (len xs) i) (rev xs))))
```

**模型 CE（日志，取其一）**

- `i = -1`，`xs = (cons 1 nil)`  
- `take (-1) (cons 1 nil) = (cons 1 nil)`  
- `minus 1 (-1) = 2`  

**逐步计算**

| 项 | 值 |
|---|---|
| LHS `rev (take …)` | `rev [1] = [1]` |
| RHS `drop 2 (rev [1])` | `drop 2 [1] = drop 1 nil = nil`（`drop` 非负递归可展开） |
| 相等？ | 否 |

**结论**：反例成立。与 goal74 同一类编码漏洞。

---

## 3. 诊断正确：`dtt-isa/goal79`

**目标**

```smt
(forall ((x Int) (l Lst))
  (=> (sorted l) (sorted (insort x l))))
```

**关键公理**

```smt
(assert (forall ((x Int) (y Int))
  (=> (and (>= x 0) (>= y 0)) (= (less x y) (< x y)))))
```

`insort` 用 `less` 分支；`sorted` 用真实 `<=`（`leq`）。

**模型 CE**

- `x = -1`，`l = (cons 0 nil)`，`less (-1) 0 = false`  

**逐步计算**

| 项 | 值 |
|---|---|
| `sorted [0]` | `true` |
| `insort (-1) [0]` | `ite(false, …, cons 0 (insort (-1) nil)) = [0, -1]` |
| `sorted [0, -1]` | `leq 0 (-1) = false` → `false` |

**结论**：反例成立。`less` 在含负数时自由，可与 `sorted` 使用的整数序脱节。

---

## 4. 诊断正确：`dtt-isa/goal80`

**目标**

```smt
(forall ((l Lst)) (sorted (sort l)))
```

**模型 CE**

- `l = (cons (-1) (cons (-2) nil))`  
- `less (-1) (-2) = true`（两边皆负，公理不管）  

**逐步计算**

| 项 | 值 |
|---|---|
| `sort [-2]` | `[-2]` |
| `sort [-1,-2] = insort (-1) [-2]` | `ite(true, [-1,-2], …) = [-1,-2]` |
| `sorted [-1,-2]` | `(-1 <= -2) = false` |

**备注**：若误设 `less (-1) (-2) = false`，则 `sort` 得到 `[-2,-1]`，`sorted` 反而为真。模型必须选 `less (-1) (-2) = true`；日志里的选择是对的。

**结论**：反例成立。与 goal79 同根因。

---

## 5. 假阳性：`vmcai15-dt/leon/bsearch-tree-goal11`

**目标**

```smt
(forall ((i Nat) (x Tree))
  (=> (tsorted x) (= (tcontains x i) (tmember x i))))
```

**`less` 公理（Nat）**

```smt
(assert (not (less zero zero)))
(assert (forall ((x Nat)) (less zero (succ x))))
(assert (forall ((x Nat) (y Nat))
  (= (less (succ x) (succ y)) (less x y))))
```

**没有** `∀x. ¬less (succ x) zero`。这与 dtt-leon 上「`less` 在未覆盖点自由」是同一味道，但这里载体是 `Nat` 而非带负的 `Int`。

### 5.1 模型给的反例

- 设 `less (succ zero) zero = true`  
- `i = zero`  
- `x = (node (succ zero) (node zero leaf leaf) leaf)`  

**手工展开**

| 判断 | 结果 |
|---|---|
| `tsorted x` | 左子仅含 `0`，`leq 0 1` 真（由 `less zero (succ _)`）；右子空 → **真** |
| `tcontains x 0` | 左子含 `0` → **真** |
| `tmember x 0` | 根为 `1`，`less 1 0 = true` → 走向**右**子 `leaf` → **假** |

因此在「允许 `less(1,0)=true`」的解释下，`tsorted` 成立但 `tcontains ≠ tmember`。

对规模 ≤3、值域 `{0,1,2}` 的树枚举：在该 `less` 解释下，文件中若干 insert/`tcontains` 相关助手引理的有限实例**未**发现破坏（仍可能有更大反例）。

### 5.2 为什么仍判「根诊断错误 / 假阳性」

1. **同一次全量实验后来证出了该题**（`solved_by=llm`，`winner_profile=cvc5_inductive`，约 787s）。根上的 `INVALID_GOAL` 与最终结果矛盾。  
2. 证出时库中出现了与 CE 直接冲突的引理，例如：  
   `∀ d l r i. tsorted(node d l r) ∧ tcontains l i ⇒ ¬less d i`  
   对 CE 树即要求 `¬less 1 0`，而 CE 依赖 `less 1 0`。  
3. 既有文档 `root-invalid-goal-counterexamples.md` §6 写明：vmcai 的 Nat `bsearch-tree` **不是** dtt 那种「负数 `less`」问题（「Nat 上的 less 是全定义的」——至少在**归纳语义 / 证明器惯用理解**下不应把 `less(1,0)` 当合法模型）。  
4. 根诊断把「缺一条 `¬less (succ x) zero` 的编码味道」说成「目标不是定理并停在 INVALID」，**过强**；真正该说的是 soft-risk，而不是宣判无解。

**错误原因（诊断侧）**：把 dtt-Int 上「守卫型 `less`」的反例模式，套到 Nat BST 上，并取了与 `tsorted`+偏序直觉冲突的 `less` 解释；在归纳证明设定下该解释不被接受。

**编码侧仍值得记一笔**：补上

```smt
(assert (forall ((x Nat)) (not (less (succ x) zero))))
```

可去掉这个 soft-risk 口子（与 dtt-leon 补全 `less` 同类）。

---

## 6. 假阳性：`autoproof/standard/tree_Flatten1List`

**目标**

```smt
(forall ((ps list)) (= (flatten1 ps) (concatMap lam ps)))
```

其中 `apply1 lam = flatten0`（中序打平）。

**模型声称（`llm_prompts.txt` 全文）**

> `flatten1` 在左孩子非 `Nil` 时改写后「再不归约」，故欠定；  
> 反例：`ps = (cons (Node (Node Nil a Nil) b Nil) nil)`，可令 `flatten1 ps = nil2`，而 `concatMap lam ps = (cons2 a (cons2 b nil2))`。

### 6.1 按定义性方程强制展开

记 `L = Node(Nil, a, Nil)`，`head = Node(L, b, Nil)`，`ps = [head]`。

1. `L ≠ Nil` 分支：  
   `flatten1(ps) = flatten1([ L , Node(Nil, b, Nil) ])`
2. 此时头为 `Node(Nil, a, Nil)`，左为 `Nil`：  
   `= cons2(a, flatten1([ Nil , Node(Nil, b, Nil) ]))`？  
   更精确：左 `Nil` 时  
   `= cons2(a, flatten1(cons(Node_2(head'), tail')))`，此处 `Node_2 = Nil`，  
   `= cons2(a, flatten1([Nil, Node(Nil,b,Nil)]))`
3. 头为 `Nil`：丢掉头 → `flatten1([Node(Nil,b,Nil)])`
4. 左 `Nil`：`= cons2(b, flatten1([Nil])) = cons2(b, nil2)`

故 **`flatten1(ps) = [a,b]`**，与 `flatten0(head)` / `concatMap` 一致。

模型把 `flatten1 ps` 赋成 `nil2` **直接违反** `flatten1` 的 `ite` 定义方程，不是合法模型。

### 6.2 「永不归约 / 欠定」为何错

左孩子非 `Nil` 时，方程把

- `Node(L, a, R)`  

改写成列表

- `[ L , Node(Nil, a, R) ]`  

第一棵树的**尺寸严格变小**（`|L| < |Node(L,a,R)|`），左脊深度下降，递归是良基的，函数由方程**唯一确定**，并非欠定。

**结论**：根 `INVALID_GOAL` 为假阳性；失败应归因于证明难度（Autoproof 硬题），不是「公式在当前公理下为假」。

---

## 7. 与系统行为的关系（再次强调）

| 层级 | 行为 |
|---|---|
| Prompt | `Child only, if the CURRENT goal is not a theorem: empty <output> + ; INVALID_GOAL`（`1349a8b`） |
| 根上仍写出 `INVALID_GOAL` | 解析为 **`空引理输出`** → `parse_retry`；**不**写 `node_outcome=invalid` |
| 子节点 `INVALID_GOAL` | 允许空输出，可 `node_outcome=invalid` 并停子节点 |
| 本表 6 题 | 全量 / 重测的 `failed_lemmas.json` 中根 `node_outcome` 均为空；与上表一致 |

因此：「根节点 invalid」在这两轮实验里 = **LLM 文本诊断**，不是 runner 的最终标签。其中 **2 道文本诊断是错的**，**4 道文本诊断对应当前 SMT 下的真非定理**。

---

## 8. 建议

1. **基准/编码**  
   - 为 `dtt-isa/goal74/76/79/80`（及同文件族）补全 `less`/`drop`/`take`/`minus` 在全体 `Int` 上的定义，或把目标加上 `i >= 0` / 元素非负前提；否则应进入 skip/非定理名单，避免算进方法失败。  
   - 可选：为 vmcai Nat `less` 增加 `¬less (succ x) zero`，去掉 soft-risk。  

2. **诊断策略**  
   - 维持「根不做 INVALID 宣判」是对的（本审计里已有假阳性）。  
   - 对 Autoproof 递归函数题，模型常误报「欠定」；parse retry 后应继续要引理，而不是信根诊断。  

3. **不必**因为根上出现 `INVALID_GOAL` 字符串就认为实验又把根标成 invalid——当前代码路径不会。

---

## 9. 源文件与日志

| 题 | SMT | 全量任务日志目录 |
|---|---|---|
| goal74 | `benchmarks/preprocessed/dtt/dtt-isa/goal74/goal74.smt2` | `.../20260911_153446_dtt/dtt-isa/goal74/` |
| goal76 | `.../goal76/goal76.smt2` | `.../dtt-isa/goal76/` |
| goal79 | `.../goal79/goal79.smt2` | `.../dtt-isa/goal79/` |
| goal80 | `.../goal80/goal80.smt2` | `.../dtt-isa/goal80/` |
| bsearch-tree-goal11 | `benchmarks/preprocessed/vmcai15-dt/leon/bsearch-tree-goal11/bsearch-tree-goal11.smt2` | `.../20260911_145620_vmcai15-dt/leon/bsearch-tree-goal11/` |
| tree_Flatten1List | `benchmarks/preprocessed/autoproof/standard/tree_Flatten1List/tree_Flatten1List.smt2` | `.../20260911_160601_autoproof/standard/tree_Flatten1List/` |

失败重测中仍出现根 `INVALID_GOAL` 的：`dtt-isa/goal74/76/79/80`（目录在 `experiments/results/failed89_ancestor_hints_on/20260915_*_dtt/...`）。
