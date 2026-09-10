# 根节点 INVALID_GOAL 诊断核实，以及同族失败题的扩展扫描

- **实验**：`ours_full706_deepseekv4flash_cvc5_local`（2026-09-08，DeepSeek-v4-flash + CVC5，TASK_TIMEOUT=1200s）
- **第一批核实**：根节点带 `; INVALID_GOAL:` 的 11 题（§0–§3）
- **扩展扫描**：其余失败题里与这 11 题同文件族的题目（§6–§8）——`crafted_assorted` 共用错误 `cnt`、`crafted_rotate` 共用全脊旋转、`dtt-leon bsearch-tree` 共用偏序 `less`
- **软风险扫描**：公理盖不住量化范围、但函数体并非缺失的几族（§10）——`dtt-leon bsearch-tree` 的部分 `less`、heap 的 heapsort/`sorted`、`autoproof` 的 regexp 与 `weird_nat_mul3*`、以及 `dtt-isa/goal64`
- **核实方法**：把 SMT 文件里的公理当成重写规则，逐步计算具体反例。原文件直接丢给 CVC5 对全称目标返回 `unknown`，因此不以求解器 `sat/unsat` 为裁决，以实例计算为准。
- **日志目录**：`experiments/results/ours_full706_deepseekv4flash_cvc5_local/`

---

## 0. 结论一览

| 题 | 模型反例是否算对 | 当前公理下是不是定理 | 若修正编码 |
|---|---|---|---|
| `ind-ben crafted_assorted/2` | 对 | 不是（结论绑错了 list） | 仍不是 |
| `ind-ben crafted_assorted/3` | 对 | 不是（`cnt` 写反） | 会变成标准定理 |
| `ind-ben crafted_assorted/6` | 对 | 不是（`cnt` 写反） | 会变成标准定理 |
| `ind-ben crafted_assorted/15` | 对 | 不是（`cnt` 写反） | 会变成标准定理 |
| `ind-ben crafted_assorted/17` | 对 | 不是（`cnt` 写反） | 会变成标准定理 |
| `ind-ben crafted_assorted/19` | 对 | 不是（`cnt` 写反） | 会变成标准定理 |
| `ind-ben crafted_rotate/10` | 对 | 不是（全脊旋转不是互逆） | 改成单步旋转才可能是 |
| `ind-ben crafted_rotate/11` | 对 | 不是（全脊旋转不是互逆） | 改成单步旋转才可能是 |
| `dtt-leon bsearch-tree-goal4` | 对（无约束模型） | 不是（`less` 在负数上自由） | 把 `less` 补成全体整数 `<` 后，该尺寸反例消失 |
| `dtt-leon bsearch-tree-goal11` | 对 | 不是（`less` 在负数上自由） | 补全 `less` 后，意图中的定理多半仍成立 |
| `dtt-leon bsearch-tree-goal17` | 对（与 11 同构的模型） | 不是（`less` 在负数上自由） | 同上 |

这 11 次根节点 `INVALID_GOAL` **没有** `generated_add_18sym/0` 那种算术算错的假阳性。问题在基准/编码，不在模型胡写格式。提示词里拿掉根节点的 `INVALID_GOAL` 只会让模型改去硬编引理，**不会把这些题证出来**。

扩展扫描后又确认 **3 道同样不是定理**（`dtt-leon bsearch-tree-goal5/8/14`），都是同一个 `less` 漏洞。`crafted_rotate/0–9` 与 `crafted_assorted/18` 同族但目标在现有公理下仍然像定理，失败是证明难度，不是「公式本来为假」。

软风险几族里，本实验失败题中又确认 **1 道不是定理**：`vmcai15-dt leon/heap-goal11`（`sorted (heapsort l)`）。heapsort 抽出的是降序，而 `sorted` 按升序比较，且递归支误用了 `rsorted`。其余软风险失败题（heap 的长度/leftist、regexp 代数律、`mul3` 交换结合、bsearch 的 goal2/3）在实例计算下**没有**找到反例。

---

## 1. `crafted_assorted` 共用的 `cnt` 公理错误

六题 SMT 都来自 `benchmarks/smtlib2/ind-ben/list/crafted_assorted/*.smt2`，`cnt` 三条公理相同：

```smt
(assert (forall ((x nat)) (= (cnt nil x) zero)))
(assert (forall ((e nat) (tail lst) (x nat))
  (=> (not (= e x)) (= (cnt (cons e tail) x) (cnt tail e)))))
(assert (forall ((e nat) (tail lst))
  (= (cnt (cons e tail) e) (s (cnt tail e)))))
```

第二行在 `e ≠ x` 时递归的是 `(cnt tail e)`，不是 `(cnt tail x)`。查询键会在第一次不相等时被换成表头。下文把自然数写成 `0, 1, 2, …`（即 `zero, (s zero), (s (s zero)), …`），list 写成 `[0,1,2]`。

按错误公理逐步展开时用的规则：

- `cnt(nil, x) = 0`
- `e = x` 时 `cnt(cons e tail, x) = s(cnt(tail, e))`
- `e ≠ x` 时 `cnt(cons e tail, x) = cnt(tail, e)`

---

### 1.1 `crafted_assorted/2`

**目标**（文件第 39 行）：

```smt
(forall ((e nat) (i nat) (l lst) (x lst))
  (=> (and (less i (len x)) (= (get x i) e))
      (less zero (cnt l e))))
```

前提用的是 list `x`，结论却要求**另一个** list `l` 里 `cnt l e > 0`。

**模型原文**（日志 `list/crafted_assorted/2/20260908_204601.log`）：

> The formula is false. Counterexample: `e=zero, i=zero, l=nil, x=(cons zero nil)`. Then `(less zero (len x))` and `(= (get x zero) zero)` hold, but `(cnt nil zero)=zero`, so `(less zero (cnt l e))` is false.

**逐步计算**：

| 项 | 值 |
|---|---|
| `len [0]` | `1` |
| `less 0 1` | 真 |
| `get [0] 0` | `0` |
| `cnt nil 0` | `0` |
| `less 0 0` | 假 |

前提真、结论假。即便把 `cnt` 改成正确递归 `(cnt tail x)`，`l=nil` 这个反例仍然成立。这题是公式绑错变量，不是计数函数写错造成的。

---

### 1.2 `crafted_assorted/3`

**目标**：

```smt
(forall ((l1 lst) (l2 lst))
  (=> (forall ((x nat)) (= (cnt l1 x) (cnt l2 x)))
      (= (len l1) (len l2))))
```

**模型原文**：

> Counterexample: `l1=(cons zero (cons (s zero) nil)), l2=(cons zero nil)` satisfy `(forall ((x nat)) (= (cnt l1 x) (cnt l2 x)))` but not `(= (len l1) (len l2))`.

**逐步计算**（`l1=[0,1]`，`l2=[0]`）：

`cnt(l1, 0)`：头等于查询 → `s(cnt([1], 0))`；`cnt([1], 0)` 头 `1≠0` → `cnt(nil, 1)=0`；故为 `1`。  
`cnt(l1, x)` 对任意 `x≠0`：头 `0≠x` → `cnt([1], 0)=0`。

`cnt(l2, 0)=1`，`cnt(l2, x≠0)=0`。两边作为函数相同，长度却是 `2` 和 `1`。

---

### 1.3 `crafted_assorted/6`

**目标**：

```smt
(forall ((xs lst) (x nat)) (= (cnt xs x) (cnt (rev xs) x)))
```

**模型原文**：

> The cnt axiom for `(not (= e x))` returns `(cnt tail e)` instead of `(cnt tail x)`, so counting is not preserved under reverse. For example, `xs = [zero, s zero, s (s zero)]`, `x = zero`, gives `(cnt xs zero) = (s zero)` but `(cnt (rev xs) zero) = zero`.

**逐步计算**（`xs=[0,1,2]`，`rev xs=[2,1,0]`，查询 `0`）：

- 正向：头 `0=0` → `s(cnt([1,2], 0))`；随后两次 mismatch，落到 `cnt(nil, …)=0`；结果 `1`
- 反向：头 `2≠0` → `cnt([1,0], 2)`；再 mismatch → `cnt([0], 1)`；再 mismatch → `cnt(nil, 0)=0`

两边不相等，与模型一致。

---

### 1.4 `crafted_assorted/15`

**目标**：

```smt
(forall ((xs lst) (ys lst))
  (=> (not (= xs ys))
      (exists ((e nat)) (not (= (cnt xs e) (cnt ys e))))))
```

**模型原文**：

> Counterexample: `xs = (cons zero nil)`, `ys = (cons zero (cons (s zero) nil))`. Then `xs != ys`. But for every natural number `e`: if `e = zero`, both counts are `(s zero)`; if `e != zero`, both collapse to `zero`.

**逐步计算**：

| 查询 `e` | `cnt [0] e` | `cnt [0,1] e` |
|---|---|---|
| `0` | `1` | `1`（第二次 mismatch 把查询换成 `1` 再落到 nil 前，对 `0` 的那次命中仍得到 `1`） |
| `≠0` | `0` | `0` |

没有任何区分元素。错误 `cnt` 把多重集信息塌缩了。

---

### 1.5 `crafted_assorted/17`

**目标**：回文且长度为偶数 ⇒ 每个元素的计数都是偶数。

```smt
(forall ((xs lst))
  (=> (and (= (rev xs) xs)
           (exists ((k nat)) (= (len xs) (mul (s (s zero)) k))))
      (forall ((x nat))
        (exists ((k nat)) (= (cnt xs x) (mul (s (s zero)) k))))))
```

**模型原文**：

> Take `xs = (cons zero (cons zero nil))` and `x = (s zero)`. Then `rev xs = xs` and `len xs = mul (s (s zero)) (s zero)`, but `cnt xs (s zero) = (s zero)`, which cannot equal `mul (s (s zero)) k` for any natural number `k`.

**逐步计算**：`xs=[0,0]`，`rev xs = xs`，`len=2=2·1`。  
`cnt([0,0], 1)`：头 `0≠1` → `cnt([0], 0)=s(cnt(nil,0))=1`。`1` 不是 `2k`。

---

### 1.6 `crafted_assorted/19`

**目标**：回文 ⇒ 全偶数计数，或恰好一个奇数「中心」、其余偶数。

```smt
(forall ((xs lst))
  (=> (= (rev xs) xs)
      (or (forall ((x nat)) (exists ((k nat)) (= (cnt xs x) (mul (s (s zero)) k))))
          (exists ((mid nat))
            (and (exists ((k nat)) (= (cnt xs mid) (s (mul k (s (s zero))))))
                 (forall ((x nat))
                   (=> (not (= x mid))
                       (exists ((k nat)) (= (cnt xs x) (mul (s (s zero)) k))))))))))
```

**模型原文**：

> `xs=(cons zero (cons zero nil))`; `(rev xs)=xs`, but `cnt(xs,(s zero))=(s zero)` and `cnt(xs,(s(s zero)))=(s zero)`, so the conclusion is false.

**逐步计算**（同一 `xs=[0,0]`）：

| 查询 | `cnt` | 奇偶 |
|---|---|---|
| `0` | `2` | 偶 |
| `1` | `1` | 奇 |
| `2` | `1` | 奇 |

「全偶数」失败；「唯一奇数中心」也失败（`1` 和 `2` 都是奇数计数）。与模型一致。

---

## 2. `crafted_rotate/10` 与 `/11`

文件：`benchmarks/smtlib2/ind-ben/tree/crafted_rotate/{10,11}.smt2`。

这里的旋转**不是**单步 AVL 旋转，而是递归转到一条脊：

```smt
(assert (= (rotateLeft Nil) Nil))
(assert (forall ((p tree) (x nat))
  (= (rotateLeft (node p x Nil)) (node p x Nil))))
(assert (forall ((p tree) (x nat) (q tree) (y nat) (r tree))
  (= (rotateLeft (node p x (node q y r)))
     (rotateLeft (node (node p x q) y r)))))

(assert (= (rotateRight Nil) Nil))
(assert (forall ((p tree) (x nat))
  (= (rotateRight (node Nil x p)) (node Nil x p))))
(assert (forall ((p tree) (x nat) (q tree) (y nat) (r tree))
  (= (rotateRight (node (node p x q) y r))
     (rotateRight (node p x (node q y r))))))
```

`rotateLeft` 一直转到右子为空；`rotateRight` 一直转到左子为空。互逆在这种定义下一般不成立。

树写成 `(L v R)`，`Nil` 为叶。

### 2.1 `/11`：`rotateRight(rotateLeft x) = x`

**模型原文**（`tree/crafted_rotate/11/20260908_205947.log`）：

> Counterexample: `x = (node (node Nil zero Nil) zero Nil)`. `rotateLeft(x) = x`, but `rotateRight(x) = (node Nil zero (node Nil zero Nil))`, which is not equal to `x`.

**逐步计算**：`x = ((Nil 0 Nil) 0 Nil)`

- 右子已是 `Nil`，`rotateLeft x = x`
- 左子非空，`rotateRight x = rotateRight (Nil 0 (Nil 0 Nil))`；左子已空，停在 `(Nil 0 (Nil 0 Nil))`
- `rotateRight(rotateLeft x) ≠ x`

与模型原文逐符号一致。

### 2.2 `/10`：`rotateLeft(rotateRight x) = x`

**模型原文**（`tree/crafted_rotate/10/20260908_205939.log`）：

> For `x = (node (node Nil zero Nil) (s zero) (node Nil (s (s zero)) Nil))`, `rotateLeft(rotateRight x)` evaluates to `(node (node (node Nil zero Nil) (s zero) Nil) (s (s zero)) Nil)`, which is not `x`.

**逐步计算**：`x = ((Nil 0 Nil) 1 (Nil 2 Nil))`

1. `rotateRight x`：左子非空，一步变成 `(Nil 0 (Nil 1 (Nil 2 Nil)))`（右脊）
2. `rotateLeft` 该右脊：一直左旋，得到 `(((Nil 0 Nil) 1 Nil) 2 Nil)`（左脊）
3. 结果 ≠ 原来的平衡树

模型写的结果树与重写一致。

---

## 3. `dtt-leon` 二叉搜索树：`less` 只在非负整数上有定义

三份预处理文件：

- `benchmarks/preprocessed/dtt/dtt-leon/bsearch-tree-goal4/bsearch-tree-goal4.smt2`
- `benchmarks/preprocessed/dtt/dtt-leon/bsearch-tree-goal11/bsearch-tree-goal11.smt2`
- `benchmarks/preprocessed/dtt/dtt-leon/bsearch-tree-goal17/bsearch-tree-goal17.smt2`

`less` 的唯一约束是：

```smt
(assert (forall ((x Int) (y Int))
  (=> (and (>= x 0) (>= y 0)) (= (less x y) (< x y)))))
```

负整数上的 `less` 不受约束。`tmember` / `tremove` 靠 `less` 决定走左还是走右；`tcontains`、`content`、以及 `leq`（直接是整数 `<=`）不靠它。因此存在模型：树在 `<=` 意义下有序，搜索却走错边。

这是 **SMT 有效性**（每个公理模型是否都满足目标），不是「若把 `less` 补成全体整数 `<`，数学上还是否成立」。后者对 11/17 多半仍成立；前者对当前文本不成立。

### 3.1 `bsearch-tree-goal11`

**目标**：

```smt
(forall ((i Int) (x Tree))
  (=> (tsorted x) (= (tcontains x i) (tmember x i))))
```

**模型原文**（`dtt-leon/bsearch-tree-goal11/20260908_193905.log`）：

> The goal is not a theorem because `less` is unspecified on negative integers. For example, let `less (-1) (-5)` be true and take `x = (node (-1) (node (-5) leaf leaf) leaf)` with `i = -5`. Then `x` is `tsorted`, but `tcontains x (-5)` is true while `tmember x (-5)` is false because `less (-1) (-5)` sends the search to the empty right subtree.

**在该模型下**：

| 判断 | 结果 | 原因 |
|---|---|---|
| `tsorted x` | 真 | 左子 `-5 ≤ -1`，右子空 |
| `tcontains x -5` | 真 | 遍历全树 |
| `tmember x -5` | 假 | 根上 `less(-1,-5)=true`，走到空右子 |

`tcontains ≠ tmember`，目标在该模型中失败。

若把 `less` 补全成全体整数 `<`，则 `less(-1,-5)` 为假，搜索走进左子，`tmember` 变真，**这棵树不再是反例**。

### 3.2 `bsearch-tree-goal17`

**目标**：

```smt
(forall ((x Tree) (i Int))
  (=> (tsorted x) (= (tmember x i) (mem i (content x)))))
```

**模型原文**（`dtt-leon/bsearch-tree-goal17/20260908_194000.log`）只写了「缺非负假设」，没有给出完整树。用与 goal11 相同的树和 `less(-1,-5)=true`：

- `content x = [-5, -1]`
- `mem(-5, content x)` 为真
- `tmember` 仍为假（同上，走到空右子）

同一模型打碎 goal17。理由方向正确。

### 3.3 `bsearch-tree-goal4`

**目标**：

```smt
(forall ((t Tree) (n Int)) (leq (tsize (tremove t n)) (tsize t)))
```

`tremove` 的重写（节选）：

```smt
(=> (less i d) (= (tremove (node d l r) i) (node d (tremove l i) r)))
(=> (less d i) (= (tremove (node d l r) i) (node d l (tremove r i))))
;; 以及 i = d 的两条
```

**模型原文**（`dtt-leon/bsearch-tree-goal4/20260908_194122.log`）：

> The formula is not a theorem because tremove is underspecified when less is not total/unconstrained, e.g. for `t=(node (-1) leaf leaf)` and `n=0`, no tremove axiom applies and tremove t n can return a larger tree.

**核实**：`t = node(-1, leaf, leaf)`，`n=0`。

- `n ≠ -1`，等式情形的两条用不上
- `less(0,-1)` 与 `less(-1,0)` 都不受公理约束
- 若两者都取假，没有任何 `tremove` 重写能用，`tremove(t,0)` 可以是任意更大的树，例如 `node(0, node(1,leaf,leaf), node(2,leaf,leaf))`，`tsize=3 > tsize(t)=1`

这是 SMT 有效性上的漏洞，模型说的「公理管不到」成立。

若把 `less` 补成全体整数 `<`，则 `less(-1,0)` 为真，删除走到右子 `leaf`，尺寸不增，**这个具体树不再打破不等式**。goal4 的诊断依赖「`less` 保持偏序、可以两边都假」，不是普通整数序下的反例。

---

## 4. 和「根节点不该写 INVALID_GOAL」的关系

这 11 题的标记来自共用 system prompt 里的一句：

```
Do not emit an empty <output> block. Child only, if the CURRENT goal is not a theorem:
empty <output> plus `; INVALID_GOAL: ...`.
```

根节点第一枪就会照着写；随后 `PARSE_RETRY_USER` 又把同一模板塞回去，于是同一诊断被记成多次 `parse_error=空引理输出`。

核实结果是：模型在这 11 题上把「当前 SMT 文本不是定理」说对了。该改的是

1. **基准/编码**：`cnt` 第二公理、`rotateLeft/Right` 的全脊定义、dtt-leon 的 `less` 只覆盖非负整数；
2. **提示词**：根节点不要再教 `INVALID_GOAL`，以免把真定理（如 `generated_add_18sym/0`）也锁进这条回路。

不要在根节点「认出标记就宣判整题 invalid」——那是另一件事，且会被算术假阳性误伤。这 11 题以及下面确认同样非定理的 `bsearch-tree-goal5/8/14`，即使改提示词也证不出来，除非改 SMT。

---

## 5. 源文件与日志路径（第一批 11 题）

| 题 | SMT | 本实验日志 |
|---|---|---|
| assorted/2 | `benchmarks/smtlib2/ind-ben/list/crafted_assorted/2.smt2` | `.../20260908_204556_ind-ben/list/crafted_assorted/2/20260908_204601.log` |
| assorted/3 | 同目录 `3.smt2` | 同日 `.../3/20260908_204601.log` |
| assorted/6 | `6.smt2` | `.../6/20260908_204601.log` |
| assorted/15 | `15.smt2` | `.../15/20260908_204601.log` |
| assorted/17 | `17.smt2` | `.../17/20260908_204601.log` |
| assorted/19 | `19.smt2` | `.../19/20260908_204601.log` |
| rotate/10 | `benchmarks/smtlib2/ind-ben/tree/crafted_rotate/10.smt2` | `.../tree/crafted_rotate/10/20260908_205939.log` |
| rotate/11 | `11.smt2` | `.../11/20260908_205947.log` |
| bst-4 | `benchmarks/preprocessed/dtt/dtt-leon/bsearch-tree-goal4/bsearch-tree-goal4.smt2` | `.../20260908_193556_dtt/dtt-leon/bsearch-tree-goal4/20260908_194122.log` |
| bst-11 | `.../bsearch-tree-goal11/bsearch-tree-goal11.smt2` | `.../bsearch-tree-goal11/20260908_193905.log` |
| bst-17 | `.../bsearch-tree-goal17/bsearch-tree-goal17.smt2` | `.../bsearch-tree-goal17/20260908_194000.log` |

日志根目录：`experiments/results/ours_full706_deepseekv4flash_cvc5_local/`。

---

## 6. 扩展扫描范围

在本实验 **144 道失败题**里，按与第一批相同的三条编码缺陷筛选：

| 族 | 失败题 | 与 11 题的关系 |
|---|---|---|
| `ind-ben crafted_assorted` | `/2,3,6,15,17,18,19` | 全部 23 份 SMT 共用错误 `cnt`；失败里多出的只有 `/18` |
| `ind-ben crafted_rotate` | `/0–11` 全部失败 | `/10,11` 已证不是定理；`/0–9` 共用全脊定义但目标是 flatten/size |
| `dtt-leon bsearch-tree` | `/2,3,4,5,8,11,14,17` | `/4,11,17` 已证；其余同文件里同一条偏序 `less` |
| `vmcai15-dt leon/bsearch-tree` | `/4,5,8,11` | **同号不同因**：`Nat` 上的 `less` 是全定义的，没有负数漏洞 |

未纳入「同样问题」的：`crafted_mirror`（文件里虽有同一套 rotate，目标是 `mirror` 与 flatten，未发现同样的「公式为假」）。`dtt-leon heap-*` 的 `less` 与 BST 同款，但 `merge` 用的是 `ite` 而不是 `tremove` 那种两侧都可假的蕴含式，尺寸/leftist 目标因此仍像定理；heapsort 是否有序见 §10.3，那里确认 `vmcai leon/heap-goal11` 不是定理。

---

## 7. 同族失败题里，同样「当前公理下不是定理」的

### 7.1 `crafted_assorted/18`：同族，但**没找到反例**

目标：回文且长度为**奇数** ⇒ 存在唯一奇数计数中心，其余偶数。

```smt
(forall ((xs lst))
  (=> (and (= (rev xs) xs)
           (exists ((k nat)) (= (len xs) (s (mul (s (s zero)) k)))))
      (exists ((mid nat))
        (and (exists ((k nat)) (= (cnt xs mid) (s (mul (s (s zero)) k))))
             (forall ((x nat))
               (=> (not (= x mid))
                   (exists ((k nat)) (= (cnt xs x) (mul (s (s zero)) k))))))))
```

这是 `/19` 的奇数长度特化。`/17`、`/19` 在偶长度 `[0,0]` 上已被错误 `cnt` 打倒；对奇数长度，穷举了字母表 `{0,1,2}`、长度 1/3/5/7 的全部回文，**零个反例**。例如 `[0,0,0]` 只有 `cnt(0)=3` 为奇，结论反而成立。

因此 `/18` **不能**归入「公式本来为假」。它和 `/17/19` 共用坏公理，失败更像证明难度（本实验 `timeout`）。

同一目录里证成功的 `/0,1,4,5,7–14,16,20–22` 也不依赖「正确的多重集计数」（长度、前缀、`rev`/`app`、或 `cnt` 的键只经 `add` 结合律），所以即使 `cnt` 写反仍可能是定理。

### 7.2 `dtt-leon bsearch-tree-goal5`

目标：`tsize (tremove-all t l) ≤ tsize t`。

`tremove-all` 是对 list 逐个 `tremove`。§3.3 已说明单次 `tremove` 在 `less` 两端都假时可以变成任意更大的树，因此 `tremove-all` 也可以。同一模型：`t = node(-1, leaf, leaf)`，`l = [0]`，与 goal4 相同。**当前文本不是定理。**

### 7.3 `dtt-leon bsearch-tree-goal8`

目标：`tsorted x ⇒ tsorted (tinsert x i)`。

`tinsert` 用 `less` 决定左右，`tsorted` 对左子用整数 `leq`、对右子用 `less`。两者可以不一致。

**反例**：令 `less(-5,-3)=false`（两元都为负，公理不管），其余未提及的负数对仍按整数 `<`。

- `x = node(-1, node(-5, leaf, leaf), leaf)` 仍 `tsorted`（`-5 ≤ -1`）
- `tinsert x (-3)`：根上 `less(-1,-3)` 为假，走进左子；`less(-5,-3)` 为假，再走进 `-5` 的左子
- 得到 `node(-1, node(-5, node(-3, leaf, leaf), leaf), leaf)`
- 结点 `-5` 的左子是 `-3`，`leq(-3,-5)` 为假，**不再 tsorted**

### 7.4 `dtt-leon bsearch-tree-goal14`

目标：`tsorted (tinsert-all leaf x)`（从空树插入任意 list 都有序）。

**反例**：`x = [-5, -1]`，`less(-5,-1)=false`。

1. `tinsert leaf (-5) = node(-5, leaf, leaf)`
2. 再插入 `-1`：`less(-5,-1)` 为假，走进左子
3. 得到 `node(-5, node(-1, leaf, leaf), leaf)`
4. `leq(-1,-5)` 为假，**不是 tsorted**

与 goal8 同一机制：`tinsert` 按可任意解释的 `less` 走，`tsorted` 的左支却用真正的 `<=`。

---

## 8. 同族失败、但是定理仍可能成立（编码一样，不是「公式为假」）

### 8.1 `crafted_rotate/0–9`

目标分别是：

| 题 | 目标 |
|---|---|
| `/0` | `flatten0 (rotateLeft x) = flatten0 x` |
| `/1` | `flatten2 (rotateLeft x) nil = flatten0 x` |
| `/2` | `flatten0 (rotateRight x) = flatten0 x` |
| `/3` | `flatten2 (rotateRight x) nil = flatten0 x` |
| `/4` | `flatten0 (rotateLeft x) = flatten2 x nil` |
| `/5` | `flatten2 (rotateLeft x) nil = flatten2 x nil` |
| `/6` | `flatten0 (rotateRight x) = flatten2 x nil` |
| `/7` | `flatten2 (rotateRight x) nil = flatten2 x nil` |
| `/8` | `size (rotateLeft x) = size x` |
| `/9` | `size (rotateRight x) = size x` |

全脊旋转**保持中序**（`flatten0`）和结点个数。对 `/10`、`/11` 用过的那两棵反例树以及左脊/右脊，逐步计算上述等式全部成立。这 10 题失败是归纳/引理链没走完（本实验均为 `timeout` 或子目标断链），**不是**互逆那种「公式为假」。

### 8.2 `dtt-leon bsearch-tree-goal2`、`goal3`

- `/2`：`tsize t ≤ tsize (tinsert-all t l)`
- `/3`：`tsize (tinsert-all t l) = plus (tsize t) (len l)`

`tinsert` 无论 `less` 真假，都是在某一侧递归并构造一个新 `node`，尺寸结构上必 `+1`。偏序漏洞打不倒这两条。失败应视为证明难度（`tinsert-all` 归纳），与 goal4/5/8/11/14/17 不同。

### 8.3 `vmcai15-dt leon/bsearch-tree-goal4,5,8,11`

同名目标在 StandardDT 里用的是 `Nat` 数据类型，`less` 由 `zero/succ` 完全定义，**没有**「负数上自由」的漏洞。这四题失败不能用 dtt 的反例解释；那是另一套难度（不变量/删除）。同号的 dtt 题里，goal11 在 vmcai 也失败，更说明 Nat 版本仍可能是真定理只是证不出来，而 Int 版本则额外是无效公式。

---

## 9. 扩展扫描后的总表

| 题 | 本实验结果 | 与 11 题同一缺陷？ | 当前公理下是不是定理 |
|---|---|---|---|
| `crafted_assorted/18` | 失败 | 文件里有同一错误 `cnt` | **未证伪**（奇数回文穷举无反例） |
| `crafted_rotate/0–9` | 全部失败 | 同一套全脊 `rotate*` | **仍像定理**（flatten/size 保持） |
| `dtt-leon bsearch-tree-goal5` | 失败 | 同一 `less` + `tremove` | **不是**（goal4 的迭代） |
| `dtt-leon bsearch-tree-goal8` | 失败 | 同一 `less` + `tinsert` vs `leq` | **不是** |
| `dtt-leon bsearch-tree-goal14` | 失败 | 同上 | **不是** |
| `dtt-leon bsearch-tree-goal2,3` | 失败 | 文件里有 `less`，但目标不依赖走哪边 | **仍像定理**（每次插入 +1 结点） |
| `vmcai15-dt bsearch-tree-goal4,5,8,11` | 失败 | 否（`Nat`，`less` 全定义） | 不能用 dtt 反例下结论 |

连同第一批，**当前公理下已确认不是定理**的失败题是：

- `crafted_assorted/2,3,6,15,17,19`
- `crafted_rotate/10,11`
- `dtt-leon bsearch-tree-goal4,5,8,11,14,17`
- `vmcai15-dt leon/heap-goal11`（§10.3；与 `less` 漏洞无关，Nat 编码下同样为假）

---

## 10. 软风险族：名单、本实验失败题、诊断

先前把「函数有定义，但公理盖不住目标的量化范围」叫作**软风险**：不能像 `isa/goal75` 那样静态标 invalid，但有「按这份公理本来就不是定理」的可能。范围是下面五族（`dtt-leon amortize-queue` 虽共用 `less`，11 题本实验全部证出，不列入失败诊断）。

| 族 | 题目 | 软风险是什么 |
|---|---|---|
| `dtt-leon bsearch-tree` | goal1–18（18 题） | `less`/`plus` 只在 `>= 0` 上等于 `<`/`+`，树结点是全体 `Int` |
| `dtt-isa` / `dtt-clam` `goal64` | 2 题 | 同一条部分 `less`；目标里 `n` 有 `>= 0` |
| heap heapsort / 长度 | dtt `heap-goal10/12/13`；vmcai `heap-goal10/11/12/13` | `hasLeftistProperty` 只管 rank/右高，没有堆序；`sorted` 与 heapsort 是否匹配 |
| `autoproof regexp_*` | 13 题 | 代数律是否与 `plus`/`seq` 的空语言吸收一致 |
| `autoproof weird_nat_mul3*` | 17 题 | `mul3`/`mul3acc` 的 `ite` 极偏，像定义错，其实是 TIP 的难定理 |

本实验（`ours_full706_deepseekv4flash_cvc5_local`）里，这几族**失败**的是：

| 族 | 证出 | 失败 |
|---|---|---|
| bsearch-tree 18 | 10：goal1,6,7,9,10,12,13,15,16,18 | 8：goal2,3,4,5,8,11,14,17 |
| goal64 | **2/2**（isa 与 clam 都 `unsat`） | 无 |
| dtt heap 12 | 6：goal1,3–7 | 6：goal2,8,9,10,12,13 |
| vmcai heap 13 | 8：goal2–9 | 5：goal1,10,11,12,13 |
| regexp 13 | 2：`RecAtom`、`RecEps`（直接） | 11：其余全 timeout / attempts_exhausted |
| mul3 17 | 0 | 全部失败 |

goal64 本实验已经证出，不再诊断。bsearch 失败题里 goal4/5/8/11/14/17 已在 §3、§7 确认不是定理；goal2/3 见 §8.2。下面只补 heap / regexp / mul3，以及 bsearch 里本实验新证出的 goal1。

### 10.1 `dtt-leon bsearch-tree`：失败 8 题里 6 假 2 真

同一套偏序 `less` **没有**让整族作废。membership / `tcontains` 不靠 `less` 走哪边，本实验直接或靠引理证出：

- goal6 `tcontains (tinsert x i) i`
- goal7 `tcontains` 对 insert 的更新
- goal9 `tmember (tinsert x i) i`（`tmember` 虽用 `less`，但插入与查找走同一条 `ite`）
- goal10 类似 goal7 的 `tmember` 版
- goal12 `tmember ⇒ tcontains`（一边是搜索、一边是遍历，搜索找到则遍历一定找到）
- goal13 `tinsert-all` 与 `append` 交换
- goal15/18 列表 `mem` 与 `tcontains`/`content`
- goal16 `mem` 对 `append`
- **goal1** `tsize (tinsert t n) = 1 + tsize t`：本实验 LLM 引理证出（355s）。`tinsert` 用 `ite` 总是构造一个新 `node`，尺寸不依赖 `less` 的真假。

失败且**不是定理**的 6 题见 §3、§7。失败但**仍像定理**的只有 goal2、goal3（每次插入结构上 +1 结点，§8.2）。

### 10.2 heap：leftist / 尺寸仍像定理；只有「有序」是假的

`merge` 与 `tremove` 不同：比较写在 `ite (less v2 v1)` 里，总有一条分支，不会出现「两侧 `less` 都假、函数无定义」。`mergea` 按 rank 交换孩子，leftist 不读结点值。因此 `less` 在负数上自由，打不倒「插入/合并保 leftist」和「结点数可加」。

对字母表 `{0,1,2}`、长度 ≤ 4 的全部 121 个列表，按文件里的重写执行：

| 目标 | 实例反例 |
|---|---|
| goal2 `hinsert-all` 保 leftist | 0 |
| goal8 `hsize (hinsert x n) = 1 + hsize x` | 0 |
| goal9 `hsize (hinsert-all l x) = plus (hsize x) (len l)` | 0 |
| goal10 `len (heapsorta x) = hsize x` | 0 |
| goal12 `len (qheapsorta x (cons v l)) = 1 + len (qheapsorta x l)` | 0 |
| goal13 `len (qheapsorta x l) = plus (hsize x) (len l)` | 0 |

dtt 上 goal2/8/9 本实验失败、vmcai 上对应题多数已证出（vmcai 文件还累积了前面的 leftist/尺寸引理）。失败应视为归纳深度，不是公式为假。vmcai `heap-goal1`（单次 `hinsert` 保 leftist）这次 timeout，dtt 同题已经 `unsat`。

dtt 没有 heap-goal11。

### 10.3 `vmcai15-dt leon/heap-goal11`：当前公理下不是定理

文件：`benchmarks/preprocessed/vmcai15-dt/leon/heap-goal11/heap-goal11.smt2`。`less` 在 `Nat` 上由 `zero/succ` **完全定义**，不能用 dtt 的负数洞解释。

**目标**：`(forall ((l Lst)) (sorted (heapsort l)))`，且文件已把 goal1–10 的 leftist/尺寸当作公理。

`merge` 在 `less v2 v1` 为真时保留 **v1**（较大者）为根，是最大堆。`heapsorta` 先 `cons` 根再递归 `merge` 左右子，因此输出是**降序**。

`sorted` 的递归支却按升序比较，并且把尾巴交给了 `rsorted`：

```smt
(assert (forall ((x Nat) (z Nat) (y Lst))
  (= (sorted (cons x (cons z y)))
     (and (rsorted (cons z y)) (leq x z)))))
```

`rsorted` 要求 `leq z x`（降序）。所以 `sorted` 对长度 ≥ 2 要求「头 ≤ 第二」且「尾巴降序」，既不是升序也不是降序。

**反例**：`l = (cons zero (cons (succ zero) nil))`，即 `[0,1]`。

1. `hinsert-all [0,1] hleaf` 先插入 `1` 得单结点堆，再插入 `0`。
2. `merge (heap 1 0 …) (heap 1 1 …)`：`less 1 0` 为假，根留下 `1`，得到 `(heap 1 1 (heap 1 0 hleaf hleaf) hleaf)`。
3. `heapsorta` 得到 `(cons (succ zero) (cons zero nil))`，即 `[1,0]`。
4. `sorted [1,0]` = `rsorted [0]` ∧ `leq 1 0`。单元素 `rsorted` 为真，`1 ≤ 0` 为假。

本实验日志 `leon/heap-goal11/20260908_191528.log` 里模型写「`heapsorta` 产生升序、与 `rsorted` 尾巴冲突」。升序说反了——实际是降序；「目标不是定理」仍对。即便把 `merge` 改成最小堆、输出改成升序 `[0,1,2]`，`sorted` 仍会因尾巴要 `rsorted` 而在长度 ≥ 3 上失败（`rsorted [1,2]` 要求 `2 ≤ 1`）。两条编码问题叠在一起，只改堆序或只改 `sorted` 的递归函数都不够。

### 10.4 `autoproof regexp_*`：11 题失败，未找到反例

函数都有定义。目标比的是 `recognise`（语言），不是语法上的 `Plus`/`plus` 相等。`plus` 对 `Nil` 吸收只出现在导数 `step` 里，会改变正则的语法形状，不必然改变语言。

在构造深度 ≤ 1 的全部 40 个正则、字母表 `{X,Y}`、长度 ≤ 2 的全部字符串上，下列失败目标的两边 `recognise` **全部一致**（0 个反例）：

- `PlusCommutative` / `PlusAssociative` / `PlusIdempotent`
- `RecPlus`（`Plus` 即并）
- `SeqAssociative` / `SeqDistrPlus`
- `Star`（`Star p` 与 `Plus Eps (Seq p (Star p))`）
- `RecStar`（空串或 `Seq p (Star p)`）
- `Deeps`（`Star p` 与 `Star (deeps p)`）
- `Reverse`（`recognise (rev r) s` 与 `recognise r (reverse s)`）

这 11 题失败是证明难度（本实验几乎全是 1200s timeout），**不能**标成「编码下语言等式为假」。`RecAtom` / `RecEps` 已直接证出，也说明同一套导数定义可以对简单情形成立。

### 10.5 `autoproof weird_nat_mul3*`：17 题全失败，未找到反例

`mul3` / `mul3acc` 的 `ite` 按「谁 ≥ 2」分三支，看起来像写错，但是 TIP 的三重乘法。在 `{0,…,4}³` 的 125 组参数上：

- `mul3 x y z = x·y·z`
- `mul3 x y z = mul3 y x z`（comm12 / rot 的目标）
- `mul3 x y z = mul3acc x y z`（`same`）

零个反例。结合/旋转目标在 `mul3 = 三重积` 下也成立。这族是难证，不是缺公理或公式为假。

### 10.6 软风险失败题总表

| 题 | 本实验 | 当前公理下是不是定理 |
|---|---|---|
| `dtt-leon bsearch-tree-goal4,5,8,11,14,17` | 失败 | **不是**（§3、§7，`less` 偏序） |
| `dtt-leon bsearch-tree-goal2,3` | 失败 | **仍像定理**（§8.2） |
| `dtt-isa/goal64`、`dtt-clam/goal64` | **证出** | 定理（前提已限制 `n >= 0`） |
| `dtt-leon heap-goal2,8,9,10,12,13` | 失败 | **仍像定理**（长度/leftist，121 个列表无反例） |
| `vmcai leon/heap-goal1,10,12,13` | 失败 | **仍像定理**（goal1 在 dtt 已证出） |
| `vmcai leon/heap-goal11` | 失败 | **不是**（降序 heapsort vs `sorted`） |
| `regexp_*` 除 RecAtom/RecEps | 11 题失败 | **未证伪** |
| `weird_nat_mul3*` 全部 | 17 题失败 | **未证伪**（小值等于三重积） |
