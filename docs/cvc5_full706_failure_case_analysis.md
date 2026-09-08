# CVC5 全量 706 失败案例分析

本文基于 `experiments/results/ours_full706_deepseekv4flash_cvc5/`（deepseek-v4-flash + CVC5，墙钟 1200s，40 并行）。706 题证出 534（75.6%），失败 172。对照同族已证题的 `lemma_library.json`、TIP/HipSpec 常用引理，以及各题 `failed_lemmas.json` / `exp_summary.json`。

**主结论：** 很多失败题并不是「没猜到该有的引理」，而是猜到了、却在有用性检查（\(A \land C \vdash G\)，60s）上被 timeout 扔掉，从未变成子目标去证。281 组 useless 里 250 组状态是 `timeout`，0 组是 unsat。本次 flags 含 `FEEDBACK_PROGRESS=off`，没有 3s sidecar 区分「有搜索进展」和「完全没用」。

---

## 0. 实验与流程（和失败相关的部分）

流程：直接 prove（60s）失败 → LLM 生成 \(C\) → 与目标相同 / 未定义符号 / 1s 矛盾检查 → **整组有用性 60s** → 仅当 unsat 才把每条 \(c_i\) 当子目标递归 prove。有用性 timeout 记 `useless`，跳过本 attempt，不加时。

| 模式 | 题数 | 含义 |
|---|---:|---|
| 全是 useless | 78 | 从未通过有用性，库为空 |
| 有进展后超时 | 50 | 找到过有用引理、开始证子目标，1200s 到了 |
| 有用但证不完 | 17 | 过了有用性，attempt 用尽 |
| invalid 为主 | 20 | 假引理 / 与目标相同 / 未定义符号 |
| 空输出为主 | 4 | 格式问题（失败集里不是主因） |

失败题 hint：`need_stronger_lemma` 116、`timeout` 98、`high_difficulty_assertions` 87。

下文每类给 1–3 个代表：目标、需要的引理、LLM 实际给出的引理、流水线怎么处理、预期证明链、改进方向。

---

## 1. 代表用例总表

| 编号 | 题 | 失败模式 | 一句话 |
|---|---|---|---|
| A1 | `autoproof/standard/bin_plus_comm` | 全 useless | 生成了 `plus`/`s` 桥接，60s 有用性全 timeout |
| A2 | `autoproof/standard/sort_BubSortIsSort` | 全 useless | 生成了 bubble–isort 标准引理，从未变子目标 |
| A3 | `vmcai15-dt/leon/heap-goal3` | 全 useless | 生成了已证同胞题用过的 `rank=rightHeight` |
| B1 | `vmcai15-dt/isa/goal80` | 进展后超时 | 证出 insertion-sort 关键一步，孩子反复失败，1200s |
| B2 | `vmcai15-dt/leon/heap-goal1` | 进展后超时 | 证出 `mergea` 保 leftist，插入不变量没走完 |
| C1 | `dtt/dtt-leon/bsearch-tree-goal11` | 有用但证不完 | 证出 3 条 BST 引理，等价性目标 attempt 用尽 |
| D1 | `autoproof/standard/regexp_PlusAssociative` | invalid / 假引理 | 把语法 `plus` 当成语义结合律，1s 即 sat 矛盾 |
| D2 | `autoproof/standard/weird_nat_mul3_assoc1` | same-as-goal + timeout | 把目标换元再交；真正需要的 `add3` 交换则 timeout |
| D3 | `vmcai15-dt/isa/goal75` | 缺定义 | `filter` 无公理，同态引理被 `undefined_symbol` 挡掉 |
| E1 | `dtt/dtt-isa/goal87` | 空输出 + 进展 | 已证 `len(rev)=len`，18 次空输出烧光墙钟 |

---

## 2. 类型 A：猜到了该有的引理，有用性 60s 扔掉

共同机制：\(C\) 方向正确，甚至和已证同胞题库引理同形；有用性全部 `timeout`；`n_obligation_trees=0`，递归从未启动。

改进主方向：有用性 timeout **不要丢**——把 \(C\) 当子目标先证，证完再以 \(C\) 为公理重试 \(G\)（可加长超时）；打开 `FEEDBACK_PROGRESS`；对定向等式在注入公理时加 `:pattern`。

### A1 `bin_plus_comm`（autoproof，attempts_exhausted）

**目标**

```smt2
(forall ((x Bin) (y Bin)) (= (plus x y) (plus y x)))
```

`Bin` 构造子是 `One` / `ZeroAnd` / `OneAnd`，`s` 是二进制后继。`exp_summary`：6 次 LLM 全 `useless`，库 0，子目标 0。solver 430s 几乎全耗在 6×60s 有用性上。

**该族需要的引理**

同数据集唯一证出的 `bin_s`（`toNat (s n) = S (toNat n)`）库里是 Nat 上的

```smt2
(forall ((x Nat) (y Nat)) (= (plus x (S y)) (S (plus x y))))
```

TIP/HipSpec 证 `plus` 交换通常要：

1. `plus (s x) y = s (plus x y)`
2. `plus x (s y) = s (plus x y)`
3. 往往还要 `plus` 结合，或 `toNat` 同态把 Bin 问题推到 Nat。

**LLM 实际给出的（全部 status=timeout）**

| attempt 组 | 引理 | 对不对 |
|---|---|---|
| 1 | `(plus (s x) y) = (s (plus x y))` | 需要的 (1) |
| 2 | (1) + `(plus x (s y)) = (s (plus x y))` | 需要的 (1)(2) |
| 3 | `plus` 结合律 | 需要的 (3) |
| 4 | 结合 + (1) + (2) | 整套桥 |
| 5 | `(plus x (s y)) = (plus (s x) y)` | (1)(2) 的推论 |

**流水线做了什么**

没有 invalid、没有 same-as-goal。每一组当公理加进 \(G\) 后 60s timeout → 记 useless → 下一 attempt。hint 一直是 `need_stronger_lemma`（skolem/conj ≤ 0.05），系统以为「缺更强归纳引理」，其实 \(C\) 已经是标准桥，只是 CVC5 在 60s 内没把它们实例化到 Bin 构造子归纳上。

**预期证明链**

```text
证 L1:  ∀x y. plus (s x) y = s (plus x y)     （对 x 结构归纳，用 s/plus 定义）
证 L2:  ∀x y. plus x (s y) = s (plus x y)     （对 x 或 y 归纳，可用 L1）
证 L3:  ∀x y z. plus (plus x y) z = plus x (plus y z)   （可选）
由 L1,L2,(L3) 对 x 结构归纳推出 plus x y = plus y x
```

当前缺口在第一步之前：L1/L2 从未成为子目标。

**改进**

- 有用性 timeout 仍升级 L1/L2 为子目标（它们比 comm 本身更局部）。
- 注入公理时给 L1 加 `:pattern ((plus (s x) y))`，给 L2 加 `:pattern ((plus x (s y)))`。
- 不要被 `need_stronger_lemma` 带去再生成「更强的 comm」。

---

### A2 `sort_BubSortIsSort`（autoproof，attempts_exhausted）

**目标**

```smt2
(forall ((x list)) (= (bubsort x) (isort x)))
```

`sort_*` 本实验 18 败 / 1 胜。唯一胜利 `sort_ISortCount` 库引理是 count–insert：

```smt2
(forall ((x Int) (h Int) (l list))
  (= (count x (insert2 h l)) (ite (= x h) (S (count x l)) (count x l))))
```

**该题需要的引理（文献 / 标准证明）**

冒泡 = 插入排序的经典链：

```text
L_perm:  ∀x. isort (second (bubble x)) = isort x
         （一次 bubble 不改变排列，对 isort 不变）
L_fix:   ∀x. is-cons x → bubsort x = bubsort (second (bubble x))
         （bubsort 的递归就是对 bubble 的第二分量再排）
L_insert: isort 的定义性引理（cons 情况 = insert2 head (isort tail)）
由 L_perm 与 L_fix 对长度/结构归纳：bubsort x = isort x
```

**LLM 实际给出的（全部 timeout）**

- `isort (second (bubble x)) = isort x`  → 就是 L_perm
- `is-cons` 条件下的 isort 定义性等式  → L_insert
- `bubsort x = bubsort (second (bubble x))` + L_perm  → L_fix + L_perm

hint 同时有 `high_difficulty_assertions`（`bubble`/`insert2`/`isort` 定义反复被点到）和 `need_stronger_lemma`。

**预期证明链与缺口**

引理集合已经构成证明链的骨架。缺口仍是：60s 有用性无法在「把 L_perm、L_fix 当公理」的前提下推完 \(G\)，于是整组丢弃。对排序题，即使 \(C\) 为真，CVC5 也经常需要先**证出** \(C\)（对 bubble 归纳），再回头证 \(G\)。当前顺序把这条路堵死了。

**改进**

与 A1 相同，外加：打开 progress sidecar，避免下一轮把 L_perm 整组重发；子目标应优先证 L_perm（比 `bubsort=isort` 更局部）。

---

### A3 `leon/heap-goal3`（vmcai15-dt，attempts_exhausted）

**目标**

```smt2
(forall ((v Nat) (x Heap) (y Heap))
  (=> (and (hasLeftistProperty x) (hasLeftistProperty y))
      (hasLeftistProperty (mergea v x y))))
```

**同胞已证题给出的「需要的引理」**

`dtt-leon/heap-goal1` 库：

```smt2
(forall ((h Heap))
  (=> (hasLeftistProperty h) (= (rank h) (rightHeight h))))

(forall ((a Heap) (b Heap))
  (=> (and (hasLeftistProperty a) (hasLeftistProperty b))
      (hasLeftistProperty (merge a b))))
```

本数据集失败的 `heap-goal1` 反而证出了与本目标几乎相同的 `mergea` 保 leftist（见 B2）。说明这条引理在本编码下是可证的，只是 **heap-goal3 自己没把它送进子目标**。

**LLM 实际给出的（全部 timeout）**

```smt2
(forall ((h Heap))
  (=> (hasLeftistProperty h) (= (rightHeight h) (rank h))))
```

以及带 `mergea` 右高计算的加强式。这就是已证同胞题用的 L_rank。

**预期证明链**

```text
L_rank:  hasLeftistProperty h → rank h = rightHeight h
L_mergea: 前提 leftist(x), leftist(y), leq (rightHeight y) (rightHeight x)
          → leftist (mergea v x y)
由 L_rank 把 mergea 的 rank 条件改写成 rightHeight，得到目标
```

`heap-goal1`（失败题，见 B2）已经走通了 L_mergea；`heap-goal3` 停在「L_rank 当公理 60s 推不出目标」。

**改进**

- timeout 升级 L_rank 为子目标（dtt 上 depth 2 就能证出）。
- 同数据集、同签名的已证库引理迁移（`rank=rightHeight`、`mergea` 保 leftist）对 heap 族立刻有用。

---

## 3. 类型 B：引理已有用，子树没证完就 1200s

共同机制：有用性至少成功过一次，库里有 1–2 条 `proved` 引理，义务树展开后孩子反复 `failed`，墙钟耗尽。改进不是再发明全新根引理，而是针对**失败孩子**推广、把已证引理锁进后续 attempt、对 `n_library>0` 放宽墙钟，并让 `subgoal_failed` 真正进 prompt（当前会被滤掉）。

### B1 `isa/goal80`（vmcai15-dt，timeout 1200s）

**目标**

```smt2
(forall ((l Lst)) (sorted (sort l)))
```

`sort` 定义为 `sort (cons x y) = insort x (sort y)`。

**需要的引理（标准 IsaPlanner/CLAM）**

```text
L_ins:   sorted ys → sorted (insort x ys)
L_tail:  sorted (cons z zs) → sorted zs
L_step:  sorted (cons z zs) ∧ ¬(less x z) → sorted (cons z (insort x zs))
由 L_ins 对 sort 的递归结构归纳得到目标
```

**LLM / 系统实际达到的**

库里证出了一条比 L_step 略强的形式（depth 2）：

```smt2
(forall ((x Nat) (z Nat) (zs Lst))
  (=> (and (sorted (cons z zs)) (sorted (insort x zs)) (not (less x z)))
      (sorted (cons z (insort x zs)))))
```

义务树（`failed_lemmas_1.json`）反复出现：

| 孩子 | 树状态 |
|---|---|
| L_step（无 `sorted (insort x zs)` 前提） | failed |
| `sorted ys → sorted (insort x ys)`（即 L_ins） | failed |
| `sorted (cons z zs) → sorted zs` | failed |
| 带额外前提的 L_step | **proved**（进库） |

计数：22 次 LLM，11 棵义务树，子目标 1 成功 / 3 失败，库注入 16 次。墙钟 1200s（LLM 565s + 求解器 635s）。

**预期证明链与缺口**

已经摸到正确链，但根目标需要的是 **L_ins**（对任意 sorted 表插入仍 sorted）。系统证出的是 L_ins 在「头元素不小于 x」这一特殊情况下的一步。孩子 L_ins 多次 failed 后，下一轮根 prompt **看不到这条失败公式**（`repair_hint_for_prompt` 丢掉 `subgoal_failed`），于是反复换一套根 \(C\)，而不是推广失败的 L_ins。

**改进**

- 失败孩子公式进下一轮 user prompt，明确要求：泛化变量、补全/去掉过强前提。
- 对已有库的题不要在 1200s 硬切；优先把 L_ins 证完再回到 `sorted (sort l)`。

---

### B2 `leon/heap-goal1`（vmcai15-dt，timeout 1200s）

**目标**

```smt2
(forall ((x Heap) (n Nat))
  (=> (hasLeftistProperty x) (hasLeftistProperty (hinsert x n))))
```

`hinsert` 经 `merge`/`mergea` 定义。

**需要的引理**

```text
L_rank:    leftist h → rank h = rightHeight h
L_mergea:  leftist l ∧ leftist r ∧ leq (rightHeight r) (rightHeight l)
           → leftist (mergea v l r)
L_merge:   leftist a ∧ leftist b → leftist (merge a b)
hinsert x n 展开为 merge，由 L_merge 得目标
```

dtt 上 `heap-goal1` 整题证出，库里正是 L_rank + L_merge。

**本失败题实际达到的**

库：

```smt2
; lib_1 (depth 1, attempt 4)  —— 即 L_mergea（带 rightHeight 条件）
(forall ((v Nat) (l Heap) (r Heap))
  (=> (and (hasLeftistProperty l) (hasLeftistProperty r)
           (leq (rightHeight r) (rightHeight l)))
      (hasLeftistProperty (mergea v l r))))

; lib_2 (depth 2)  —— 过窄的特例，不是 L_merge
(forall ((n Nat))
  (hasLeftistProperty (merge (heap (succ zero) n hleaf hleaf) hleaf)))
```

14 棵义务树，子目标 0 成功 / 4 失败（与 summary 的 `n_subgoals_proved=0` 对照：库引理可能来自更深节点，根统计口径不一致）。23 次 LLM attempt，墙钟耗尽。

**缺口**

L_mergea 已证，缺的是去掉 `rightHeight` 条件、升到 `merge`/`hinsert` 的那一步（要 L_rank）。根上后续 attempt 有 4 次又变成 useless——已经有用的引理没有锁住，搜索又漂走。特例 lib_2 对一般 `hinsert` 几乎没用。

**改进**

- 已证库引理强制注入后续所有有用性/prove，禁止「证出 L_mergea 之后又去猜无关引理」。
- 针对失败孩子生成 L_rank / L_merge，而不是新的根猜想。
- 同族迁移：dtt 已证的 L_rank、L_merge 签名一致即可注入。

---

## 4. 类型 C：有用性过了，attempt 用尽（未到 1200s）

### C1 `dtt-leon/bsearch-tree-goal11`（attempts_exhausted）

**目标**

```smt2
(forall ((i Int) (x Tree))
  (=> (tsorted x) (= (tcontains x i) (tmember x i))))
```

**需要的引理**

BST 上 `tcontains`（结构成员）与 `tmember`（有序查找）一致：

```text
L_false:  tsorted t ∧ ¬ tcontains t i → tmember t i = false
L_ord_r:  tsorted (node d l r) ∧ tcontains r i → less d i
L_ord_l:  对称，tcontains l i → leq i d（或 less）
对树归纳：有序时两条路径判定相同
```

**实际达到的**

库三条全部是上述方向：

```smt2
; lib_1
tsorted t ∧ ¬ tcontains t i → tmember t i = false
; lib_2  （node 情形的 L_false）
; lib_3
tsorted (node d l r) ∧ tcontains r i → less d i
```

25 次 LLM，10 棵义务树，子目标 2 成功 / 3 失败。exit 是 `attempts_exhausted` 不是 timeout。根 attempt 预算用完时，L_ord_l 和「`tcontains → tmember = true`」一侧可能还没闭合。

**预期证明链**

```text
已有 L_false、L_ord_r
还需 L_true: tsorted t ∧ tcontains t i → tmember t i = true
     L_ord_l: tsorted (node d l r) ∧ tcontains l i → less i d 或 leq
对 t 结构归纳拼出等价
```

**改进**

- 子树失败反馈进 prompt，点名还缺「contains 为真的一侧」。
- 根预算用尽但库非空时，应用已证引理再做一次加长 prove，而不是直接 `attempts_exhausted`。
- `less` 在 DTT 上对全体 Int 只部分定义，部分 invalid 来自「对负整数量化」——生成引理应带 `tsorted` 前提，避免无前提的 `less`。

---

## 5. 类型 D：引理本身不合格（假 / 撞目标 / 缺符号）

这类不是「有用性太短」，改 timeout 策略也救不了。

### D1 `regexp_PlusAssociative`（假代数）

**目标（语义：语言相等，不是语法 AST 相等）**

```smt2
(forall ((p R) (q R) (r R) (s list))
  (= (recognise (Plus p (Plus q r)) s)
     (recognise (Plus (Plus p q) r) s)))
```

`plus` 是 regex 上的智能构造（Nil/Eps 吸收），**语法上不结合**。1s 有效性检查对

```smt2
(forall ((x R) (y R) (z R)) (= (plus x (plus y z)) (plus (plus x y) z)))
```

直接 `cvc=unsat`（与公理矛盾）。LLM 诊断也写了「`plus` 不结合」。

真正有用的是 **recognise/step 层**：

```text
step (Plus p (Plus q r)) a = plus (step p a) (plus (step q a) (step r a))
再对字符串归纳 recognise 两侧相同
```

LLM 后几轮确实往 `step`/`recognise` 靠，一组 timeout、一组 unknown；还证出一条「若 head 上 step 相等则 recognise 相等」的条件引理并进库。根目标仍未闭合。`regexp_*` 11 败 / 2 胜，两胜是 `RecAtom`/`RecEps` **直接证**。

**改进**

- 禁止把构造子智能折叠函数的语法结合律当引理；prompt 写明：只对 `recognise`/`step` 生成语义等式。
- 1s sat 检查对这族往往够用（本例已挡住语法结合律）；unknown/timeout 的 `step` 引理应走类型 A 的「先证再试 G」。
- 再堆 equational/term-rewrite prompt 没有用。

---

### D2 `weird_nat_mul3_assoc1`（撞目标 + 真引理 timeout）

**目标**

```smt2
(forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat))
  (= (mul3 (mul3 x1 x2 x3) x4 x5)
     (mul3 x1 x2 (mul3 x3 x4 x5))))
```

**LLM**

- 把目标换元再交 → `Same as original goal`（浪费 2 个 attempt）。
- 一条错误展开式 → `contradicts axioms`。
- 真正有用的方向：`mul3` 前两元交换、对 `Z` 的零化 —— 全部有用性 timeout。

TIP 上这族通常先证 `add3` 交换/结合，再提升到 `mul3`。17 题全败。定义是多层 `ite`，模型既容易撞目标，也容易写假展开。

**预期证明链**

```text
add3 交换 / 旋转
mul3 x y Z = Z 等零化
mul3 对单个 S 的递归展开（必须与公理 ite 一致，不能手写「看起来像」的等式）
再证五元结合
```

**改进**

- same-as-goal 在换元规范化后拦截（已有字符级相同检测；缺 α 换元）。
- timeout 的 `add3`/`mul3` 交换按类型 A 升级为子目标。
- 对「定义是巨型 ite」的函数，prompt 禁止发明展开式，只允许从公理抄递归条款做定向重写。

---

### D3 `isa/goal75`（公理里没有 filter 定义）

**目标**

```smt2
(forall ((xs Lst)) (= (rev (filter xs)) (filter (rev xs))))
```

`template.smt2` 只公理化了 `append`/`rev`。`filter`、`P` 仅有 `declare-fun`。这是 VMCAI/Leon 编码就缺定义，不是预处理丢公理。

**LLM 给出的正是文献需要的 filter 同态**（`P z` 时 `filter (append ys (cons z nil)) = append (filter ys) (cons z nil)` 等），被 `undefined_symbol:P,filter` 全部挡掉。6/6 invalid。对这份公理，目标不是定理；标 invalid 是对的。

**改进**

- 不要为了刷 unsat 去「发明 filter 定义」（unsound）。
- 根目标若使用未公理化函数，可在诊断里直接 `INVALID_GOAL`，省 6 次 LLM。
- 评测时把这类题从「方法失败」里分开统计。

---

## 6. 类型 E：空输出吞掉预算（次要，但会毁掉已有进展）

### E1 `dtt-isa/goal87`（timeout，18 次 empty）

**目标**

```smt2
(forall ((xs Lst) (ys Lst))
  (=> (= (len xs) (len ys))
      (= (zip (rev xs) (rev ys)) (zrev (zip xs ys)))))
```

**已证库引理（方向完全正确）**

```smt2
(forall ((l Lst) (m Lst)) (= (len (append l m)) (+ (len l) (len m))))
(forall ((xs Lst)) (= (len (rev xs)) (len xs)))
```

还需要 `zip`/`zrev`/`append` 交互（例如 `zip (append …)`、`zrev (zcons …)`）。34 次 LLM 里 18 次 empty、7 次 invalid、3 次 useless、6 次义务树；子目标 2 成功 / 2 失败。空输出不走 parse retry（标签在就返回 `[]`），attempt 被跳过。

**预期证明链**

```text
len (rev xs) = len xs          —— 已证
len (append l m) = len l + len m  —— 已证
zip (rev xs) (rev ys) 在 |xs|=|ys| 下对 xs 归纳
  需要 zip-append / zrev-cons 局部等式
```

**改进**

- 空 `<output>` 且无 `INVALID_GOAL` 当格式错误并 retry（见空输出专项分析）。
- 已证 `len(rev)` 锁进后续 attempt，避免空输出把搜索冲掉。

---

## 7. 按原因看改进方向（对应落地顺序）

| 优先级 | 改什么 | 对准哪些代表 | 预期 |
|---|---|---|---|
| 1 | 有用性 timeout 仍升子目标，证完再试 \(G\) | A1 A2 A3，以及 D2 里 timeout 的 `add3`/`mul3` 交换 | 最大块：78 道全 useless，整族 `sort_*`/`bin_*`/部分 heap |
| 2 | 打开 `FEEDBACK_PROGRESS` | 所有 A，以及 B 里后来又变 useless 的 attempt | 让 L_perm、L_rank 进入下一轮，而不是只看到 `need_stronger_lemma` |
| 3 | 失败孩子进 prompt；库非空则加时/锁库 | B1 B2 C1 E1 | 67 道「已经找到有用引理」 |
| 4 | 公理注入时给定向等式加 `:pattern` | A1 A2，CLAM 的 take/append | 辅助 1，不替代 1 |
| 5 | α 换元 same-as-goal；regex 禁语法结合律；缺定义题早停 | D1 D2 D3 | 省 attempt，不大幅抬上限 |
| 6 | 同数据集同签名库迁移 | A3↔B2，heap/sort/bin | 中等，注意 Nat/Int、缺定义题 |

**不必指望**

- D3 这类缺定义题刷成 unsat。
- 只靠再加 equational prompt 救 `regexp_*`。
- 放宽空输出或非 forall 提取来抬这 172 题（失败主因不是提取器）。

---

## 8. 若只做第 1+2 步，优先回看的题

应用「timeout 升子目标 + progress sidecar」之后，应优先复跑：

- `bin_plus_comm`、`bin_plus_assoc`、`bin_times_*`（A1 同类）
- `sort_BubSortIsSort` 及 `sort_*IsSort` / `*Count`（A2 同类）
- `leon/heap-goal3`（A3）；对照 `dtt-leon/heap-goal1` 是否仍能直接证
- CLAM/Isa 中生成了 `take (len xs) xs = xs`、`len (append …)` 却全 timeout 的题（如 `isa/goal74`、`dtt-isa/goal74`）

成功判据：这些题应出现 `n_obligation_trees>0` 且库非空；若子目标 L1/L2 证出而根仍 timeout，再归入类型 B 用第 3 步收。

---

## 9. 数据路径

| 项 | 路径 |
|---|---|
| 结果根 | `experiments/results/ours_full706_deepseekv4flash_cvc5/` |
| 四份 CSV | 各数据集目录下 `results_*_default.csv` |
| 逐题日志 | `<task>/exp_summary.json`、`failed_lemmas.json`、`lemma_library.json`、`llm_prompts.txt` |
| 旧版 Vampire 未证分析 | `docs/unsolved_failure_analysis.md`（706 题另一后端，勿与本文数字混用） |
