# Vampire 失败反馈信息与引理生成指导

本文整理 Vampire 反馈信息的形式、代码使用方式，以及这些信号如何帮助提高辅助引理的生成质量。

## 一、Vampire 当前使用的信号

当前 Vampire 路径主要使用五类信号：

1. 求解状态；
2. 归纳焦点；
3. 归纳与重写统计；
4. unsat core；
5. proof 或原始输出中的推理轨迹。

其中，真正写入下一轮 prompt 的主要是前 3 类和 unsat core。

## 二、求解状态信号

`vampire_runner.py` 使用 `VampireResult` 保存一次运行结果：

```python
VampireResult(
    proved=False,
    status="incomplete",
    elapsed=2.006,
    stats={...},
    induction_focus=[...],
    induction_formulas=[...]
)
```

结果状态可能是：

```text
unsat       找到证明
timeout     达到时间限制
unknown     无法明确分类
incomplete  当前策略没有找到反驳
error       输入或执行错误
```

例如：

```text
Proof not found in time 2.006 s
SZS status Timeout for template
```

会被转化为：

```json
{
  "proved": false,
  "status": "timeout",
  "elapsed": 2.006
}
```

`timeout` 或 `incomplete` 只表示当前搜索没有完成，不表示目标不成立。

## 三、归纳焦点信号

### 3.1 原始输出形式

对 `mul_comm` 任务运行：

```bash
./vampire/vampire \
  -t 2s \
  --mode vampire \
  --input_syntax smtlib2 \
  --induction struct \
  --induction_gen on \
  --show_induction on \
  benchmarks/preprocessed/ind-ben/nat/crafted_mul_comm/0/template.smt2
```

Vampire 可能输出：

```text
[Induction] process zero != s(X0) in 7.
[Induction] process add(zero,X0) = X0 in 15.
[Induction] process zero = mul(zero,X0) in 17.
[Induction] process mul(sK0,sK1) != mul(sK1,sK0) in 19.
```

其中：

```text
[Induction] process mul(sK0,sK1) != mul(sK1,sK0)
```

说明 Vampire 当前正在处理乘法交换性：

\[
mul(x,y) \neq mul(y,x)
\]

程序会提取为：

```python
[
    "zero != s(X0)",
    "add(zero,X0) = X0",
    "zero = mul(zero,X0)",
    "mul(sK0,sK1) != mul(sK1,sK0)"
]
```

这些项表示当前证明搜索中的归纳对象、构造子关系或目标文字。

### 3.2 归纳公式

Vampire 还会输出归纳公式：

```text
[Induction] formula 44.
! [X0 : 'nat()'] :
(
  mul(sK0,zero) = mul(zero,sK0)
  &
  (
    mul(sK0,X0) = mul(X0,sK0)
    =>
    mul(sK0,s(X0)) = mul(s(X0),sK0)
  )
)
=>
! [X1 : 'nat()] :
  mul(sK0,X1) = mul(X1,sK0)
[structural induction hypothesis (one)]
```

它大致对应：

\[
\begin{aligned}
&mul(x,0)=mul(0,x) \\
&\land \bigl(
mul(x,n)=mul(n,x)
\Rightarrow
mul(x,s(n))=mul(s(n),x)
\bigr) \\
&\Rightarrow
\forall y.\;mul(x,y)=mul(y,x)
\end{aligned}
\]

这类公式可以帮助判断：当前问题是否已经进入归纳步骤，以及归纳假设是否能够匹配归纳结论。

## 四、归纳统计信号

Vampire 的 `--statistics full` 可能输出：

```text
Generated clauses: 43804
Final active clauses: 470
Fw demodulations: 10215
Bw demodulations: 25
StructuralInduction: 21
InductionApplications: 56
GeneralizedInductionApplications: 4
Time elapsed: 2.006 s
```

### 4.1 `StructuralInduction`

表示结构归纳规则触发的次数。

如果：

```text
baseline:
StructuralInduction: 5

candidate:
StructuralInduction: 12
SZS status: Unsatisfiable
```

说明候选引理可能帮助 Vampire 找到了新的结构归纳路径。

如果：

```text
StructuralInduction: 0
InductionApplications: 0
Generated clauses: 30000
```

可能表示：

- Vampire 没有识别出合适的归纳变量；
- 当前目标形状不适合直接结构归纳；
- LLM 生成的引理没有暴露递归函数或构造子结构。

下一轮可以提示 LLM：

```text
Vampire did not trigger productive structural induction.
Try a lemma that exposes the recursive argument or generalizes the induction variable.
```

### 4.2 `InductionApplications`

表示归纳规则实际应用的次数。

典型模式一：归纳多、重写少：

```text
StructuralInduction: 30
InductionApplications: 80
Fw demodulations: 35
Fw demodulations to eq. taut.: 2
```

这通常表示：

- Vampire 已经在做归纳；
- 但归纳假设没有有效改写当前目标；
- 可能缺少交换律、结合律、展开/折叠或桥接引理。

可以反馈：

```json
{
  "kind": "need_rewrite",
  "detail": "Many induction applications but little productive rewriting.",
  "suggested_actions": [
    "Generate rewrite-oriented lemmas",
    "Prefer lemmas whose left-hand side matches a goal subterm"
  ]
}
```

典型模式二：重写多、归纳少：

```text
Fw demodulations: 12000
InductionApplications: 2
StructuralInduction: 1
```

这可能表示需要更强的归纳命题，而不是继续增加普通等式。下一轮可以要求：

```text
Try a stronger or generalized induction lemma.
Consider an accumulator or helper-function identity.
```

### 4.3 `GeneralizedInductionApplications`

表示带一般化的归纳应用次数。

如果目标中的归纳变量位置复杂、同一项多次出现，或者直接归纳不够强，可能需要：

- 对目标进行一般化；
- 将公共子项替换为变量；
- 引入 accumulator；
- 同时处理多个项的出现位置。

例如目标：

\[
mul(x,y)=mul(y,x)
\]

可以尝试生成更强的辅助性质：

\[
mul(s(x),y)=add(mul(x,y),y)
\]

如果 `GeneralizedInductionApplications` 很少，同时证明搜索停滞，可以反馈：

```text
The current search is not using productive generalized induction.
Generate a stronger lemma rather than another direct restatement of the goal.
```

## 五、重写统计信号

### 5.1 `Fw demodulations`

例如：

```text
Fw demodulations: 10215
```

表示前向重写或化简次数。例如递归定义：

```smt2
(= (plus (succ x) y)
   (succ (plus x y)))
```

可以将：

```text
plus(succ(x), y)
```

改写为：

```text
succ(plus(x,y))
```

如果：

```text
baseline:
Fw demodulations: 7049

candidate:
Fw demodulations: 8990
```

可以得到：

```text
more_demodulations(+1941)
```

这说明候选引理改变了重写空间，但不一定表示证明更接近成功。因此还需要结合等式恒真式数量、passive clause 比例和最终状态判断。

### 5.2 `Bw demodulations`

例如：

```text
Bw demodulations: 25
```

它表示反向重写或反向化简。当前代码将前向和反向重写合并为：

```python
dem_delta =
    delta("Fw demodulations")
    + delta("Bw demodulations")
```

可能得到：

```text
more_demodulations(+1840)
```

### 5.3 `Fw demodulations to eq. taut.`

例如：

```text
Fw demodulations to eq. taut.: 82
```

它表示重写后产生了等式恒真式或可以直接消除的等式。这个信号通常比单纯的 demodulation 数量更有价值。

例如：

```text
baseline:
Fw demodulations to eq. taut.: 36

candidate:
Fw demodulations to eq. taut.: 82
```

反馈：

```text
more_eq_taut_demod(+46)
```

当前代码中：

```python
if taut_delta > 8:
    score += 1.25
    signals.append(f"more_eq_taut_demod(+{taut_delta})")
```

这表示候选引理产生了有效等式化简，下一轮可以围绕相同的重写方向生成桥接引理。

## 六、Clause 与搜索规模信号

### 6.1 `Generated clauses`

```text
Generated clauses: 43804
```

表示生成过的子句总数。

它不是越高越好。

如果：

```text
baseline:
Generated clauses: 10000
status: timeout

candidate:
Generated clauses: 18000
status: unsat
```

说明新增搜索可能是有效的。

但如果：

```text
baseline:
Generated clauses: 10000
Final passive clauses: 800

candidate:
Generated clauses: 80000
Final passive clauses: 30000
status: timeout
```

则更像是搜索爆炸。下一轮应要求 LLM：

```text
Prefer smaller and more goal-directed lemmas.
Avoid overly general quantified formulas.
```

### 6.2 `Final active clauses`

```text
Final active clauses: 470
```

表示最终进入 active set 的子句数量。它可以和 `Generated clauses` 一起构成搜索集中度指标，但不能单独解释。

### 6.3 `Final passive clauses`

```text
Final passive clauses: 1200
```

表示仍等待处理的子句数量。

当前代码比较：

```python
passive_ratio =
    Final passive clauses / Generated clauses
```

例如：

```text
baseline:
Generated clauses: 30000
Final passive clauses: 5000
ratio = 0.167

candidate:
Generated clauses: 28000
Final passive clauses: 1000
ratio = 0.036
```

可能产生：

```text
lower_passive_ratio
```

它表示候选引理可能使搜索更加聚焦。

## 七、Superposition 信号

Vampire 可能输出：

```text
Forward superposition: 2968
Backward superposition: 1531
Self superposition: 22
```

这些指标反映等式之间的组合推理活动。

如果 superposition 增加，同时出现更多等式恒真式并最终证明成功，可以认为候选引理扩大了有效的等式组合。

但如果：

```text
Forward superposition: +30000
Generated clauses: +50000
Final passive clauses: +25000
Fw demodulations to eq. taut.: +0
status: timeout
```

则更像是搜索爆炸，而非有效进展。应当生成更小、更定向的重写引理。

当前 `parse_vampire_stats` 已经解析 Forward/Backward superposition，但 `compute_progress_score` 尚未直接使用它们评分。

## 八、整数归纳信号

对于整数递归或算术约束问题，Vampire 可能输出：

```text
IntegerInfiniteIntervalInduction: 1846
IntegerFiniteIntervalInduction: 176
IntegerInfiniteIntervalUpInduction: 1753
IntegerFiniteIntervalUpInduction: 82
IntegerInfiniteIntervalDownInduction: 93
IntegerFiniteIntervalDownInduction: 94
```

这些指标可以帮助区分：

- ADT 结构归纳问题；
- 整数区间归纳问题；
- 向上归纳；
- 向下归纳；
- 有界区间与无界区间归纳。

例如：

```text
IntegerInfiniteIntervalInduction: 1800
StructuralInduction: 0
```

说明问题主要卡在整数归纳，而不是 ADT 结构归纳。此时下一轮应偏向生成：

```text
arithmetic bridge lemmas
monotonicity lemmas
recurrence-strengthening lemmas
```

这些指标当前已经解析，但尚未全部纳入 progress score。

## 九、`MaxInductionDepth`

示例：

```text
MaxInductionDepth: 1
```

如果 Vampire 不断进行归纳但反复达到深度限制，可能说明需要：

- 更强的归纳命题；
- 更好的目标一般化；
- 辅助不变量；
- 而不是简单增加搜索时间。

可反馈：

```text
The search repeatedly reaches the induction-depth boundary.
Generate a stronger generalized lemma or an auxiliary invariant.
```

## 十、unsat core 信号

当候选引理已经帮助 Vampire 证明目标时，程序会对引理命名：

```smt2
(assert (! lemma_1 :named lemma_1))
(assert (! lemma_2 :named lemma_2))
```

Vampire 可能返回：

```text
unsat
(
lemma_1
lemma_2
)
```

如果原始引理是：

```text
L1: add(x,y) = add(y,x)
L2: mul(x,zero) = zero
L3: x = x
```

那么程序会只保留 `L1` 和 `L2`，丢弃 `L3`。

日志形式：

```text
组合引理证出目标；ucore 保留 2/3 条引理
```

注意：unsat core 是证明成功后的筛选信号，不是失败时的卡住信号。

## 十一、失败后的 `failed_lemmas.json`

一次候选引理组合失败后，文件可能类似：

```json
{
  "invalid_lemmas": [],
  "useless_lemma_groups": [
    {
      "lemmas": [
        "(forall ((x nat)) (= (add x zero) (add x zero)))",
        "(forall ((x nat) (y nat)) (= (add x y) (add y x)))"
      ],
      "status": "timeout",
      "hint_kind": "partial_progress",
      "progressive_count": 1
    }
  ],
  "progress_lemmas": [
    {
      "lemma": "(forall ((x nat) (y nat)) (= (add x y) (add y x)))",
      "score": 3.5,
      "signals": [
        "more_demodulations(+1900)",
        "more_eq_taut_demod(+46)",
        "lower_passive_ratio"
      ]
    }
  ],
  "repair_hints": [
    {
      "kind": "induction_stuck",
      "context": "baseline_goal",
      "detail": "Vampire attempted induction but could not finish the proof.",
      "induction_focus": [
        "mul(sK0,sK1) != mul(sK1,sK0)"
      ],
      "suggested_actions": [
        "Generate equational lemmas about constructors appearing in the focus terms",
        "Try a generalized form"
      ]
    }
  ]
}
```

这些内容会被追加到下一轮 prompt：

```text
; SOLVER PROGRESS SIGNALS:
; The following lemmas did NOT finish the proof,
; but Vampire statistics suggest they made rewrite/induction progress.

; Progress lemma 1:
; score=3.50
; more_demodulations(+1900)
; more_eq_taut_demod(+46)
; lower_passive_ratio

; SOLVER-GUIDED REPAIR:
; Vampire attempted induction on:
; mul(sK0,sK1) != mul(sK1,sK0)

; -> Generate equational lemmas about constructors
; -> Try a generalized form
```

## 十二、统计信息与引理质量的关系

统计信息只是搜索行为信号，不是证明证书。例如：

```text
more_instantiations(+1000)
```

并不保证引理是正确或必要的。

更可靠的候选引理通常具有以下组合信号：

```text
InductionApplications 增加
Fw demodulations to eq. taut. 增加
Final passive clause ratio 下降
最终能够证明目标或某个子集能够证明目标
```

整体反馈链路是：

```text
Vampire statistics
        ↓
判断归纳、重写、匹配和搜索规模
        ↓
识别瓶颈：
  归纳不足 / 重写不足 / 搜索爆炸 / 算术归纳不足
        ↓
生成 repair hint
        ↓
引导 LLM 生成更具体的辅助引理
        ↓
再次通过 Vampire 验证
```

## 十三、工程注意事项

不要直接比较 Vampire portfolio 的多个 statistics block。当前系统使用单策略 diagnostic run 进行 baseline/candidate/control 比较，避免不同 portfolio 策略的统计混在一起。

此外，统计增加不等于证明质量提高。尤其是 superposition、generated clauses 和 demodulation 增加时，需要同时观察：

- 是否产生更多等式恒真式；
- passive ratio 是否下降；
- 是否减少了高难度归纳目标；
- 是否最终证明成功。
