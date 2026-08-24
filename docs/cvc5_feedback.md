# CVC5 失败反馈信息与引理生成指导

本文整理 CVC5 新增反馈代码中实际使用的信号、信号的具体形式，以及这些信号如何帮助提高辅助引理生成质量。

理论分流、solver routing 与实验设计见 [feedback_guided_portfolio.md](feedback_guided_portfolio.md)。

## 一、CVC5 当前使用的信号

当前 CVC5 路径主要使用四类信号：

1. 求解状态；
2. `--stats` 统计；
3. `get-difficulty` 难度信息；
4. baseline、candidate、control 三组运行之间的 progress signal。

`unsat core`、proof、`--dump-instantiations` 虽然 CVC5 支持，但当前代码没有依赖它们进行引理筛选。

## 二、求解状态信号

`cvc5_runner.py` 使用 `CvcResult` 保存一次 CVC5/CVC4 运行结果：

```python
CvcResult(
    proved=False,
    status="timeout",
    elapsed=3.12,
    strategy="cvc5_inductive",
    stats={...},
    difficulty=[...]
)
```

结果状态可能是：

```text
unsat       找到证明
sat         找到满足模型
timeout     达到时间限制
unknown     无法确定
error       执行或输入错误
```

例如：

```json
{
  "proved": false,
  "status": "timeout",
  "elapsed": 3.12,
  "strategy": "cvc5_inductive"
}
```

求解状态主要用于：

- 判断原目标是否已经证明；
- 判断候选引理组合是否有用；
- 失败后写 timeout / unknown 类 repair hint；
- 有用性失败时才触发短 sidecar 诊断（不是入口 60s prove 之前的另一次求解）。

## 三、CVC5 诊断模式

主证明仍然使用多个策略的 portfolio：

```text
cvc5_simple
cvc5_inductive
cvc5_inductive_no_ematching
cvc4_default
```

诊断反馈使用单独的 CVC5 归纳策略：

```218:224:cvc5_runner.py
cmd = [
    binary,
    "--lang=smt2",
    "--full-saturate-quant",
    "--quant-ind",
    "--conjecture-gen",
    f"--tlimit-per={ms}",
    "--stats",
    str(smt2_path),
]
```

首次 60s prove 在 CVC5 策略上会带 `--stats`、`--tlimit-per`，并注入 `produce-difficulty` / `get-difficulty`，失败结果缓存为 `baseline_diag`。有用性失败后的 sidecar 仍用上面这条单策略，超时 3s，用于和 control/candidate 比 progress。不要把不同 portfolio 策略混出来的计数直接相比。

**注意：** sidecar 默认 3s，baseline 可能来自 60s prove，两者不完全可比；这是已知问题，见 `docs/feedback_fix_plan.md`。

## 四、`--stats` 统计信号

CVC5 可能输出：

```text
global::totalTime = 4040ms

theory::datatypes::inferencesFact = {
  DATATYPES_UNIF: 2,
  DATATYPES_INST: 77,
  DATATYPES_LABEL_EXH: 18,
  DATATYPES_COLLAPSE_SEL: 1
}

theory::datatypes::inferencesLemma = {
  DATATYPES_SPLIT: 3
}

theory::quantifiers::inferencesLemma = {
  QUANTIFIERS_INST_E_MATCHING: 129,
  QUANTIFIERS_INST_E_MATCHING_SIMPLE: 702,
  QUANTIFIERS_INST_CBQI_CONFLICT: 6,
  QUANTIFIERS_INST_CBQI_PROP: 145,
  QUANTIFIERS_CONJ_GEN_SPLIT: 6,
  QUANTIFIERS_CONJ_GEN_GT_ENUM: 100,
  QUANTIFIERS_SKOLEMIZE: 8
}
```

当前代码解析的主要统计项包括：

```python
QUANTIFIERS_INST_E_MATCHING
QUANTIFIERS_INST_E_MATCHING_SIMPLE
QUANTIFIERS_INST_CBQI_PROP
QUANTIFIERS_INST_CBQI_CONFLICT
QUANTIFIERS_SKOLEMIZE
QUANTIFIERS_CONJ_GEN_GT_ENUM
QUANTIFIERS_CONJ_GEN_SPLIT
DATATYPES_INST
DATATYPES_SPLIT
DATATYPES_UNIF
```

## 五、量词实例化信号

例如：

```text
QUANTIFIERS_INST_E_MATCHING: 129
QUANTIFIERS_INST_E_MATCHING_SIMPLE: 702
QUANTIFIERS_INST_CBQI_PROP: 145
```

代码将其中一部分聚合为：

```python
INST_TOTAL =
    QUANTIFIERS_INST_E_MATCHING
    + QUANTIFIERS_INST_E_MATCHING_SIMPLE
    + QUANTIFIERS_INST_CBQI_PROP
```

示例：

```json
{
  "QUANTIFIERS_INST_E_MATCHING": 129,
  "QUANTIFIERS_INST_E_MATCHING_SIMPLE": 702,
  "QUANTIFIERS_INST_CBQI_PROP": 145,
  "INST_TOTAL": 976
}
```

它表示 CVC5 正在大量尝试将量词公理实例化到当前目标上。

如果加入某个候选引理后：

```text
candidate INST_TOTAL - control INST_TOTAL = +239
```

则可以记录：

```text
more_instantiations(+239)
```

这可能说明候选引理让更多递归公理能够与目标匹配。

但它不一定表示证明更接近成功，也可能只是增加了搜索量。因此必须和难度下降、datatype 推理以及最终证明状态一起分析。

## 六、猜想生成信号

CVC5 的 `--conjecture-gen` 可能输出：

```text
QUANTIFIERS_CONJ_GEN_GT_ENUM: 100
QUANTIFIERS_CONJ_GEN_SPLIT: 6
```

代码聚合为：

```python
CONJ_TOTAL =
    QUANTIFIERS_CONJ_GEN_GT_ENUM
    + QUANTIFIERS_CONJ_GEN_SPLIT
```

示例：

```json
{
  "CONJ_GEN_GT_ENUM": 100,
  "CONJ_GEN_SPLIT": 6,
  "CONJ_TOTAL": 106
}
```

这表示 CVC5 正在生成候选猜想。

如果：

```text
CONJ_TOTAL 很高
SKOLEMIZE 很低
```

代码认为：

> CVC5 正在枚举和生成候选，但没有形成有效的归纳强化，可能需要更强的归纳引理。

因此生成：

```json
{
  "kind": "need_stronger_lemma",
  "detail": "cvc5 conjecture-gen was active but skolem/induction strengthening stayed low.",
  "suggested_actions": [
    "Strengthen or generalize the goal into an inductive lemma",
    "Try associativity/commutativity/distributivity style facts"
  ]
}
```

这类反馈会推动 LLM 生成：

- 更强的归纳命题；
- 交换律或结合律；
- 分配律；
- accumulator/helper-function 性质；
- 对原目标进行一般化后的性质。

## 七、Skolemization 信号

例如：

```text
QUANTIFIERS_SKOLEMIZE: 8
```

当前实现把它作为归纳/量词强化活动的近似信号。

如果：

```text
SKOLEMIZE 较高
INST_TOTAL 较低
```

可能说明 CVC5 已经进入了归纳式量词处理，但实例化匹配不足，缺少重写桥接引理。

代码会生成类似：

```json
{
  "kind": "need_rewrite",
  "detail": "cvc5 skolemized (induction-like) but instantiations stayed sparse.",
  "suggested_actions": [
    "Propose rewrite lemmas whose LHS matches a subterm of the goal",
    "Unfold recursive definitions one step in a lemma"
  ]
}
```

这里的 `SKOLEMIZE` 并不是 Vampire 那样明确的归纳步骤记录，而是 CVC5 量词处理行为的近似指标。

## 八、ADT 推理信号

CVC5 可能输出：

```text
DATATYPES_INST: 77
DATATYPES_SPLIT: 3
DATATYPES_UNIF: 2
```

代码聚合为：

```python
DT_TOTAL =
    DATATYPES_INST
    + DATATYPES_SPLIT
    + DATATYPES_UNIF
```

结果：

```json
{
  "DATATYPES_INST": 77,
  "DATATYPES_SPLIT": 3,
  "DATATYPES_UNIF": 2,
  "DT_TOTAL": 82
}
```

如果候选引理使 `DT_TOTAL` 增加，可能表示该引理帮助 CVC5 对构造子、选择器或递归数据类型进行了更多推理。

例如：

```text
more_datatype_inference(+60)
```

这类引理可能值得保留，但仍需确认它没有造成搜索爆炸。

## 九、Difficulty 信号

Difficulty 是当前 CVC5 路径最有特色的信号。

代码会临时改写 SMT 文件，加入：

```smt2
(set-option :produce-difficulty true)
```

并在 `(check-sat)` 后加入：

```smt2
(get-difficulty)
```

CVC5 可能返回：

```text
(
  ((forall ((n Nat)) (= (plus zero n) n)) 2)
  ((forall ((n Nat) (m Nat))
      (= (plus (succ n) m)
         (succ (plus n m)))) 10)
  ((forall ((x Lst)) (= (append nil x) x)) 2)
  ((forall ((x Nat) (y Lst) (z Lst))
      (= (append (cons x y) z)
         (cons x (append y z)))) 3)
  ((= (len nil) zero) 1)
  ((forall ((x Nat) (y Lst))
      (= (len (cons x y))
         (succ (len y)))) 5)
  ((not
      (forall ((x Lst) (y Lst))
        (= (len (append x y))
           (plus (len x) (len y))))) 1)
)
```

格式是：

```text
(assertion) difficulty_score
```

例如：

```text
((forall ((n Nat) (m Nat))
    (= (plus (succ n) m)
       (succ (plus n m)))) 10)
```

表示这条递归公理是当前搜索中难度较高的断言。

代码将其保存为：

```python
difficulty: List[Tuple[str, int]]
```

例如：

```python
[
    (
        "(forall ((n Nat) (m Nat)) (= ...))",
        10
    ),
    (
        "(forall ((x Nat)) (= ...))",
        5
    )
]
```

### 9.1 高难度公理

Hard axioms 取**当前问题**中 difficulty 为正的 forall 断言的中位数及以上（最多 4 条），而不是全局 `difficulty >= 3`。因此小型任务里最高的 `difficulty=2` 也会进入提示；大型任务里处于分布底部的 `difficulty=3` 则不会。

```json
{
  "kind": "high_difficulty_assertions",
  "context": "initial_goal",
  "detail": "cvc5 difficulty tracking shows these assertions were frequently involved without finishing the proof.",
  "hard_axioms": [
    "(forall ((n Nat) (m Nat)) (= (plus (succ n) m) ...))"
  ],
  "goal_fragments": [],
  "suggested_actions": [
    "Generate equational lemmas about functions appearing in hard axioms",
    "Propose a generalized inductive lemma",
    "Avoid repeating lemmas already marked invalid or useless"
  ]
}
```

它告诉 LLM：

> 不要随机生成引理，应围绕 difficulty 高的递归函数生成桥接引理或一般化引理。

### 9.2 Difficulty 下降

如果原始目标 difficulty 为 10，加入候选引理后变为 4（相对下降 60% ≥ 20%），则记录：

```text
goal_difficulty_drop(10->4,60%)
```

如果某些递归公理的 difficulty 显著下降，则记录：

```text
axiom_difficulty_drop(x2)
```

表示至少两条公理的 difficulty 下降。

## 十、Progress score

系统不会简单认为“实例化越多越好”，而是比较：

```text
baseline：原始目标
candidate：加入候选引理的目标
control：加入平凡恒真引理的目标
```

control 通常类似：

```smt2
(assert
  (forall ((x Nat))
    (= x x)))
```

这样可以避免由于多加入一个公式而导致统计自然增加的误判。

当前可能产生的 progress signal 包括：

```text
more_conjecture_gen(+40%)
more_instantiations(+131%)
more_skolemize(+50%)
more_datatype_inference(+25%)
goal_difficulty_drop(10->4,60%)
axiom_difficulty_drop(x2)
search_explosion(+80%)
```

评分使用每秒活动率的 log1p 相对增益，而不是 `conj > 20` / `inst > 50` 这类固定计数。Difficulty 使用本问题正分数的中位数作为 hard-axiom 截断，下降按相对比例（≥20%）计算。细节见 `docs/relative_metrics.md`。

如果只有一个较弱信号，代码会降低 score，并附加：

```text
weak_single_signal
```

如果没有可观测进展，则记录：

```text
no_measurable_progress
```

## 十一、一个具体实例

假设目标是乘法交换性，LLM 生成：

```smt2
(forall ((x nat))
  (= (add x zero)
     (add x zero)))
```

以及：

```smt2
(forall ((x nat) (y nat))
  (= (add x y)
     (add y x)))
```

第一条是平凡恒真式，因此 sidecar 诊断时会跳过：

```text
诊断单条#1 跳过：平凡重言式引理
```

加入加法交换律后，CVC5 可能产生：

```text
cvc5诊断单条#2 score=2.70
signals=[
  'more_instantiations(+239)',
  'more_datatype_inference(+60)'
]
```

保存结果：

```json
{
  "lemma": "(forall ((x nat) (y nat)) (= (add x y) (add y x)))",
  "score": 2.7,
  "signals": [
    "more_instantiations(+239)",
    "more_datatype_inference(+60)"
  ]
}
```

它并不表示加法交换律已经被证明有用，而是表示：

> 加入该引理后，CVC5 的量词实例化和 ADT 推理活动发生了明显变化，值得围绕它继续生成或强化引理。

## 十二、Prompt 中的反馈形式

`Mate_new.py` 会把这些信息加入下一轮 LLM prompt：

```text
; SOLVER PROGRESS SIGNALS (cvc5 stats/difficulty):
; The following lemmas did NOT finish the proof,
; but made measurable progress.

; Progress lemma 1
; score=2.70
; more_instantiations(+239), more_datatype_inference(+60)
; (forall ((x nat) (y nat))
;   (= (add x y) (add y x)))

; SOLVER-GUIDED REPAIR
; Repair hint [high_difficulty_assertions]:
; cvc5 difficulty tracking shows these assertions were frequently involved
; without finishing the proof.

; Hard axiom:
; (forall ((n Nat) (m Nat))
;   (= (plus (succ n) m)
;      (succ (plus n m))))

; -> Generate equational lemmas about functions appearing in hard axioms
; -> Propose a generalized inductive lemma
```

下一轮 LLM 应该倾向于生成：

```smt2
(forall ((x Nat) (y Nat))
  (= (plus x y)
     (plus y x)))
```

或者其他围绕 `plus` 递归定义的桥接、一般化性质，而不是生成无关公式。

## 十三、`failed_lemmas.json` 示例

一次候选引理组合失败后，文件可能类似：

```json
{
  "invalid_lemmas": [],
  "useless_lemma_groups": [
    {
      "lemmas": [
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
      "score": 2.7,
      "signals": [
        "more_instantiations(+239)",
        "more_datatype_inference(+60)"
      ]
    }
  ],
  "repair_hints": [
    {
      "kind": "high_difficulty_assertions",
      "context": "initial_goal",
      "detail": "cvc5 difficulty tracking shows these assertions were frequently involved without finishing the proof.",
      "hard_axioms": [
        "(forall ((n Nat) (m Nat)) (= ...))"
      ],
      "goal_fragments": [],
      "suggested_actions": [
        "Generate equational lemmas about functions appearing in hard axioms",
        "Propose a generalized inductive lemma",
        "Avoid repeating lemmas already marked invalid or useless"
      ]
    },
    {
      "kind": "partial_progress",
      "context": "usefulness_check",
      "detail": "The full lemma group did not help cvc5 prove the goal. One lemma showed partial stats/difficulty progress.",
      "suggested_actions": [
        "Build on progress lemmas",
        "Target high-difficulty recursive definitions",
        "Do not repeat the same useless lemma group"
      ]
    }
  ]
}
```

## 十四、当前代码没有使用的 CVC5 信号

### 14.1 Unsat core

虽然 CVC5 支持：

```text
--produce-unsat-cores
--dump-unsat-cores
```

但在量词、ADT 和归纳问题中经常返回空 core：

```text
unsat
(
)
```

因此当前代码不依赖 CVC5 unsat core 做引理剪枝。有用性只做 **一次整组** `A ∧ C → P`（默认 60s）。失败后不再枚举单条/pair 再证明，只对最多 3 条 singleton 做短诊断写下一轮反馈。

### 14.2 Proof

CVC5 支持：

```text
--produce-proofs
(get-proof)
```

但当前代码没有解析 proof 中的具体推理步骤。

### 14.3 Instantiation dump

CVC5 支持：

```text
--dump-instantiations
```

它可以输出具体的量词实例，但当前代码只使用 `--stats` 中的实例化计数，没有解析具体实例项。

### 14.4 Verbose 输出

`-v` 主要输出配置，例如：

```text
setting dt-stc-ind to true due to quantInduction
setting int-wf-ind to true due to quantInduction
```

当前代码没有把这些内容写入 repair hint。

## 十五、重要限制

这些信号都是启发式搜索信号，不是证明证书。

例如：

```text
more_instantiations(+239)
```

只表示加入引理后量词实例化活动增加，并不保证：

- 该引理是逻辑上必要的；
- 该引理最终能够证明目标；
- 该引理比其他引理更好；
- 搜索一定更接近成功。

因此当前 CVC5 反馈链路是：

```text
CVC5 timeout/unknown
        ↓
读取 stats + difficulty
        ↓
比较 baseline / candidate / control
        ↓
生成 progress signal
        ↓
推断需要：
  - 更强归纳引理
  - 重写引理
  - ADT 桥接引理
  - 一般化命题
        ↓
写入 failed_lemmas.json
        ↓
加入下一轮 LLM prompt
```

真正可靠的接受条件仍然是：

```text
CVC5 返回 unsat
```
