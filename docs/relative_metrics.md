# 相对化求解器反馈指标：改动对照

本文记录把 Vampire / CVC5 反馈从**固定绝对阈值**改为**问题内相对指标**的全部改动点：原始实现、修改后实现、以及未落地的备选方案。

公共实现：`solver_relative_metrics.py`  
评分入口：`vampire_runner.py`、`cvc5_runner.py`  
测试：`tests/test_relative_metrics.py`

设计原则：

```text
绝对计数     → log1p 相对增量 + 每秒活动率
固定难度阈值 → 当前问题内分位数 / top-k
活动数量     → 同一 run 内的活动份额（mix）
搜索变吵     → 体积暴涨且无有效产品时扣分
```

相对门槛仍然是常数（例如约 20% log-gain），但它们作用在**比率/对数增量**上，因此小规模 Nat 引理和大 ADT/整数任务可以共用一套逻辑。

---

## 0. 共用原语（新模块）

| 原语 | 含义 |
|------|------|
| `log_gain(cand, ref)` | `log1p(cand) - log1p(ref)`，与计数规模近似无关 |
| `activity_rate(count, elapsed)` | `count / max(elapsed, 0.2)`，消除诊断时长差异 |
| `is_relative_gain` | 高流量：约 +20% log-gain，且增量 > `max(1, 2%·ref)`；稀有事件：约 +10%，允许 `0→1` |
| `gain_score` | 2× 对应约 1 分，再封顶 |
| `in_problem_hard_cutoff` | 本问题 **正** difficulty 分数的中位数 |
| `is_relative_drop` | 相对下降 ≥ 20% |

未采用、但可替换的备选原语：

- 纯比例 `(cand-ref)/ref`：小计数 `0→3` 会得到无穷大，不如 `log1p` 稳定。
- z-score / MAD：需要多次 control 或历史分布，当前每个 lemma 只有一次 control。
- 按文件大小分桶的绝对阈值：实现简单，但桶边界仍是人为的，跨数据集要重标定。

---

## 1. CVC5 progress：`CONJ / INST / DT / SKOLEM`

### 原始实现

```python
if conj > 20:
    score += min(conj / 80.0, 2.5)
if skol > 0:
    score += min(skol, 2.0)
if inst > 50:
    score += min(inst / 200.0, 2.0)
if dt > 10:
    score += min(dt / 40.0, 1.5)
```

`conj/inst/dt/skol` 是 candidate 相对 control 的**原始计数差**。

问题：小型任务 `INST 12→30` 达不到 50；大型任务 `INST 10000→10040` 却可能过线。

### 修改后

比较 **每秒活动率** 的 log-gain（有 control 时相对 control，否则相对 baseline）：

```python
if is_relative_gain(conj_c, conj_r):      # 高流量，~+20%
    score += gain_score(conj_c, conj_r, 2.5)
if is_relative_gain(skol_c, skol_r, rare=True):
    ...
if is_relative_gain(inst_c, inst_r):
    ...
if is_relative_gain(dt_c, dt_r, rare=True):
    ...
```

信号字符串改为百分数，例如 `more_instantiations(+131%)`，便于跨问题阅读。

### 备选方案

1. **保留绝对门槛作噪声地板，再叠加相对增益**  
   `if inst_delta > 50 or relative_gain > 0.2` —— 大问题假阳性仍在。
2. **只比 control，不除时间**  
   诊断都是 3s 时与现在几乎等价；一旦某次提前结束，每秒率更公平。
3. **按 SMT 规模分桶阈值**（量词数 / AST 大小）  
   需要标定每个 benchmark 族，换数据集就要重做。
4. **用历史 run 的分位数当门槛**  
   改造顺序第 7 步；要先积累 `(问题特征, stats, 是否证出)` 数据。

---

## 2. CVC5 difficulty：固定 `>= 3` 与 `s+2`

### 原始实现

```python
hard_axioms = [t for t, s in difficulty if s >= 3 and "forall" in t ...][:4]
# progress:
if t in b_map and s + 2 < b_map[t]:
    dropped += 1
if gc < gb:  # 目标难度任意下降
    score += 1.5
```

问题：某题全部公理难度为 1～2 时，hard list 为空；另一题全部为 8～10 时，几乎每条都“高难度”。`3→2` 相对很明显，却因未降满 2 分而不计。

### 修改后

- **Hard axioms**：本问题正分数的**中位数及以上**，最多 4 条。单独一条 `difficulty=1` 也会被当作该题难点。
- **Drop**：相对下降 ≥ 20%（`10→8` 与 `3→2` 都算）。目标难度下降按 `min(drop/0.5, 1)` 加权。

### 备选方案

1. **固定 top-k，不问分数**  
   最简单；若所有断言 difficulty 都接近，会把并不难的公理送进 prompt。
2. **前 25% 分位（更严）或前 75%（更松）**  
   把 `HARD_AXIOM_PERCENTILE` 从 0.50 调到 0.75 即可。
3. **难度份额**：`s / sum(scores)` 超过均匀份额  
   对分数高度偏斜的问题更稳，实现稍复杂。
4. **跨问题标准化 difficulty**  
   CVC5 的 difficulty 语义依赖策略与时间，跨题不可比，不建议做全局 z-score。

---

## 3. CVC5 repair mix：`conj>=50 and skol<=2`

### 原始实现

```python
if conj >= 50 and skol <= 2:
    need_stronger_lemma
elif skol >= 3 and inst < 30:
    need_rewrite
```

问题：小问题 `conj=8, skol=0` 永远走不到 `need_stronger_lemma`；大问题 `skol=400` 即使远小于 conjecture-gen，也不会被看成“归纳强化不足”。

### 修改后

在**同一次**诊断的量词活动内部看份额：

```text
q_activity = CONJ + SKOLEM + INST

need_stronger_lemma:
  conj/q >= 0.25  且  skol/conj <= 0.05

need_rewrite:
  skol/q >= 0.01  且  inst/skol < 10
```

这是原始比例 `2/50`、`30/3` 的 scale-free 读法。

### 备选方案

1. **继续用绝对数，但按 `Generated-like` 活动分档**  
   例如 `conj > 0.1 * INST_TOTAL`。仍要调系数。
2. **决策树：先看是否有 skolem，再看 inst/skol**  
   更易解释，本质仍是 mix。
3. **与 baseline mix 比较**  
   “加入引理后 conj 份额升高、skol 份额下降”才提示 need_stronger。需要 candidate 诊断，当前 `derive_repair_hints` 只看单次 result（baseline / subgoal）。若要做，应在 `analyze_lemma_progress` 里对 candidate 单独提示。

---

## 4. Vampire progress：`dem>100 / taut>8 / ind>8 / gen>100`

### 原始实现

```python
if dem_delta > 100: ...
if taut_delta > 8: ...
if ind_delta > 8: ...
if gen_b > 100 and gen_c > 100 and ratio_c < 0.7 * ratio_b:
    lower_passive_ratio
```

`lower_passive_ratio` 本身已是相对量，但 `gen>100` 会让小型证明的聚焦信号丢失。

### 修改后

- demod / taut / induction：对 **每秒率** 做 `is_relative_gain`（taut/induction 走 `rare=True`）。
- passive ratio：只要 `Generated clauses >= 1` 就比较；`0.7×` / `0.9×control` 不变。
- 信号为 `more_demodulations(+125%)` 这种百分数。

### 备选方案

1. **demod 用相对增益，taut 仍用绝对 `>8`**  
   taut 是低计数“产品质量”，绝对地板有时更稳；当前用 `rare=True` 兼顾 `0→3` 与 `80→82`。
2. **把 superposition 纳入评分**  
   文档已解析但未使用。建议同样用 log-gain，并与 eq-taut 联合，避免把 superposition 爆炸当进展。
3. **passive ratio 用 logit 差**  
   对极小/极大比例更稳，收益有限。

---

## 5. Vampire repair mix：`ind>=10 and dem<100`

### 原始实现

```python
if ind >= 10 and dem < 100:
    need_rewrite
elif dem >= 500 and ind < 5:
    need_induction_lemma
```

小问题 `ind=6, dem=8` 不会提示缺重写；大问题 `dem=400, ind=4` 达不到 500，也不会提示缺归纳。

### 修改后

```text
mix = induction + demodulation

need_rewrite:
  ind/mix >= 0.08  且  dem/ind < 8

need_induction_lemma:
  dem/mix >= 0.85  且  ind/dem < 0.02
```

另外用份额接上文档里已有、但原先没实现的整数归纳：

```text
need_arithmetic_lemma:
  (IntegerInfinite + IntegerFinite) / (上述 + 结构归纳) >= 0.70
```

### 备选方案

1. **相对 baseline 的 mix 变化**  
   “加入引理后 induction share 升高但 demod share 仍低” → 更像引理质量信号。当前 hints 多来自 baseline/subgoal 单次诊断。
2. **用 `dem / Generated clauses` 当重写效率**  
   可同时诊断搜索爆炸；阈值仍需标定。
3. **`MaxInductionDepth` 反复顶格**  
   文档建议过；深度通常是 1～3 的小整数，用“达到上限且未证出”比相对化更合适，尚未接入。

---

## 6. 搜索爆炸惩罚（新）

### 原始实现

无。体积变大若碰巧跨过绝对门槛，会被当成正进展。

### 修改后

- **Vampire**：`Generated clauses` 每秒率 log-gain ≥ ln(1.5)（约 +50%），且没有 eq-taut / induction / lower_passive_ratio → 扣分并打 `search_explosion(+N%)`。
- **CVC5**：用 **conjecture-gen** 当枚举体积代理（不用 INST，以免把匹配进展打成爆炸）；无 skolem / datatype / difficulty / instantiation 进展时扣分。

### 备选方案

1. **只标记不扣分**  
   让 LLM 看到爆炸，但 progress score 仍可能 ≥ 0.5。
2. **爆炸 = 体积↑ 且 difficulty 不变**  
   对 CVC5 更贴文档；Vampire 没有 difficulty，需继续用 taut/passive。
3. **多次 matched control 估计噪声带宽**  
   改造顺序第 6 步。例如 3 个平凡引理 control，取 stats 的均值±2σ，只有超出带宽才算增益。成本是 3× 诊断时间。

---

## 7. 未在本轮落地的改造顺序后续项

| 项 | 原因 | 若要做 |
|----|------|--------|
| 多次 matched control | 诊断时间 ×N | 在 `analyze_lemma_progress` 对 2～3 个平凡断言取均值/方差 |
| 按数据集分桶标定 | 需要离线统计 | 对 ind-ben / autoproof / dtt 分别估 log-gain 分位数 |
| 学习排序/逻辑回归 | 需要标签 | 用“最终 unsat / 子集证明 / ucore 成员”当正例 |
| 证明图 / instantiation dump | 另一条线 | 见先前关于 proof DAG 的讨论，与阈值无关 |

---

## 8. 行为对照（测试覆盖）

| 场景 | 原始 | 现在 |
|------|------|------|
| `INST 12→30`（小问题） | 不触发 | `more_instantiations` |
| `INST 10000→10040`（大问题） | 可能触发 | 不触发 |
| `difficulty=2` 且为本题最高 | 不进 hard list | 进 hard list |
| `difficulty 3→2` | 不计入 drop | 计入 33% drop |
| `conj=8, skol=0` | 无 need_stronger | 有 |
| `ind=6, dem=8` | 无 need_rewrite | 有 |
| 子句 1000→8000 且无 taut/ind | 可能被当成“更多搜索” | `search_explosion`，分数 ≤ 0 |
| `gen=90` 且 passive 比例明显下降 | 因 `gen>100` 丢掉 | `lower_passive_ratio` |

`Mate_new*.py` 的 `_PROGRESS_SCORE_THRESHOLD = 0.5` **未改**。相对评分仍把 2× 映射到约 1 分，单弱信号继续打折（Vampire ×0.35，CVC5 ×0.4）。

---

## 9. 如何再调

只改 `solver_relative_metrics.py` 顶部常数即可，不必回到绝对计数：

| 常数 | 默认 | 调大则 |
|------|------|--------|
| `LOG_GAIN_MIN` | ln(1.20) | 更少 progress 假阳性 |
| `LOG_GAIN_MIN_RARE` | ln(1.10) | 稀有事件更不敏感 |
| `DIFFICULTY_REL_DROP` | 0.20 | 更少 difficulty-drop 信号 |
| `HARD_AXIOM_PERCENTILE` | 0.50 | hard list 更短、更“尖” |
| `EXPLOSION_LOG_GAIN` | ln(1.50) | 更少爆炸惩罚 |
| `REWRITE_PER_INDUCTION_MAX` 等 mix 比 | 见模块 | 更少/更多 repair kind |
