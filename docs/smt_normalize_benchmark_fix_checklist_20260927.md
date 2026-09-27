# SMT 输入规范化与 Benchmark 语法修复清单

日期：2026-09-27  
依据：[`v5_nohd_noadv_failure_audit_20260927.md`](v5_nohd_noadv_failure_audit_20260927.md) 中「规范化 SMT 输入 / 生成后语法类型检查」相关问题。

## 摘要

**不重跑整库预处理。** 只定点改这 12 道相关文件；`preprocessed.py` 的逻辑改动供以后增量使用，本次不对 `benchmarks/preprocessed` 做全量 `process_directory`。

| 类别 | 数量 | 本次处理 |
|---|---:|---|
| `check-sat` 落在证明目标之前（预处理模板） | 8 | **定点**把唯一 `(check-sat)` 挪到 `; proof goal end` 之后（与 `preprocessed.py` 写出策略一致） |
| Tip 风格 `declare-datatypes` 无法被 cvc5 解析（源文件） | 4 | **定点**改正 `benchmarks/smtlib2/...`，并同步同名预处理副本 / 模板中的对应声明 |
| LLM 候选引理中的未声明符号 / 类型错 / 保留字 | 7（审计下界） | **不是 benchmark 错误**；需运行时 parse/type 门控（未在本次改代码路径中落地） |

---

## 1. 预处理：`check-sat` 必须在目标之后

### 根因

`preprocessed.py` 在处理完**单行** `(declare-fun …)` / `(assert …)` 后未清空 `current_block='functions'`，后续 `(check-sat)` 被并入 functions 段，写出顺序变成：

```text
; functions declarations
...
(check-sat)          ← 错误：查询背景理论
; functions declarations end
; proof goal
(assert (not ...))
```

源文件 `benchmarks/smtlib2/...` 本身顺序通常正确（目标与公理之后才有一次 `check-sat`）；问题出在模板生成。

### 代码修复（已完成）

文件：[`preprocessed.py`](../preprocessed.py)

- 单行声明/断言括号平衡后立即关闭当前块。
- `(check-sat)` / `(exit)` **优先于**未关闭块的续写分支，避免被吞进 axioms。
- 写出模板时**强制**在 `; proof goal end` 之后写入唯一的 `(check-sat)`。
- 保留 `declare-sort` / `declare-const` / `define-fun`。
- 对 Tip 风格 datatype 做规范化（见第 2 节）。
- `__main__` 入口改为：`benchmarks/smtlib2/autoproof` → `benchmarks/preprocessed/autoproof`。

### 定点修复的模板（8）

路径均在 `benchmarks/preprocessed/autoproof/standard/<name>/template.smt2`。  
改法：删掉 functions 段内过早的 `(check-sat)`，在 `; proof goal end` 之后只保留一次 `(check-sat)`。不重写声明/公理正文。

| # | 任务 | 验收 |
|---|---|---|
| 1 | `list_Select` | `check-sat` 在 `; proof goal end` 之后；恰好一次 |
| 2 | `list_return_2` | 同上；`adt_structural` 3s 内对模板得到 `unsat` |
| 3 | `sort_HSortIsSort` | 同上 |
| 4 | `sort_MSortBUCount` | 同上 |
| 5 | `sort_MSortBUIsSort` | 同上 |
| 6 | `sort_TSortCount` | 同上 |
| 7 | `sort_TSortIsSort` | 同上 |
| 8 | `tree_Flatten1List` | 同上 |

`benchmarks/preprocessed/**/template.smt2` 中 **0** 个「`check-sat` 早于 proof goal end」。

### 语法检查（cvc5 + Vampire）

对下列文件均已检查通过（2026-09-27）：

- 上述 8 个 `template.smt2`
- 第 2 节 4 个源文件 + 对应 `template.smt2` + 预处理目录内同名副本（共 12 个路径 × 求解器）

```bash
# cvc5
cvc5 --parse-only path/to/file.smt2   # 无 Parse Error 即通过

# Vampire（与 runner 一致：先把 (is-C t) 改成 ((_ is C) t) 再喂入）
# 实现见 smt_adt_tester_rewrite.rewrite_smtlib_testers / vampire_runner.prepare_vampire_smt_input
vampire --input_syntax smtlib2 -t 1 /tmp/rewritten.smt2
# 不出现 User error / Unrecognized term identifier 即视为语法通过
```

证明查询是否对准目标（可选）：

```bash
cvc5 --lang=smt2 --tlimit=3000 --full-saturate-quant --quant-ind --dt-stc-ind \
  benchmarks/preprocessed/autoproof/standard/list_return_2/template.smt2
# 期望：unsat
```

---

## 2. Benchmark 语法：Tip `declare-datatypes` 直接改正

### 错误形态

Tip/Isa 导出常见写法（**非法 SMT-LIB**）：

```smt2
(declare-datatypes ((T 0)) ((T (C0 ...) (C1 ...))))
```

cvc5 报错形如：`Expected LPAREN_TOK or RPAREN_TOK, got \`T\``。

合法 SMT-LIB：

```smt2
(declare-datatypes ((T 0)) (((C0 ...) (C1 ...))))
```

（去掉类型名后的重复 `T`，构造子列表再包一层括号。）

全库 `cvc5 --parse-only` 扫描（`smtlib2` + `preprocessed` 的 `.smt2`，排除 `with_lemmas` / `harvest` / `valid_`）共发现 **4** 个源文件失败；对应旧模板多已手工修好，但源副本与 `preprocessed/.../<name>.smt2` 仍是坏的。

### 已直接修复的源文件（4）

| # | 文件 | 非法片段 | 修复 |
|---|---|---|---|
| 1 | `benchmarks/smtlib2/autoproof/standard/int_add_assoc.smt2` | `((Z (P ...) (N ...)))` | `(((P ...) (N ...)))` |
| 2 | `benchmarks/smtlib2/autoproof/standard/rotate_self.smt2` | `((Nat (S ...) (Z)))` | `(((S ...) (Z)))` |
| 3 | `benchmarks/smtlib2/autoproof/standard/rotate_structural_mod.smt2` | `((List2 (Cons ...) (Nil)))` | `(((Cons ...) (Nil)))` |
| 4 | `benchmarks/smtlib2/autoproof/standard/relaxedprefix_correct.smt2` | `((list3 (nil3) (cons3 ...)))` | `(((nil3) (cons3 ...)))` |

同步动作（定点，非全量预处理）：把上述合法 `declare-datatypes` 写回

- `benchmarks/preprocessed/autoproof/standard/<name>/<name>.smt2`
- 若模板中仍是 Tip 形态则同样改正（当前 4 题模板原本已是合法形态）

验收：4 源 + 模板 + 副本均通过 **cvc5 `--parse-only`** 与 **Vampire**（经 tester 改写）语法检查；autoproof 下剩余 parse error **0**。

### 预处理侧防护（已完成）

`normalize_tip_datatype` / `normalize_tip_datatypes_in_text`：若源文件仍是 Tip 形态，预处理写副本与模板时自动改写；对已合法的 SMT-LIB 形式幂等。

---

## 3. LLM 候选：语法/类型预检（已实现）

原先只有不完整的 `undefined_symbol` 静态门（只抓「已声明无定义」），且 cvc5 Parse Error 常被记成 `unknown`/`invalid`。

现流程（`LEMMA_WELLFORMED_CHECK`，默认 on）：

1. `apply_static_lemma_screen` 末段：保留字 binder 检查 + `cvc5 --parse-only`（`cvc5_runner.check_lemma_wellformed`）。
2. 失败 gate = `parse_error` / `type_error` → 写入 `illformed_lemmas`，**不**写入 `invalid_lemmas`；`format_screen_retry_user` 把具体错误回传生成器（同 attempt 的 `LLM_SCREEN_RETRIES`）。
3. 仅通过筛查的候选才进入 1s validity 与并行 usefulness profiles；validity 若仍见到 Parse Error，同样走 `illformed` 而非数学 invalid。

关闭：`LEMMA_WELLFORMED_CHECK=off`。测试：`tests/test_lemma_wellformed.py`。

---

## 4. 验收清单（勾选）

- [x] `preprocessed.py`：块状态不会把 `check-sat` 并入 functions
- [x] `preprocessed.py`：模板末尾唯一 `check-sat`，且位于 proof goal 之后
- [x] `preprocessed.py`：Tip datatype 规范化 + 幂等
- [x] `__main__` 路径指向 `benchmarks/smtlib2/autoproof` → `benchmarks/preprocessed/autoproof`
- [x] 8 个提前 `check-sat` 模板已定点修复，全库 early-check-sat = 0（未全量重跑预处理）
- [x] 4 个 Tip 语法错误源文件已改正；源 / 模板 / 副本均通过
- [x] 上述 8+4 相关文件均通过 cvc5 与 Vampire 语法检查
- [x] `list_return_2` 修复后模板短时归纳配置下 `unsat`
- [x] 候选引理求解前 cvc5 `--parse-only` / 类型检查：失败记 `parse_error`/`type_error`（`illformed_lemmas`），不写入数学 `invalid`；同 attempt 经 screen-retry 反馈生成器；仅通过后进入 validity / portfolio
- [ ] （后续）proof / validity / usefulness / harvest 共用结构化 solver-input builder（不仅依赖预处理模板）

---

## 5. 相关路径速查

| 角色 | 路径 |
|---|---|
| 预处理实现 | `preprocessed.py` |
| 原始 AutoProof | `benchmarks/smtlib2/autoproof/standard/*.smt2` |
| 运行用模板 | `benchmarks/preprocessed/autoproof/standard/*/template.smt2` |
| 审计报告 | `docs/v5_nohd_noadv_failure_audit_20260927.md` |
