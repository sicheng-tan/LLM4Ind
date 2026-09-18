# prompts_ours → prompts_ours_compact（对照，修订版）

路径：`prompts_ours_compact/`。`user_prompt.txt` 与原版相同。

本修订按反馈：**保留原 CoT 思维过程 + 各留一组重要示例**；仍删掉 Input 长教程与重复 Requirements。

实验切换：`--strategy-mode default_simple`（别名 `ours_simple` / `simple`）→ `folder_path=./prompts_ours_compact`，模板名与 `default` 相同。

## 体积（约）

| 文件 | 原版词数 | 精简词数 | 约减 |
|------|----------|----------|------|
| equational `system_prompt.txt` | ~1343 | ~521 | ~61% |
| term_rewrite `system_prompt.txt` | ~1350 | ~505 | ~63% |

## 相对原版：删 / 留

| 区块 | 原版 | 精简版 |
|------|------|--------|
| Role | 长铺陈 | 短 Role |
| Input 教程 | 三段 + 多段 SMT 逐句讲解 | **一段短 SMT 结构示例**（equational: Nat/plus；term_rewrite: Pow2） |
| **Chain of thoughts** | 完整条目 + 例 | **完整条目保留**；例各留关键子集（见下） |
| Output 骨架 | equational 有 `; The prove goal is :` 等 | **保留**（equational）；term_rewrite 仍为 XML |
| Requirements | 长列表 + 多 Example + 与 Output 重复 | 合并为 **Rules**；禁止抄 goal/祖先保留一条 |

## 相对上一版「极简 compact」：加回了什么

| 加回 | equational | term_rewrite |
|------|------------|--------------|
| CoT 全文结构 | identify → simplify → base → IH step → rewrite simplify | pattern rewrite → restore bridges → subterm → strengthen → def facts |
| 关键例 | IH `(P (succ n))`；**qreva** 一般化；**A2 + plus 交换律** 卡点 | **Pow2/div pattern→p**；restore 两条桥；**Pow2 i** 子项改写；前提加强 / Q 加强（短述） |
| Output CoT 模板 | `; Inductive proof` / `; Equational reasoning` 骨架 | XML（原版即如此） |
| Input 小例 | Nat + plus + negated goal | Pow2 + negated div goal |

## 仍删（相对原版）

- Lst 第二段 datatype 长讲解；plus 三行 assert 的自然语言复述
- equational Requirements 里 Example1–3 长展开（规则一句代替）
- term_rewrite 里 **同一 Pow2 目标重复 3–4 遍** 的 strengthen 长例（CoT 条目保留，例只留主 rewrite + 一条 subterm + 策略短句）
- 「You are good at extracting…」等套话

## 风险

- 比极简版更长，但仍明显短于原版。
- 若还掉点，优先把原版第二个 Pow2 strengthen 长例加回 term_rewrite，而不是恢复整段 Input 教程。
