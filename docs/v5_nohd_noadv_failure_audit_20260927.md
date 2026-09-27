
## 1. 范围与结论

审计目录：\`ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink\`。读取全部4份结果CSV、95个失败题的根目标、候选记录、已证引理库、运行/提示日志，以及284份子节点失败记录；对照M2的同题成功库与过程。这里只分析当前目录实际运行的686题，不将目录名“706”误作分母，也不把LLM的invalid判断当作已确认错误题。未根据该判断擅自删题。

本次仅新增本文档，保留用户所有已有代码修改，不改实验结果。本文不是新一轮完整消融实验。短验证使用本地cvc5，每次3秒内部上限、最多6秒进程等待，在内存中构造输入；仍以solver输出unsat为成功标准，timeout/空输出均不算成功。已证库按实验记录使用，未重新独立审计整个库的证明来源。

最重要的结论：**首先修输入与失败状态的真实性，其次修证明经验的使用方式，再增强生成。不能把当前所有失败都归因于LLM hint不够聪明。**

| 数据集 | v5成功/总数 | M2成功 | v5新增成功 | v5回退 |
|---|---:|---:|---:|---:|
| AutoProof | 76/141 | 75 | 2 | 1 |
| DTT | 150/158 | 149 | 4 | 3 |
| ind-ben | 138/148 | 139 | 2 | 3 |
| vmcai15-dt | 227/239 | 228 | 4 | 5 |
| 合计 | 591/686 | 591 | 12 | 12 |

### 已经做过短验证的恢复路径

| 任务 | 日志中的真实问题 | 本次只读验证 | 能主张什么 |
|---|---|---|---|
| AutoProof list_return_2 | 唯一check-sat在目标之前 | 移到末尾后，不加引理，原目标在归纳配置下unsat | 已有可复现的输入修复案例 |
| AutoProof list_Select | 同样未查询目标；正确辅助桥已生成却未真正评估 | map2 lam(select3 x ys)=map2 lam ys独立unsat；将其加入规范输入后根目标unsat | 已有可验证的两段恢复证明链 |
| DTT goal47 | nmax交换有非负前提，但缺height非负 | height≥0独立unsat；与v5已证库合并后根目标unsat | 前提闭包模块有直接证据 |
| DTT queue-goal6 | 缺len非负和plus后继桥 | 两条辅助事实分别unsat，但加入后根目标3秒仍超时 | 只有辅助链改善，不能记根目标恢复 |
| vmcai BST-goal5 | 缺leq传递，且被LLM否定 | 传递桥3秒未证成；一次根查询因exit位置没有产生有效判定，未计成功 | 仅有M2成功链支持，不声称本次验证恢复 |

前两题属于输入规范化修复，不应包装成LLM feedback的算法贡献。正式评估应对baseline和新方法一致修复并重跑。其余7个提前check-sat题的原目标3秒规范化测试均未证成；不能据此承诺全部8题恢复。以上结果未回写CSV，所以正式成绩仍是591/686、AutoProof76/141。

## 2. 实现层优先级：先处理能破坏分析依据的问题

### P0：实际SMT查询没有包含目标（8题）

8题全部失败：list_Select、list_return_2、sort_HSortIsSort、sort_MSortBUCount、sort_MSortBUIsSort、sort_TSortCount、sort_TSortIsSort、tree_Flatten1List。

它们的template.smt2都只有一次check-sat，位置在“functions declarations end”之前，目标assert在后面；保存的harvest/with_lemmas文件继承了这个布局。当前cvc5_runner把文件直接交给求解器，没有把查询重组到目标之后。因此许多超时是在检查递归背景理论的可满足性，而不是尝试证明目标。list_return_2的append nil辅助目标就是直接证据。

**修法**：统一的solver-input builder按顶层S-expression重建单查询文件：声明/定义、背景公理、允许使用的已证库、候选假设（只在usefulness查询中）、负目标、最后且唯一的check-sat。删除/重定位exit、旧查询和诊断命令。对proof/validity/usefulness/harvest/counterexample所有入口共用，不只修根模板。若任务真是增量脚本，必须显式拒绝或走独立模式，不能随意合并scope。

相关实现：[cvc5_runner.py:616](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/cvc5_runner.py:616)、[cvc5_runner.py:825](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/cvc5_runner.py:825)。[preprocessed.py:49](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/preprocessed.py:49) 的块状态解析也值得核查：单行声明/公理后未立即清理current_block时，后面的check-sat可能被归入functions；本报告确认了产物和调用路径，未将该预处理函数擅自认定为本次运行唯一来源。

验收：每次调用保存规范化输入hash；检查负目标在查询之前；一份输入恰好一个结果；异常查询数量直接报input_error，不进入LLM数学repair。

### P0：解析/类型错被当作unknown，静态筛选漏完全未声明符号

对95题**保留下来的根级template_with_lemmas.smt2**逐个运行cvc5 --parse-only，7题解析失败：

- relaxedprefix_correct：未转义保留字as被用作变量。
- sort_MSortBU2Count、sort_QSortCount：plus未声明。
- sort_MSortBUCount：+_nat未声明。
- sort_MSortTDCount、sort_NMSortTDCount、sort_NMSortTDIsSort：Nat类型值被送入内建算术+。

这是“最后保留文件”的下界，不能视作所有历史轮次的错误比例。加上上面的8题，重叠1题，共14个AutoProof失败题存在已证实的查询/编译障碍；这不等于修后一定多成功14题。

[lemma_gates.py:567](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/lemma_gates.py:567) 返回的是 used∩declared−axiomatized，故只抓“已声明但无定义”，漏完全未声明函数，也不检查sort、自由变量和保留字。[cvc5_runner.py:703](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/cvc5_runner.py:703) 的输出解析将未识别结果归unknown，没有利用这些Parse Error做repair。

**修法**：候选先做只解析/类型检查；保留原始stderr和returncode，返回syntax_error/type_error/undeclared_symbol；同一generation attempt内修复，不消耗数学搜索分支，也不写入数学invalid。提示中附真实签名，例如count:Int×list→Nat；没有Nat加法就不能建议Int的+。优先生成现有语言能表达的条件/后继关系；若另加辅助定义，必须是单独审计的保守定义扩展，绝不能为了引理随意加入新公理。

### P1：LLM“不可证”硬升级为invalid，并沿父子节点传播

95个失败题的284份子节点记录中，有155个node_outcome由LLM标invalid：104个source=llm，51个source=llm_final，涉及54题。这是来源统计，**不代表155个判断全错**；但以下错误有具体公式/已证事实支持：

- regexp_RecPlus / PlusCommutative / PlusAssociative：把Plus构造子结构不同当作recognise语义不等。相同实验的PlusIdempotent成功库恰好含一般recognise/plus分配桥。
- crafted_rotate/5：称rotateLeft缺“左子树为node”情况；实际定义按右子树Nil/node已经完整覆盖。
- rotate_snoc：给出的y单元素“反例”把rotate一步算成了原表，计算错误。
- weird_nat_mul3_comm13：解释与库里已经证出的mul3 Z y z=Z直接冲突。
- BST-goal5：说less传递不成立，而M2已证该桥。
- isa/goal74：一种证明路线使用无定义plus，不说明len(rev xs)=len xs本身为假。

代码：[Mate_new.py:3203](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/Mate_new.py:3203)、[lemma_gates.py:543](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/lemma_gates.py:543)、[lemma_gates.py:291](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/lemma_gates.py:291)。最终诊断还使用“INVALID or CANNOT be verified；do not weaken”，混合了不同证据等级。

**修法**：拆成refuted_verified、ill_formed、unproved、cycle/redundant、llm_suspected_false。只有经可信验证的反例/矛盾证据可以禁止数学候选；timeout、找不到证明和LLM猜测只能影响优先级。子引理失败不能推出父目标为假。模型解释中的具体反例需回放到当前理论；unknown时打印的模型也不能自动升级成有效反例。对“无需重复当前目标”的限制继续保留，但不要写成数学invalid。

这不同于“关闭所有反例反馈”：保留真正反驳，降低未经验证的否定的权限。

## 3. 算法层：建议的小模块与具体收益场景

| 模块 | 输入与触发 | 输出/动作 | 日志支持的问题 | 实现难度 |
|---|---|---|---|---|
| 类型化编译repair | 新候选无法解析或sort不对 | 返回精确错误、函数签名，在本轮修复 | 7个实测解析错题、heap12、rotate/1 | 低 |
| 前提闭包 | 已证引理的前提不能由当前上下文实例化满足 | 生成待证guard事实，而非仅重复结论 | height/mirror、queue6、DTT heap、last/drop | 低—中 |
| 分离局部证明价值和根有用性 | usefulness未成功，但候选有合法形状且补足已知依赖 | 在小预算内独立证明一条基础桥，形成library增长 | bin_times、bin_plus_assoc、BubSortCount、0树排序题 | 中 |
| 轻量proof-frontier | 有真实证明进度但同一缺口重复出现 | 保留1—3个活动缺口及已证前提，库增长时只重试受影响节点 | mul3_same、MSortBU2IsSort、heap、rotate/6、qfac | 中 |
| 可检查的归纳步模式 | 候选是祖先性质在更小递归参数的应用 | 独立构造base/step验证与合法IH，不把祖先当全局事实 | recognize/plus、bin_plus、sorted-insort、递归旋转 | 中—高 |
| 观察层修订 | 数据结构等式被反驳，但目标只比较其观察值 | 保留recognise/count/flatten/size上下文，改为较弱语义桥 | 正则10题、排序Count、树旋转 | 中 |
| 已证代数规范化 | AC/单位/后继桥已证明 | 程序规范化残差、生成局部组合证明，去掉自反包装 | generated_add_24sym、mul3_same、bin_plus | 中 |
| 经验检索+当前理论重证 | 当前缺口与已存证明片段签名相容 | 返回少量桥及前提/来源，重新验证后才入库 | M2回退12题、正则共享桥、乘法基础 | 中 |

前提闭包例：nmax交换要求两个参数非负，目标把参数实例化成height l和height r。候选应是forall t.height t≥0，而不是“多关注nmax”。这一设计不需要“mirror题模板”，也不靠difficulty绝对阈值。

观察层例：Plus p q和Plus q p作为AST确实不相等，但recognise(Plus p q,s)和recognise(Plus q p,s)可以相等。应记录“被反驳的是哪一层等式”。同理count排序等于count原表不要求排序结果与原表相同。这是由目标上下文推导的通用动作，不按理论族名称定制prompt。

### 轻量proof-frontier：不要再造一棵不受控义务树

一个记录只需：target、已验证的known lemma ids、仍未证的missing candidates、候选类型/域前提、上次尝试所用library_version、父节点usefulness证据、状态与剩余预算。

- 若已经验证“加入C可以关闭父目标”，保留这一**有用性证据**；并不把C当已证明。
- 将C分成已证明K和未证明R，只在R上继续；K增长后尝试直接关闭父目标。
- 若usefulness只是timeout，不标为“C可关闭父目标”；此时只保留低置信候选记录，最多推进一个独立基础桥。
- 新库增长只触发受影响frontier；没有新证据、同规范化目标与同库版本，不再完整重跑。缓存键包含理论、前提scope、目标和library版本，不能只靠公式字符串。
- 近祖先实例不自动标invalid；要么展示合法induction step，验证严格小项，要么仍保持unproved。普通子目标机制无法凭空获得IH。
- 真正需要长度/size/右脊度量的旋转、堆提取、merge/quick/selection sort，先证明下降，再允许良基归纳。简单添加base/step文字不具备证明效力。
- 优先按“已关闭多少实际依赖、是否只剩一个guard/桥、近期是否新增证明”排序，不按跨任务的CONJ或difficulty绝对数值设门槛。

现有代码**已经有**子候选回传、harvest短重试和120秒root_finish_prove，不能当作缺失功能重新提出。此次全体日志有426次harvest_retry，9次成功（其中1次仅在最终失败任务里关闭了局部目标）；57次root_finish_prove，1次成功。95个失败题中有56次最终根重试，40题结束原因为timeout。root_finish_prove只在根attempt耗尽后调用且受剩余预算限制：[Mate_new.py:1602](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/Mate_new.py:1602)。因此改进点是保留收尾时间、在关键库增长后提前组合、限制无进展child扩张，**不是无差别再增加一个长重试**。

## 4. 对LLM hints本身的评价

从真实调用/提示日志而非CSV旧计数重算：

| 统计 | 全部686题 | 失败95题 |
|---|---:|---:|
| 有诊断调用的任务 | 48 | 39 |
| 诊断调用次数 | 158 | 139 |
| REVISE_CANDIDATE | 98 | 86 |
| NEW_DIRECTION | 41 | 36 |
| NO_ACTION | 19 | 17 |
| 实际注入SOLVER HINTS的生成调用 | 247 | 215 |
| 实际被注入的任务 | 47 | 38 |

CSV里的n_prompt_with_hints全为0是统计口径错误：[exp_stats.py:375](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/exp_stats.py:375) 只识别旧repair hints/INITIAL SOLVE，漏SOLVER HINTS。应记录诊断产生→实际消费→生成采用→独立验证→帮助关闭父目标，而非只数hint文本。

当前pool非空且library增长才调用：[feedback_llm_hints.py:240](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/feedback_llm_hints.py:240)。对抑制无依据hint是合理的保守设计，但有三个局限：

1. 38个失败题根本没有义务树，15题没有库；许多重要基础候选从未进入可复活池。不能指望REVISE_CANDIDATE覆盖所有失败。
2. “pool空但库增长”被跳过456次，其中失败任务296次。height非负/关系传递这类前提缺口可能需要新的小桥，不一定来自旧池。只为**可展示的未满足guard**开放窄NEW_DIRECTION，比全面放宽触发更可控。
3. 调用跳过时仍可能消费旧缓存hint；当前注入路径不核对library/候选状态是否已经变化：[lemma_gates.py:1217](//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/lemma_gates.py:1217)。应重新过滤已证/已反驳/与当前目标等价的revive，并对note也检查时效；同一个note不能在库变化后继续声称“缺X”，而X已证。

开启LLM hints会连local-vs-parent反馈一起隐藏，即使NO_ACTION或未调用。保持“nohd不回退HD”的意图可以不变，但“该事实已独立证明/尚未证明”和“父有用性查询结果”属于证据状态，不应随HD一起隐藏。

### 正面证据与副作用必须同时看

- PlusIdempotent：REVISE确实把recognise/step/plus语义候选交回生成器，生成器实际采用；最终库有一般recognise/plus分配和幂等。说明可以指导生成，但中间NEW_DIRECTION也错误建议已存在的eps桥，后期反复引导布尔自反/幂等小事实。成功不等于所有hint都正确。
- isa/goal79：NEW_DIRECTION后生成了正确的less分支插入排序桥；后续REVISE围绕新入库的sorted-cons组装引理选择tail候选，方向有针对性。但仍反复绕回祖先sorted-insort，诊断还提过“不出现于列表即可放到头部”这样的错误建议。
- 新增成功12题中只有2题有hint诊断，其余10题不能作为hint直接贡献；回退12题中有4题没有hint诊断（queue6、height/mirror、rotate/2、mul3acc_comm23），也不能全部归因于hint带偏。单次运行且代码/随机生成等因素未隔离，不能作净因果估计。
- weird_nat_mul3_comm13的“两次循环等于反转”、regexp_Star的Eps无条件吸收，属于note逻辑错误；即使公式继续受solver验证，仍会浪费搜索预算并污染下一轮解释。

**推荐hint收紧，不是加更多advice标签**：每条建议必须附引用的已证lemma ids、一个尚未满足的前提/残差、候选为何不同于上一轮、可立即执行的验证动作。禁止把timeout翻译成“定理是假的”，禁止把伪反例写为事实。复活公式经过当前签名、状态和相同目标过滤；note无证据时退NO_ACTION。第一次生成维持原方法，不自动注入诊断。

## 5. 建议实施与评估顺序

1. **输入可信化**：统一查询、parse/type检查、保存stderr/returncode、区分数学状态；同样修baseline。先复测8个查询错题和7个解析错题。
2. **关闭LLM硬invalid权限**，保留已验证反例。优先回放正则、rotate_snoc、rotate/5、BST-goal5；观察候选是否重新获得独立证明机会。
3. **前提闭包 + 过期hint淘汰**。优先height/mirror、queue6、last/drop、DTT heap；这是比恢复HD或新增理论族advice更小的改动。
4. **frontier与已证库组合调度**。优先mul3_same、rotate/6、MSortBU2IsSort、heap10/13、qfac；记录减少的重复目标/调用与父目标闭合，不仅记录库变大。
5. **独立归纳步/度量归纳支持、观察层语义修订**。这是AutoProof进一步明显提升更可能需要的能力，工程成本高于调prompt。先做结构列表归纳，再做旋转/堆等良基情况。
6. 跨任务经验继承按定义/符号签名和前提检索，每条在当前理论重证；测试任务在线相互传经验需单列设置，防止顺序依赖或把M2同题成功答案当作无泄漏测试输入。M2证明链在本文只是诊断证据。

消融至少分：输入修复基线；+软化invalid；+前提闭包；+frontier；+受控hints。相同总体预算和任务集合，多次运行配对统计成功/回退、关键桥独立证成率、库增长后关闭父目标率，以及提示消费时是否过期。不存在日志足以支持的“预计能提高到90/141”等数值保证。

## 6. 全部95个失败任务逐题分析

每行给出实际过程与下一步；P0=输入/编译先修，P1=有明确缺口或参考成功链，P2=仍需较长数学/归纳能力建设。P1不是成功概率标签。A/T/L/P分别是日志CSV记录的LLM attempts、义务树数、库引理数、成功子目标数，不将其等同于总API次数或证明难度。H=实际生成调用中注入hint的次数。


### AutoProof（65题）
#### standard/bin_distrib — P1

- 日志：A/T/L/P=6/0/1/0; 650.42s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_distrib/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_distrib/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_distrib/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin) (z Bin)) (= (times x (plus y z)) (plus (times x y) (times x z))))))`
- 实际过程：6次生成、0棵树；加法结合/交换及乘法分配候选反复 usefulness timeout，库仅保留双 ZeroAnd 加法展开。 已证库关键片段：(forall ((a Bin) (b Bin)) (= (plus (ZeroAnd a) (ZeroAnd b)) (ZeroAnd (plus a b))))。最近/代表性候选：(forall ((a Bin) (b Bin) (c Bin)) (= (times (plus a b) c) (plus (times a c) (times b c))))；(forall ((x Bin) (y Bin)) (= (times (s x) y) (plus y (times x y))))。
- 根节点筛除记录：(forall ((a Bin) (b Bin)) (= (plus (ZeroAnd a) b) (ZeroAnd (plus a b)))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：先证明携带进位的 plus/s 桥及可闭合的分配律，允许在 usefulness 未成功时单独推进一个基础候选；不能把大分配律反复打包。

#### standard/bin_plus — P1

- 日志：A/T/L/P=14/1/12/0; 1203.04s; timeout；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin)) (= (toNat (plus x y)) (plus2 (toNat x) (toNat y))))))`
- 实际过程：库已有 toNat(s x)=S(toNat x)、双倍换序和 plus2 AC 等12条，仍因 OneAnd 分支转回一般目标而被 LLM 判不可证。 已证库关键片段：(forall ((a Nat) (b Nat) (c Nat)) (= (plus2 (plus2 a b) c) (plus2 a (plus2 b c))))；(forall ((n Nat) (m Nat)) (= (plus2 n m) (plus2 m n)))；另10条。最近/代表性候选：(forall ((p Nat) (q Nat)) (= (plus2 (plus2 p p) (plus2 q q)) (plus2 (plus2 p q) (plus2 p q))))；(forall ((n Nat) (m Nat)) (= (plus2 n (S m)) (S (plus2 n m))))。
- 根节点筛除记录：(forall ((x Bin) (y Bin)) (=> (is-OneAnd x) (= (toNat (plus x y)) (plus2 (toNat x) (toNat y))))) → The conditioned goal (is-OneAnd x => toNat(plus x y) = plus2(toNat x)(toNat y)) cannot be proved; the inductive case for x = OneAnd x' reduces to the general unconditioned distrib…
- 子节点否定记录（来源未必是solver反例）：The goal is not a theorem of the axioms; the prior invalid lemma shows the intended arithmetic identity does not follow, and the given recursive definitions/axioms lack the needed commutativity/associ
- 理想证明路线及改进：对 Bin 构造子分支显式保留合法归纳假设，参数 y 泛化；用已证 toNat/s 与双倍桥闭合进位分支。重点是验证归纳步而非再生成加法包装式。

#### standard/bin_plus_assoc — P1

- 日志：A/T/L/P=6/0/1/0; 733.21s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus_assoc/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus_assoc/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus_assoc/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin) (z Bin)) (= (plus x (plus y z)) (plus (plus x y) z)))))`
- 实际过程：反复提出 plus(s x)y、plus x(s y) 的 successor 桥，但只收集到 plus x One=s x。 已证库关键片段：(forall ((x Bin)) (= (plus x One) (s x)))。最近/代表性候选：(forall ((x Bin) (y Bin)) (= (plus x (s y)) (s (plus x y))))；(forall ((x Bin) (y Bin)) (= (plus (s x) y) (s (plus x y))))。
- 理想证明路线及改进：先对进位桥做独立证明/双参数构造子分解，再重试结合律；保存桥的证明进度，不以根目标60秒不成功判整组无价值。

#### standard/bin_plus_comm — P1

- 日志：A/T/L/P=10/2/1/0; 837.09s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus_comm/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus_comm/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_plus_comm/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin)) (= (plus x y) (plus y x)))))`
- 实际过程：右 One 基例已入库；OneAnd 子目标因为需要一般交换律被判 invalid。 已证库关键片段：(forall ((y Bin)) (= (plus y One) (s y)))。最近/代表性候选：(forall ((x Bin) (y Bin)) (= (plus x (s y)) (s (plus x y))))；(forall ((x Bin) (y Bin)) (= (plus (s x) y) (s (plus x y))))。
- 根节点筛除记录：(forall ((x Bin) (y Bin)) (= (plus (OneAnd x) y) (plus y (OneAnd x)))) → The CURRENT goal is a strict instance of the ancestor commutativity A0; any inductive proof reduces to full commutativity `(plus z y) = (plus y z)` for arbitrary z, y, which is ex…
- 子节点否定记录（来源未必是solver反例）：The CURRENT goal is a strict instance of the ancestor commutativity A0; any inductive proof reduces to full commutativity `(plus z y) = (plus y z)` for arbitrary z, y, which is exactly the disallowed
- 理想证明路线及改进：区分合法较小参数归纳假设和无条件祖先循环；构造子分解 plus 的双方，先关掉 LLM 的硬否定。

#### standard/bin_times — P1

- 日志：A/T/L/P=6/0/2/0; 647.22s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin)) (= (toNat (times x y)) (mult (toNat x) (toNat y))))))`
- 实际过程：生成过正确方向的 toNat(plus)=plus2(toNat,toNat) 与 mult 分配，但库只有 plus2 交换/右零。 已证库关键片段：(forall ((a Nat) (b Nat)) (= (plus2 a b) (plus2 b a)))；(forall ((n Nat)) (= (plus2 n Z) n))。最近/代表性候选：(forall ((x Bin) (y Bin)) (= (toNat (plus x y)) (plus2 (toNat x) (toNat y))))；(forall ((a Nat) (b Nat) (c Nat)) (= (mult (plus2 a b) c) (plus2 (mult a c) (mult b c))))。
- 理想证明路线及改进：先完成二进制加法语义桥，再推进 Nat 乘法分配；把长链拆成共享关键节点，不在每轮重复根候选组合。

#### standard/bin_times_assoc — P1

- 日志：A/T/L/P=6/0/1/0; 714.94s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times_assoc/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times_assoc/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times_assoc/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin) (z Bin)) (= (times x (times y z)) (times (times x y) z)))))`
- 实际过程：库只有 times(ZeroAnd a)b 的定义性事实，分配律换方向反复超时。 已证库关键片段：(forall ((a Bin) (b Bin)) (= (times (ZeroAnd a) b) (ZeroAnd (times a b))))。最近/代表性候选：(forall ((x Bin) (y Bin) (z Bin)) (= (times x (plus y z)) (plus (times x y) (times x z))))；(forall ((x Bin) (y Bin) (z Bin)) (= (times (plus x y) z) (plus (times x z) (times y z))))。
- 理想证明路线及改进：按 times 构造子展开取得实际所需分配方向，先证明双倍/后继乘法桥，再证明分配与结合；不要一次要求所有乘法代数律。

#### standard/bin_times_comm — P1

- 日志：A/T/L/P=13/2/6/1; 1203.30s; timeout；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times_comm/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times_comm/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/bin_times_comm/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Bin) (y Bin)) (= (times x y) (times y x)))))`
- 实际过程：times x(ZeroAnd y) 和右 One 已证；右 OneAnd 乘法桥却以“times不交换”为由记 invalid。 已证库关键片段：(forall ((x Bin) (y Bin)) (= (times x (ZeroAnd y)) (ZeroAnd (times x y))))；(forall ((y Bin)) (= (times y One) y))；另4条。最近/代表性候选：(forall ((x Bin) (y Bin)) (= (times x (ZeroAnd y)) (ZeroAnd (times x y))))；(forall ((x Bin) (y Bin)) (= (times y (OneAnd x)) (plus y (ZeroAnd (times y x)))))。
- 根节点筛除记录：(forall ((x Bin) (y Bin)) (= (times x y) (times y x))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：The goal asserts a commutativity-style identity `times y (OneAnd x) = plus (ZeroAnd (times y x)) y`, but `times` is defined by recursion on its first argument and is not provably commutative; the only
- 理想证明路线及改进：证明右侧 OneAnd 展开，再用左递归归纳；这条桥不应因定义非对称而被否定。

#### standard/int_left_distrib — P2

- 日志：A/T/L/P=6/0/4/0; 657.39s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/int_left_distrib/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/int_left_distrib/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/int_left_distrib/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Z) (y Z) (z Z)) (= (times x (plus2 y z)) (plus2 (times x y) (times x z))))))`
- 实际过程：库已有 absVal(times)、toInteger 乘法与同号加法；没有异号相消关系。 已证库关键片段：(forall ((a Nat) (b Nat)) (= (plus a b) (plus b a)))；(forall ((x Z) (y Z)) (= (absVal (times x y)) (mult (absVal x) (absVal y))))；另2条。最近/代表性候选：(forall ((s Sign) (a Nat) (b Nat)) (= (toInteger s (plus a b)) (plus2 (toInteger s a) (toInteger s b))))；(forall ((s Sign) (t Sign) (a Nat) (b Nat)) (= (times (toInteger s a) (toInteger t b)) (toInteger (timesSign s t) (mult a b))))。
- 根节点筛除记录：(forall ((x Z) (y Z)) (= (sign (plus2 x y)) (timesSign (sign x) (sign y)))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：按符号和绝对值比较拆分，引入有前提的差值/相消桥。absVal 不是加法同态，已有反驳不能只改变量名再用。

#### standard/list_Select — P0

- 日志：A/T/L/P=6/0/0/0; 782.67s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/list_Select/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/list_Select/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/list_Select/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((xs list2)) (= (map2 lam (select2 xs)) xs))))`
- 实际过程：唯一 check-sat 在目标之前；原日志无法评价真实目标。候选还曾把 list/list2 混用、把固定 lam 泛化成任意 f。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((f fun1) (x sk_t) (ys list)) (= (map2 f (select3 x ys)) (map2 f ys)))；(forall ((h sk_t) (t list2)) (= (map2 lam (select3 h (select2 t))) (map2 lam (select2 t))))。
- 理想证明路线及改进：先修查询。日志已有的正确桥 map2 lam(select3 x ys)=map2 lam ys 在本次3秒短验证中独立unsat；在原理论加入此已验证桥后，根目标也unsat。因此是已验证的两段恢复链，而不是待验证猜想。

#### standard/list_return_2 — P0

- 日志：A/T/L/P=6/0/0/0; 670.00s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/list_return_2/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/list_return_2/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/list_return_2/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((xs list)) (= (bind xs lam) xs))))`
- 实际过程：唯一 check-sat 在目标前；连 append nil 的平凡引理都无法收集。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((xs list)) (or (= xs nil) (is-cons xs)))；(forall ((xs list)) (= (bind xs lam) (append (return (head xs)) (bind (tail xs) lam))))。
- 理想证明路线及改进：修查询即可优先重测；内存规范化后，原目标在3秒 cvc5_inductive 配置直接 unsat，这是本次唯一已经实际验证的根目标恢复。

#### standard/nicomachus_theorem — P2

- 日志：A/T/L/P=6/0/4/0; 791.37s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/nicomachus_theorem/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/nicomachus_theorem/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/nicomachus_theorem/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((n Nat)) (= (cubes n) (mult (sum n) (sum n))))))`
- 实际过程：生成过平方展开、2*sum=n(n+1)方向，但库仅有4条一步算术式。 已证库关键片段：(forall ((n Nat) (m Nat)) (= (plus n (S m)) (S (plus n m))))；(forall ((n Nat) (m Nat)) (= (mult (S n) m) (plus m (mult n m))))；另2条。最近/代表性候选：(forall ((n Nat)) (= (mult (sum (S n)) (sum (S n))) (plus (mult (sum n) (sum n)) (plus (mult (sum n) (S n)) (plus (mult (S n) (sum n)) (mult (S n) (S n)))))))；(forall ((n Nat)) (= (mult (S n) (S n)) (plus (S n) (mult n (S n)))))。
- 根节点筛除记录：(forall ((n Nat)) (= (mult (S n) (S n)) (S (plus (S n) (mult n (S n)))))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：先完成加法AC与乘法分配、三角数双倍关系，再给平方增量局部桥；不要单靠重复 cubes 主等式。vmcai 同类成功链可作独立重证的经验参考。

#### standard/regexp_Deeps — P1

- 日志：A/T/L/P=8/1/3/0; 618.30s; attempts_exhausted；失败节点 1。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Deeps/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Deeps/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Deeps/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (s list)) (= (recognise (Star p) s) (recognise (Star (deeps p)) s)))))`
- 实际过程：库只有 eps(step p a) 与 deeps 的局部性质；关键 residual-language 等价被以“deeps去掉Eps”否定。 已证库关键片段：(forall ((p R) (a A)) (= (eps (step p a)) (eps (step (deeps p) a))))；(forall ((p R)) (= (deeps (Star p)) (deeps p)))；另1条。最近/代表性候选：(forall ((p R) (a A) (s list)) (= (recognise (Star (seq (step p a) (Star p))) s) (recognise (Star (seq (step (deeps p) a) (Star (deeps p)))) s)))；(forall ((p R) (a A)) (= (eps (seq (step p a) (Star p))) (eps (seq (step (deeps p) a) (Star (deeps p))))))。
- 根节点筛除记录：(forall ((p R)) (= (eps p) (eps (deeps p)))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal equates recognition of `seq (step p a) (Star p)` with the deeps-transformed version. Since `deeps` removes Eps nodes (e.g. `deeps(Eps)=Nil`), it changes the language recognized; the invalid l
- 理想证明路线及改进：反馈应保留 recognise 上下文：deeps可能改变空串，但目标是 Star；先证明非空语言/导数在适当上下文等价，再处理 Star，不要求正则AST相等。

#### standard/regexp_PlusAssociative — P1

- 日志：A/T/L/P=10/3/3/1; 562.96s; attempts_exhausted；失败节点 1。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_PlusAssociative/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_PlusAssociative/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_PlusAssociative/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (q R) (r R) (s list)) (= (recognise (Plus p (Plus q r)) s) (recognise (Plus (Plus p q) r) s)))))`
- 实际过程：recognise 下的 plus 结合律被以 Plus 构造子不结合而判 invalid；库只有 step/eps展开。 已证库关键片段：(forall ((a A) (p R) (q R) (r R)) (= (step (Plus (Plus p q) r) a) (plus (step (Plus p q) a) (step r a))))；(forall ((a A) (p R) (q R) (r R)) (= (step (Plus p (Plus q r)) a) (plus (step p a) (step (Plus q r) a))))；另1条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x R) (y R) (z R)) (= (plus x (plus y z)) (plus (plus x y) z))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal reduces to associativity of `plus` on `(step p a),(step q a),(step r a)`, but `plus` is not associative under its axioms (e.g. with all three equal to `Eps`, LHS `= (Plus (Plus Eps Eps) Eps)`
- 理想证明路线及改进：先证 recognise(plus p q)s=recognise p s∨recognise q s，再用布尔结合律；结构不相等不构成语义不等的反例。

#### standard/regexp_PlusCommutative — P1

- 日志：A/T/L/P=24/8/10/0; 1034.58s; attempts_exhausted; H=4；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_PlusCommutative/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_PlusCommutative/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_PlusCommutative/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (q R) (s list)) (= (recognise (Plus p q) s) (recognise (Plus q p) s)))))`
- 实际过程：24次生成、8棵树、10条库；多条 recognise 交换引理被以 ordered Plus 结构为由否定。 已证库关键片段：(forall ((p R) (q R) (a A)) (= (step (Plus p q) a) (plus (step p a) (step q a))))；(forall ((p R) (q R)) (= (eps (Plus p q)) (or (eps p) (eps q))))；另8条。最近/代表性候选：(forall ((r1 R) (r2 R) (a A)) (= (step (plus r1 r2) a) (plus (step r1 a) (step r2 a))))；(forall ((p R) (q R)) (= (eps (Plus p q)) (or (eps q) (eps p))))。
- 根节点筛除记录：(forall ((r1 R) (r2 R) (s list)) (= (recognise (plus r1 r2) s) (recognise (plus r2 r1) s))) → The goal asserts that recognise is invariant under swapping the two arguments of plus, but plus is defined as an ordered sum (Plus x y), and step/eps on Plus are order-sensitive b…
- 子节点否定记录（来源未必是solver反例）：The goal requires plus to be commutative, but plus is defined by an ite returning Plus x y (an asymmetric constructor), so plus (step p a) (step q a) ≠ plus (step q a) (step p a) in general; hence rec
- 理想证明路线及改进：与上一题共用语言并集语义桥；不要堆长度0/1特例，使用对输入串归纳且对两个 residual regex 全称泛化。

#### standard/regexp_RecPlus — P1

- 日志：A/T/L/P=19/6/10/2; 1203.57s; timeout; H=8；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecPlus/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecPlus/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecPlus/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (q R) (s list)) (= (recognise (Plus p q) s) (or (recognise p s) (recognise q s))))))`
- 实际过程：10条库已含 step/plus 分配、eps/plus 分配、Nil语言等；目标语义桥仍被 LLM说成 false。 已证库关键片段：(forall ((x R) (y R) (a A)) (= (step (plus x y) a) (plus (step x a) (step y a))))；(forall ((x R) (y R)) (= (eps (plus x y)) (or (eps x) (eps y))))；另8条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x R) (y R) (s list)) (= (recognise (plus x y) s) (or (recognise x s) (recognise y s)))) → The goal is false: `plus x y` for non-Nil/non-Eps arguments constructs `Plus x y`, and `recognise` on a `Plus` term steps through both branches rather than being equivalent to the…
- 子节点否定记录（来源未必是solver反例）：The goal is false. `recognise (Plus p q) s` for nonempty `s` is not equivalent to `or (recognise p s) (recognise q s)`: stepping a `Plus` node yields `plus (step p a) (step q a)`, and the plus-splitti
- 理想证明路线及改进：同轮成功的 PlusIdempotent 已证明该一般桥，是强交叉证据；分离 LLM怀疑与 verified refutation，并执行串归纳的基步/归纳步。

#### standard/regexp_RecSeq — P1

- 日志：A/T/L/P=13/2/3/0; 1203.26s; timeout；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecSeq/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecSeq/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecSeq/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (q R) (s list2)) (= (recognise (Seq p q) s) (recognisePair p q (split s))))))`
- 实际过程：已有 seq/Seq识别桥；曾生成 recognisePair/consfst 与 split 的递推方向，也产生漏 eps 分支的错误公式。 已证库关键片段：(forall ((x R) (y R) (t list2)) (= (recognise (seq x y) t) (recognise (Seq x y) t)))；(forall ((p R) (q R) (a A) (t list2)) (= (recognise (step (Seq p q) a) t) (recognise (plus (seq (step p a) q) (seq (epsR p) (step q a))) t)))；另1条。最近/代表性候选：(forall ((p R) (q R) (a A) (t list2)) (= (recognise (Seq p q) (cons2 a t)) (or (recognise (Seq (step p a) q) t) (and (eps p) (recognise q (cons2 a t))))))；(forall ((p R) (q R) (a A) (t list2)) (= (recognisePair p q (split (cons2 a t))) (or (and (eps p) (recognise q (cons2 a t))) (recognisePair (step p a) q (split t)))))。
- 根节点筛除记录：(forall ((p R) (q R) (a A) (t list2)) (= (recognisePair p q (split (cons2 a t))) (or (and (recognise p (cons2 a nil2)) (recognise… → ...
- 子节点否定记录（来源未必是solver反例）：`recognise` has no axiom decomposing `plus`/`Plus` into a disjunction of `recognise` calls; the goal requires `recognise (plus ...) t = (recognise ... t) or (recognise ... t)`, which is not derivable
- 理想证明路线及改进：拆成并集语义、空前缀贡献和 consfst 导数三步；反例修复应补 eps(p)∧recognise(q,cons a t)，不能把所有 seq/split 路线淘汰。

#### standard/regexp_RecStar — P1

- 日志：A/T/L/P=13/9/6/0; 1201.51s; timeout；失败节点 5。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecStar/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecStar/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_RecStar/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (s list)) (= (recognise (Star p) s) (or (null s) (recognise (Seq p (Star p)) s))))))`
- 实际过程：已有plus/Nil单位和step/eps桥，通用 recognise/plus分配因“需要归纳”记 invalid。 已证库关键片段：(forall ((r R) (s list)) (= (recognise (plus r Nil) s) (recognise r s)))；(forall ((r R) (s list)) (= (recognise (plus Nil r) s) (recognise r s)))；另4条。最近/代表性候选：(forall ((r R) (s list)) (= (recognise (plus r Nil) s) (recognise r s)))；(forall ((r R) (s list)) (= (recognise (plus Nil r) s) (recognise r s)))。
- 根节点筛除记录：(forall ((r1 R) (r2 R) (s list)) (= (recognise (plus r1 r2) s) (or (recognise r1 s) (recognise r2 s)))) → The current goal `recognise (plus r1 r2) s = or (recognise r1 s) (recognise r2 s)` is not derivable from a strictly simpler non-circular helper; proving it requires the induction …
- 子节点否定记录（来源未必是solver反例）：The proof requires the Plus-recognition lemma `(forall ((r1 R) (r2 R) (s list)) (= (recognise (Plus r1 r2) s) (or (recognise r1 s) (recognise r2 s))))`, which is the already-listed ancestor A1. The CU
- 理想证明路线及改进：先闭合并集语义，然后在非空串分支对比 Star 和 Seq(p,Star p) 的导数；合法归纳依赖不是 false 证据。

#### standard/regexp_Reverse — P2

- 日志：A/T/L/P=9/1/1/0; 520.76s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Reverse/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Reverse/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Reverse/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((r R) (s list)) (= (recognise (rev r) s) (recognise r (reverse s))))))`
- 实际过程：多次提出 recognise r(append u[a])=recognise(step r a)u，混淆了从左读取与从右读取。 已证库关键片段：(forall ((r R)) (= (eps (rev r)) (eps r)))。最近/代表性候选：(forall ((r R)) (= (eps (rev r)) (eps r)))；(forall ((r R) (u list) (a A)) (= (recognise r (append u (cons a nil))) (recognise (step r a) u)))。
- 根节点筛除记录：(forall ((r R) (a A)) (= (rev (step (rev r) a)) (step r a))) → The goal is not a theorem. Counterexample: let r = Seq(Atom(X), Atom(Y)) and a = X. Then rev(r) = Seq(Atom(Y), Atom(X)), step(rev(r), X) = Nil (since step(Atom(Y),X)=Nil and epsR(…
- 子节点否定记录（来源未必是solver反例）：The goal is not a theorem. Counterexample: let r = Seq(Atom(X), Atom(Y)) and a = X. Then rev(r) = Seq(Atom(Y), Atom(X)), step(rev(r), X) = Nil (since step(Atom(Y),X)=Nil and epsR(Atom(Y))=Nil, giving
- 理想证明路线及改进：采用带 rev 的右导数/后缀语义桥，或先建立 Seq 的串分割语义再证明反转；该错误方向可由两字符有序串检验，不应继续只调整括号。

#### standard/regexp_SeqAssociative — P2

- 日志：A/T/L/P=6/0/4/0; 827.94s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_SeqAssociative/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_SeqAssociative/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_SeqAssociative/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (q R) (r R) (s list)) (= (recognise (Seq p (Seq q r)) s) (recognise (Seq (Seq p q) r) s)))))`
- 实际过程：6次生成0棵树；库有seq/Seq和epsR语义，但三重连接结合仍在大式之间循环。 已证库关键片段：(forall ((x R) (y R) (a A)) (= (step (Seq x y) a) (plus (seq (step x a) y) (seq (epsR x) (step y a)))))；(forall ((x R) (y R) (s list)) (= (recognise (seq x y) s) (recognise (Seq x y) s)))；另2条。最近/代表性候选：(forall ((p R) (q R) (r R)) (= (eps (Seq p (Seq q r))) (eps (Seq (Seq p q) r))))；(forall ((x R) (y R) (s list)) (= (recognise (seq (epsR x) y) s) (and (eps x) (recognise y s))))。
- 根节点筛除记录：(forall ((x R) (y R) (a A) (t list)) (= (recognise (seq (step x a) y) t) (or (recognise (seq (epsR x) (step y a)) t) (recognise (… → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：分解为并集语义、seq上下文下的分配和导数归纳闭合；或走串分割结合律，明确选择一条路线并保留其已证前提。

#### standard/regexp_SeqDistrPlus — P1

- 日志：A/T/L/P=8/1/6/1; 527.16s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_SeqDistrPlus/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_SeqDistrPlus/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_SeqDistrPlus/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (q R) (r R) (s list)) (= (recognise (Seq p (Plus q r)) s) (recognise (Plus (Seq p q) (Seq p r)) s)))))`
- 实际过程：6条库含eps基例与条件seq分配；多个 step或seq 的AST等式被真正反驳。 已证库关键片段：(forall ((q R) (r R) (a A)) (= (step (Plus q r) a) (plus (step q a) (step r a))))；(forall ((x R)) (= (eps x) (eps (epsR x))))；另4条。最近/代表性候选：(forall ((p R) (q R) (r R)) (= (eps (Seq p (Plus q r))) (eps (Plus (Seq p q) (Seq p r)))))；(forall ((p R) (q R) (r R) (a A)) (= (seq (epsR p) (plus (step q a) (step r a))) (plus (seq (epsR p) (step q a)) (seq (epsR p) (step r a)))))。
- 根节点筛除记录：(forall ((p R) (q R) (r R) (a A)) (= (step (Seq p (Plus q r)) a) (step (Plus (Seq p q) (Seq p r)) a))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal requires distributing seq (step p a) over (Plus q r), i.e. seq x (Plus q r) = plus (seq x q) (seq x r). No such axiom exists for seq, and the previously proposed distribution lemma (invalid l
- 理想证明路线及改进：将结构等式降为 recognise(...,s) 等价，这是有依据的投影层修订；保留已证eps基例，再生成语言层的归纳步桥。

#### standard/regexp_Star — P1

- 日志：A/T/L/P=22/12/11/2; 1200.24s; timeout; H=5；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Star/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Star/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/regexp_Star/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p R) (s list)) (= (recognise (Star p) s) (recognise (Plus Eps (Seq p (Star p))) s)))))`
- 实际过程：11条库中仍缺语义幂等；hint声称 unconditional Plus 幂等 invalid，甚至声称 Eps可无条件被Seq吸收。 已证库关键片段：(forall ((p R) (s list)) (= (recognise (plus Eps (Seq p (Star p))) s) (recognise (Plus Eps (Seq p (Star p))) s)))；(forall ((x R)) (= (or (eps x) (eps x)) (eps x)))；另9条。最近/代表性候选：(forall ((p R) (a A)) (= (step (Seq p (Star p)) a) (plus (seq (step p a) (Star p)) (seq (epsR p) (step (Star p) a)))))；(forall ((p R) (a A)) (= (step (plus Eps (Seq p (Star p))) a) (plus (step Eps a) (step (Seq p (Star p)) a))))。
- 根节点筛除记录：(forall ((p R) (s list)) (= (recognise (Plus (Star p) (Star p)) s) (recognise (Star p) s))) → The current goal asserts idempotence of the union constructor under `recognise` (`recognise (Plus p p) s) = recognise p s`), but `Plus` is a free datatype constructor with no axio…
- 子节点否定记录（来源未必是solver反例）：The goal asserts idempotence of union (`recognise (plus r r) s = recognise r s`), but the axioms only define `recognise` via `step`/`eps`; `step (Plus r r) a = plus (step r a) (step r a)` (lib_3), and
- 已生成的solver hint：The goal reduces to showing that the union constructor is absorbed: recognise (Plus Eps (Seq p (Star p))) s = recognise (Seq p (Star p)) s, since recognise (plus...) = recognise (Plus...) and the Plus case of step yields a plus of step results. The library already give…
- 理想证明路线及改进：对照同轮 PlusIdempotent 的成功桥；空串情况下 Eps吸收说法不成立。诊断必须列 base/step 适用条件，不能信任从错误 invalid 列继承的结论。

#### standard/relaxedprefix_correct — P0

- 日志：A/T/L/P=5/0/0/0; 593.37s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/relaxedprefix_correct/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/relaxedprefix_correct/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/relaxedprefix_correct/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((xs list2) (ys list2)) (= (isRelaxedPrefix xs ys) (spec xs ys)))))`
- 实际过程：五组候选均unknown；末轮输入实测解析失败，原因是将SMT保留字 as 用作未转义变量。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((a It) (as list2) (ys list2)) (= (spec2 ys (cons (cons2 a as) (removeOne (cons2 a as)))) (cons3 (isPrefix as ys) (spec2 ys (cons as (removeOne as))))))；(forall ((xs list2) (ys list2)) (= (or2 (spec2 ys (cons xs (removeOne xs)))) (isRelaxedPrefix xs ys)))。
- 理想证明路线及改进：先语法修复再评价数学路线；随后证明 removeOne/cons 与 spec2映射、or2折叠的递推关系，保持删除零次/一次的分支一致。

#### standard/rotate_mod — P2

- 日志：A/T/L/P=29/11/9/1; 1203.21s; timeout; H=4；失败节点 5。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_mod/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_mod/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_mod/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((n Nat) (xs List2)) (= (rotate n xs) (append (drop (mod2 n (length xs)) xs) (take (mod2 n (length xs)) xs))))))`
- 实际过程：已有单步rotate和length保持；无界 rotate k xs=drop/take 分解是错误候选，尚缺模周期闭合。 已证库关键片段：(forall ((n Nat) (xs List2)) (= (rotate (S n) xs) (rotate n (rotate (S Z) xs))))；(forall ((xs List2)) (= (append xs Nil) xs))；另7条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((k Nat) (xs List2)) (= (rotate k xs) (append (drop k xs) (take k xs)))) → The goal is false: rotate is defined by appending the head repeatedly to the tail, so rotate k xs generally moves the first k elements to the end, whereas append (drop k xs) (take…
- 子节点否定记录（来源未必是solver反例）：The goal is false. Counterexample: with xs = [a,b] (length 2) and n = S Z (1), mod2 1 2 = 1, so LHS = rotate 1 [a,b] = [b,a], while RHS = rotate 1 (rotate 1 [a,b]) = rotate 1 [b,a] = [a,b]. Since [b,a
- 理想证明路线及改进：分三块：k≤length 的切分等式、旋转完整周期、mod递减/余数边界；保留 xs=Nil 特例。需要度量归纳，不是同式再加外层rotate。

#### standard/rotate_snoc — P1

- 日志：A/T/L/P=18/11/7/2; 1204.16s; timeout; H=3；失败节点 12。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_snoc/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_snoc/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_snoc/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((xs list)) (= (rotate (length xs) xs) xs))))`
- 实际过程：候选 rotate(length y)(snoc x y)=cons x y 被 LLM用错误计算反驳；库反而积累同义展开和自反式。 已证库关键片段：(forall ((x sk_a) (y sk_a) (z list)) (= (snoc x (cons y z)) (cons y (snoc x z))))；(forall ((x sk_a) (y list)) (= (length (snoc x y)) (S (length y))))；另5条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x sk_a) (y list)) (= (rotate (length y) (snoc x y)) (cons x y))) → The goal is false; e.g. y = (cons h nil) with x ≠ h gives rotate (length y) (snoc x y) = (cons h (cons x nil)) ≠ (cons x (cons h nil)) = (cons x y). The inductive case requires co…
- 子节点否定记录（来源未必是solver反例）：the goal asserts that snoc commutes in its two element arguments, but the defining axiom (snoc x nil) = (cons x nil) forces snoc x (snoc y nil) = (cons y (cons x nil)) while snoc y (snoc x nil) = (con
- 理想证明路线及改进：该候选正是有用的累积泛化；先核验所谓反例，证明 snoc/rotate 的相容递推，再回收根目标。不能用“需要归纳”代替反驳。

#### standard/rotate_structural_mod — P2

- 日志：A/T/L/P=15/11/4/0; 1202.82s; timeout; H=3；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_structural_mod/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_structural_mod/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/rotate_structural_mod/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((n Nat) (xs List2)) (= (rotate n xs) (append (drop (mod3 n (length xs)) xs) (take (mod3 n (length xs)) xs))))))`
- 实际过程：库仅4条append代数；hint建议length同态方向合理，但尚未触及mod3循环边界，且可能使用不存在的plus。 已证库关键片段：(forall ((xs List2)) (= (append xs Nil) xs))；(forall ((xs List2) (ys List2) (zs List2)) (= (append (append xs ys) zs) (append xs (append ys zs))))；另2条。最近/代表性候选：(forall ((n Nat) (xs List2)) (= (mod3 n (length (append (Cons_1 xs) (Cons (Cons_0 xs) Nil)))) (mod3 n (length xs))))；(forall ((xs List2) (a sk_a) (zs List2)) (= (append xs (Cons a zs)) (Cons a (append xs zs))))。
- 根节点筛除记录：(forall ((n Nat) (xs List2)) (= (mod3 (S n) (length xs)) (mod3 n (length (append (Cons_1 xs) (Cons (Cons_0 xs) Nil)))))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal asserts that appending (drop n ys) before (take n ys) equals appending ys, but drop produces the suffix and take produces the prefix; e.g. n=(S Z), ys=(Cons a (Cons b Nil)), zs=Nil gives (Con
- 已生成的solver hint：The prior append-right-cons lemma is invalid (append recurses on the first argument), and the revival candidates are either invalid/trivial. The goal is a rotate/drop/take decomposition; the key missing ingredient is the interaction of length with append, since the rec…
- 理想证明路线及改进：先做符号签名检查；证明单元素append长度、mod3的循环计数不变量与有界drop/take桥，控制每轮只补一个可验证缺口。

#### standard/sort_BubSortCount — P1

- 日志：A/T/L/P=6/0/1/0; 691.89s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_BubSortCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_BubSortCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_BubSortCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list)) (= (count x (bubsort y)) (count x y)))))`
- 实际过程：bubble保count候选反复出现，库只有相邻交换保count，根0棵树。 已证库关键片段：(forall ((x Int) (a Int) (b Int) (l list)) (= (count x (cons a (cons b l))) (count x (cons b (cons a l)))))。最近/代表性候选：(forall ((x Int) (y list)) (= (count x (second (bubble y))) (count x y)))；(forall ((y list)) (=> (not (first (bubble y))) (= (second (bubble y)) y)))。
- 根节点筛除记录：(forall ((x Int) (y list)) (= (count x (bubsort y)) (count x y))) → Same as original goal
- 理想证明路线及改进：给 bubble 输出第二分量做构造子递推证明，再针对 bubsort 的循环回调使用适当终止/良基证明；不要把相邻交换当成整个bubble已证明。

#### standard/sort_BubSortIsSort — P2

- 日志：A/T/L/P=16/3/4/0; 1200.23s; timeout；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_BubSortIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_BubSortIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_BubSortIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list)) (= (bubsort x) (isort x)))))`
- 实际过程：库多为定义展开；bubsort(cons)=insert(bubsort tail) 因递归形状不同被否定。 已证库关键片段：(forall ((h Int) (t list)) (= (isort (cons h t)) (insert2 h (isort t))))；(forall ((h Int) (t list)) (= (insert2 h (isort (second (bubble (cons h t))))) (isort (cons h (second (bubble (cons h t)))))))；另2条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((h Int) (t list)) (= (bubsort (cons h t)) (insert2 h (bubsort t)))) → bubsort recurses on (first (bubble ...)) of its own argument, which is not related to the recursion of bubsort t, so (bubsort (cons h t)) and (insert2 h (bubsort t)) cannot be pro…
- 子节点否定记录（来源未必是solver反例）：bubsort recurses on (first (bubble ...)) of its own argument, which is not related to the recursion of bubsort t, so (bubsort (cons h t)) and (insert2 h (bubsort t)) cannot be proven equal; the needed
- 理想证明路线及改进：较稳路线是 isort(second(bubble xs))=isort xs 加无交换时已排序，再证明循环不变量；把非结构递归节点标为需度量证明，而非 invalid。

#### standard/sort_HSortCount — P1

- 日志：A/T/L/P=33/10/5/3; 1202.42s; timeout; H=4；失败节点 11。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_HSortCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_HSortCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_HSortCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list2)) (= (count x (hsort y)) (count x y)))))`
- 实际过程：已证明 hpairwise/hmerging 的count连接，仍缺 toHeap 输入到堆内容的组合桥；LLM因无multiset公理否定。 已证库关键片段：(forall ((x Int) (l list)) (= (count x (toList (hmerging (hpairwise l)))) (count x (toList (hmerging l)))))；(forall ((h Int) (t list2)) (= (toHeap2 (cons2 h t)) (cons (Node Nil h Nil) (toHeap2 t))))；另3条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x Int) (a Heap) (b Heap)) (= (count x (toList (hmerge a b))) (count x (toList (Node (Node_0 a) (Node_1 a) (Node_2 a))))… → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：hmerging is only structurally defined with no axiom relating its output element multiset to its input heaps; the goal asserts a count-preservation/insertion property (that merging a singleton `Node Ni
- 理想证明路线及改进：证明 hmerge 的元素计数关系与toHeap2/列表堆汇总，再证明toList输出计数；不能因为原公理没写目标性质就否定可归纳推导的性质。

#### standard/sort_HSortIsSort — P0

- 日志：A/T/L/P=6/0/0/0; 686.20s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_HSortIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_HSortIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_HSortIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list2)) (= (hsort x) (isort x)))))`
- 实际过程：提前check-sat；候选把 list-of-heaps 的toHeap2当Heap传给toList，还有无序cons结果。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (h Heap)) (= (toList (hmerge (Node Nil x Nil) h)) (cons2 x (toList h))))；(forall ((x Int) (L list)) (= (toList (hmerging (cons (Node Nil x Nil) L))) (insert2 x (toList (hmerging L)))))。
- 理想证明路线及改进：先修输入和类型；后续需堆不变量/提取最小元与排序表征桥，不应假定任意Heap的toList都有排序输出。

#### standard/sort_MSortBU2Count — P0

- 日志：A/T/L/P=6/0/0/0; 245.77s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBU2Count/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBU2Count/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBU2Count/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list2)) (= (count x (msortbu2 y)) (count x y)))))`
- 实际过程：0库、各轮unknown；保留输入实测 plus未声明，还曾凭空生成countlist。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (a list2) (b list2)) (= (count x (lmerge a b)) (plus (count x a) (count x b))))；(forall ((x Int) (c list2) (d list2) (r list)) (= (count x (mergingbu2 (cons c (cons d r)))) (plus (count x c) (count x (mergingbu2 (cons d r))))))。
- 根节点筛除记录：(forall ((x Int) (a list2) (b list2)) (= (count x (lmerge a b)) (count x (cons2 (head2 a) (tail2 a))))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：先提供严格签名和快速编译反馈；再证明risers保元素、pairwise合并保计数及mergingbu2不变量。Nat计数不能直接用Int的+。

#### standard/sort_MSortBU2IsSort — P1

- 日志：A/T/L/P=69/41/9/2; 1203.28s; timeout; H=26；失败节点 13。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBU2IsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBU2IsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBU2IsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list2)) (= (msortbu2 x) (isort x)))))`
- 实际过程：69次生成、41棵树、仅2个子目标证明成功；多数库是重括号/插入改写，最终把等价目标当缺失引理。 已证库关键片段：(forall ((x list2) (y list2)) (= (msortbu2 (lmerge x y)) (mergingbu2 (risers (lmerge x y)))))；(forall ((x list2) (y list2) (z list2)) (= (isort (lmerge (lmerge x y) z)) (isort (lmerge x (lmerge y z)))))；另7条。最近/代表性候选：(forall ((x list2)) (is-sorted2 (msortbu2 x)))；(forall ((x list2)) (is-sorted2 (isort x)))。
- 根节点筛除记录：(forall ((x list2) (y list2)) (= (lmerge x y) (lmerge y x))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal is not a theorem: `isort` is recursive insertion sort while `lmerge` preserves/merges sorted structure only under sortedness invariants, but `isort (lmerge x (cons2 a y))` and `isort (insert2
- 理想证明路线及改进：轻量frontier保留一个runs排序/合并不变量，限制同义目标扩张；先关闭 merge 对未排序表无条件交换等不正确路线，再做分支条件明确的组合证明。

#### standard/sort_MSortBUCount — P0

- 日志：A/T/L/P=6/0/0/0; 755.24s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBUCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBUCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBUCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list2)) (= (count x (msortbu y)) (count x y)))))`
- 实际过程：同时有提前check-sat、未声明+_nat/plus/countlist和占位式forall ...；0库。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (a list2) (b list2)) (= (count x (lmerge a b)) (+_nat (count x a) (count x b))))；(forall ((x Int) (y list2)) (= (count x (msortbu y)) (count x (mergingbu (map2 lam y)))))。
- 理想证明路线及改进：先修查询和编译反馈；数学上需要singleton-map输入与pairwise/merging的计数汇总。没有可用加法符号时给有类型的递推关系，或单独审计保守定义扩展，不能任意补公理。

#### standard/sort_MSortBUIsSort — P0

- 日志：A/T/L/P=6/0/0/0; 692.59s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBUIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBUIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortBUIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list2)) (= (msortbu x) (isort x)))))`
- 实际过程：提前check-sat；正确方向的单元素merge=insert和mergingbu/map桥尚未被真实目标查询评估。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((a Int) (y list2)) (= (lmerge (cons2 a nil2) y) (insert2 a y)))；(forall ((a Int) (y list2)) (= (mergingbu (cons (cons2 a nil2) (map2 lam y))) (insert2 a (mergingbu (map2 lam y)))))。
- 理想证明路线及改进：修查询后先证lmerge(singleton,y)=insert2(x,y)，再证明runs的合并不变量；3秒规范化短测试尚未解决根目标。

#### standard/sort_MSortTDCount — P0

- 日志：A/T/L/P=6/0/0/0; 307.30s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortTDCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortTDCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortTDCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list)) (= (count x (msorttd y)) (count x y)))))`
- 实际过程：后几轮把Nat型count送进内建+，实测expecting an arithmetic subterm；0库。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (l list) (k Int)) (= (count x l) (+ (count x (ztake k l)) (count x (zdrop k l)))))；(forall ((x Int) (a list) (b list)) (= (count x (lmerge a b)) (+ (count x a) (count x b))))。
- 根节点筛除记录：(forall ((x Int) (l list)) (= (count x (msorttd l)) (count x l))) → Same as original goal
- 理想证明路线及改进：修类型后用split计数守恒与merge计数组合，随后按子表长度归纳；不能将take/drop子表直接当作原列表的语法子项。

#### standard/sort_MSortTDIsSort — P2

- 日志：A/T/L/P=6/0/2/0; 604.79s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortTDIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortTDIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_MSortTDIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list)) (= (msorttd x) (isort x)))))`
- 实际过程：库仅insert/lmerge singleton与isort(cons)；整轮反复 isort(lmerge x y)=lmerge(isort x,isort y)。 已证库关键片段：(forall ((a Int) (y list)) (= (insert2 a y) (lmerge (cons a nil) y)))；(forall ((a Int) (y list)) (= (isort (cons a y)) (insert2 a (isort y))))。最近/代表性候选：(forall ((x list) (y list)) (= (isort (lmerge x y)) (isort (lmerge y x))))；(forall ((a Int) (y list)) (= (isort (cons a y)) (insert2 a (isort y))))。
- 根节点筛除记录：(forall ((x list)) (= (isort x) (msorttd x))) → Same as original goal
- 理想证明路线及改进：将合并规范化桥与split覆盖桥分开证明，随后长度归纳拼接两条已排序子表；不要用 lmerge(take,drop)=原表 这种假等式。

#### standard/sort_NMSortTDCount — P0

- 日志：A/T/L/P=6/0/0/0; 455.04s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_NMSortTDCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_NMSortTDCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_NMSortTDCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list)) (= (count x (nmsorttd y)) (count x y)))))`
- 实际过程：候选包含Nat计数的内建+类型错误；原先无加法的计数分解也未闭合。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (a list) (b list)) (= (count x (lmerge a b)) (+ (count x a) (count x b))))；(forall ((x Int) (y list) (n Nat)) (= (+ (count x (take n y)) (count x (drop n y))) (count x y)))。
- 根节点筛除记录：(forall ((x Int) (y list)) (= (count x (nmsorttd y)) (count x y))) → Same as original goal
- 理想证明路线及改进：先修类型，保留 merge 保计数与take/drop分割两段；为结构Nat半长递归提供严格减小证据。

#### standard/sort_NMSortTDIsSort — P1

- 日志：A/T/L/P=6/0/1/0; 593.08s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_NMSortTDIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_NMSortTDIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_NMSortTDIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list)) (= (nmsorttd x) (isort x)))))`
- 实际过程：库已证insert与lmerge相容；末轮length被当Int相加而解析失败。 已证库关键片段：(forall ((x list) (y list) (z Int)) (= (insert2 z (lmerge x y)) (lmerge (insert2 z x) y)))。最近/代表性候选：(forall ((x list) (y list)) (= (isort (lmerge x y)) (lmerge (isort x) (isort y))))；(forall ((x list) (y list)) (= (length (lmerge x y)) (+ (length x) (length y))))。
- 根节点筛除记录：(forall ((x list) (y list)) (is-cons (lmerge x y))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：复用这条真正有用的相容关系构造规范化证明，再补split/长度归纳，不要偏到未类型检查的length同态。

#### standard/sort_QSortCount — P0

- 日志：A/T/L/P=6/0/0/0; 238.65s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_QSortCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_QSortCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_QSortCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list)) (= (count x (qsort y)) (count x y)))))`
- 实际过程：每轮使用未声明plus，全部unknown；库0。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((h Int) (x Int) (t list)) (= (count x (cons h t)) (plus (count x (cons h nil)) (count x t))))；(forall ((h Int) (x Int) (t list)) (= (plus (count x (filter (lam h) t)) (count x (filter (lam2 h) t))) (count x t)))。
- 根节点筛除记录：(forall ((x Int) (l list)) (= (count x (qsort l)) (count x l))) → Same as original goal
- 理想证明路线及改进：严格编译反馈后生成filter互补分区与append计数桥；若语言缺Nat加法，先采用typed关系/保守定义方案。随后按过滤子表长度归纳。

#### standard/sort_QSortIsSort — P2

- 日志：A/T/L/P=6/0/2/0; 692.02s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_QSortIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_QSortIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_QSortIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list)) (= (qsort x) (isort x)))))`
- 实际过程：反复提出insert2(x,isort y)=连接两侧过滤排序结果的大桥，库只有filter/isort定义展开。 已证库关键片段：(forall ((p fun1) (x list)) (= (filter p x) (ite (is-cons x) (ite (apply1 p (head x)) (cons (head x) (filter p (tail x))) (filter p (tail x))) nil)))；(forall ((x Int) (y list)) (= (isort (cons x y)) (insert2 x (isort y))))。最近/代表性候选：(forall ((x Int) (y list)) (= (insert2 x (isort y)) (append (append (isort (filter (lam x) y)) (cons x nil)) (isort (filter (lam2 x) y)))))；(forall ((x Int) (y list)) (= (isort (cons x y)) (insert2 x (isort y))))。
- 根节点筛除记录：(forall ((x list) (y list)) (= (isort (append x y)) (append (isort x) (isort y)))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：先分解为过滤边界、排序与过滤相容、pivot插入连接三块；必须验证子表变小，不能把一个完整快排正确性变体当“小引理”。

#### standard/sort_SSortCount — P1

- 日志：A/T/L/P=19/4/8/1; 1203.25s; timeout; H=8；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_SSortCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_SSortCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_SSortCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list)) (= (count x (ssort y)) (count x y)))))`
- 实际过程：已证delete不同值保count等8条，但未完成最小值确实出现时的删除一次关系。 已证库关键片段：(forall ((x Int) (z Int) (y list)) (=> (not (= x z)) (= (count x (delete z y)) (count x y))))；(forall ((x Int) (z Int) (y list)) (=> (not (= x z)) (= (count x (cons z y)) (count x y))))；另6条。最近/代表性候选：无可复用失败候选。
- 子节点否定记录（来源未必是solver反例）：The proposed lemmas relating count/delete/ssort_minimum are refuted as unsat against the axioms (they are not consequences of the given definitions), so the proof goal relies on an unprovable counting
- 理想证明路线及改进：先证minimum属于非空输入，再按x=m与x≠m拼接count(cons m(delete m xs))=count xs；之后用delete长度下降完成ssort。

#### standard/sort_SSortIsSort — P1

- 日志：A/T/L/P=20/10/5/0; 1203.29s; timeout; H=9；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_SSortIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_SSortIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_SSortIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list)) (= (ssort x) (isort x)))))`
- 实际过程：已有minimum递推和ssort定义，minimum=head(isort输入) 因失败child被传染判invalid。 已证库关键片段：(forall ((x Int) (y list)) (= (insert2 x (isort y)) (isort (cons x y))))；(forall ((x Int) (y list)) (= (head (insert2 x (isort y))) (ite (is-cons y) (ite (<= x (head (isort y))) x (head (isort y))) x)))；另3条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x Int) (y list)) (= (ssort_minimum x y) (head (isort (cons x y))))) → The CURRENT goal is equivalent (via lib_1) to the already-invalid child lemma (ssort_minimum x y) = (head (insert2 x (isort y))), which is not a theorem of the given axioms.
- 子节点否定记录（来源未必是solver反例）：The CURRENT goal is equivalent (via lib_1) to the already-invalid child lemma (ssort_minimum x y) = (head (insert2 x (isort y))), which is not a theorem of the given axioms.
- 理想证明路线及改进：证明最小值头部性质及删除后规范排序分解；对失败child的错误前提做局部修复，不从一个辅助命题错推出根目标错。

#### standard/sort_TSortCount — P0

- 日志：A/T/L/P=6/0/0/0; 781.56s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_TSortCount/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_TSortCount/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_TSortCount/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Int) (y list)) (= (count x (tsort y)) (count x y)))))`
- 实际过程：提前check-sat；已提出任意Tree/任意acc上的count插入桥，但0库不能说明桥无效。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (h Int) (T Tree) (L list)) (= (count x (flatten (add h T) L)) (count x (cons h (flatten T L)))))；(forall ((x Int) (L list)) (= (count x (flatten (toTree L) nil)) (count x L)))。
- 理想证明路线及改进：先规范查询；再验证flatten(T,cons a acc)的计数搬移及add的计数贡献，再对toTree列表归纳。

#### standard/sort_TSortIsSort — P0

- 日志：A/T/L/P=6/0/0/0; 830.50s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_TSortIsSort/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_TSortIsSort/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/sort_TSortIsSort/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x list)) (= (tsort x) (isort x)))))`
- 实际过程：提前check-sat；候选无条件把任意树/任意acc的flatten(add)等同insert，泛化丢失BST及acc边界。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Int) (t Tree)) (=> (forall ((y Int)) (=> (member y (flatten t nil)) (<= y x))) (= (flatten (add x t) nil) (insert2 x (flatten t nil)))))；(forall ((x list)) (= (flatten (toTree x) nil) (isort x)))。
- 理想证明路线及改进：修查询后保留toTree生成域或明确BST/边界不变量，不能把任意acc泛化成有序acc。独立证明插入保持不变量。

#### standard/tree_Flatten1List — P0

- 日志：A/T/L/P=6/0/0/0; 657.79s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/tree_Flatten1List/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/tree_Flatten1List/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/tree_Flatten1List/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((ps list)) (= (flatten1 ps) (concatMap lam ps)))))`
- 实际过程：提前check-sat；候选flatten1(cons t ts)=append(flatten0 t,flatten1 ts)方向合理但0库。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((t Tree) (ts list)) (= (flatten1 (cons t ts)) (append (flatten0 t) (flatten1 ts))))；(forall ((t Tree) (ts list) (u Tree) (us list)) (= (flatten1 (cons t (cons u us))) (append (flatten0 t) (append (flatten0 u) (flatten1 us)))))。
- 根节点筛除记录：(forall ((ps list)) (= (concatMap lam ps) (flatten1 ps))) → Same as original goal
- 理想证明路线及改进：修查询，再对待处理森林的总节点度量证明该栈不变量；flatten1会改变栈长度，不能仅对列表tail作普通归纳。

#### standard/tree_Flatten3 — P1

- 日志：A/T/L/P=15/7/9/1; 1202.23s; timeout; H=1；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/tree_Flatten3/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/tree_Flatten3/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/tree_Flatten3/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((p Tree)) (= (flatten3 p) (flatten0 p)))))`
- 实际过程：9条库已有两种flatten对旋转的展开与append代数；结构递归步因需祖先命题被否定。 已证库关键片段：(forall ((x list) (y list) (z list)) (= (append (append x y) z) (append x (append y z))))；(forall ((x list)) (= (append x nil) x))；另7条。最近/代表性候选：(forall ((x list)) (= (append nil x) x))；(forall ((l Tree) (a sk_a) (r Tree) (b sk_a) (rr Tree)) (= (flatten0 (Node (Node l a r) b rr)) (flatten0 (Node l a (Node r b rr)))))。
- 根节点筛除记录：(forall ((l Tree) (a sk_a) (r Tree)) (= (flatten3 (Node l a r)) (append (flatten3 l) (cons a (flatten3 r))))) → current goal needs the flatten3/flatten0 bridge (ancestor A0), which is filtered; without it the tree-induction does not close from the given axioms.
- 子节点否定记录（来源未必是solver反例）：The inductive step cannot be closed. flatten3 (Node l a r) does not equal append (flatten3 l) (cons a (flatten3 r)) (as confirmed: this lemma is invalid for non-Nil l due to flatten3's rotation on non
- 已生成的solver hint：The library now has the flatten3 rotation lemma, the flatten0 decomposition (flatten0 (Node l a r) = append (flatten0 l) (cons a (flatten0 r))), and the append/cons interchange. The remaining gap is a flatten3 decomposition that is correct for non-Nil left subtrees; th…
- 理想证明路线及改进：验证旋转规约的良基度量，保存flatten0语义不变量；对复合node的局部剩余义务做frontier，避免绕回全局flatten等价。

#### standard/weird_nat_mul3_assoc1 — P2

- 日志：A/T/L/P=53/16/12/3; 1203.27s; timeout; H=10；失败节点 16。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc1/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc1/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc1/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat)) (= (mul3 (mul3 x1 x2 x3) x4 x5) (mul3 x1 x2 (mul3 x3 x4 x5))))))`
- 实际过程：53次生成16棵树；12条库多为add3和零例，关键mul3分配被错误的一参线性展开解释否定。 已证库关键片段：(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (add3 (add3 a b c) d e) (add3 a b (add3 c d e))))；(forall ((a Nat) (b Nat) (c Nat)) (= (add3 Z a b) (add3 a Z b)))；另10条。最近/代表性候选：(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (mul3 a b (add3 c d e)) (add3 (mul3 a b c) (mul3 a b d) (mul3 a b e))))；(forall ((a Nat) (b Nat) (c Nat)) (= (mul3 a b c) (mul3 b a c)))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat) (d Nat)) (= (mul3 (mul3 a b c) d (S Z)) (mul3 a (mul3 b c d) (S Z)))) → The goal requires associativity of mul3, but no mul3 lemma is available in the library, and the only candidate lemma is exactly the CURRENT goal (forbidden to restate); the given …
- 子节点否定记录（来源未必是solver反例）：The goal requires a first-argument recursion equation for mul3 (e.g. mul3 (S n) d e = add3 (mul3 n d e) d e), but that equation contradicts the axioms (as independently confirmed by the invalid-lemma
- 理想证明路线及改进：从三个非零构造子同时展开提取真实多项式增量；先验证add3 AC与分配基础，再做乘法嵌套结合，不猜mul3(Sx)y z=mul3 x y z+y+z。

#### standard/weird_nat_mul3_assoc2 — P2

- 日志：A/T/L/P=6/0/2/0; 786.16s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc2/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc2/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc2/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat)) (= (mul3 (mul3 x1 x2 x3) x4 x5) (mul3 x1 (mul3 x2 x3 x4) x5)))))`
- 实际过程：6次生成0棵树，库仅add3交换与末参Z特例；候选一次提出三种递增桥。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 y x z)))；(forall ((a Nat) (b Nat) (c Nat) (d Nat)) (= (mul3 (mul3 a b c) d Z) (mul3 a (mul3 b c d) Z)))。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y (S z)) (add3 (mul3 x y z) (mul3 x y (S Z)) Z)))；(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (mul3 a (mul3 b c d) e) (add3 (mul3 a b (mul3 c d e)) Z Z)))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (mul3 (mul3 a b c) d e) (mul3 a (mul3 b c d) e))) → Same as original goal
- 理想证明路线及改进：先完成一种真实构造子增量桥，继而得到所需分配；零特例不能替代一般结合律。低成本阶段不宜优先期待恢复。

#### standard/weird_nat_mul3_assoc3 — P1

- 日志：A/T/L/P=36/6/5/0; 1203.28s; timeout; H=10；失败节点 8。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc3/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc3/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_assoc3/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat)) (= (mul3 x1 (mul3 x2 x3 x4) x5) (mul3 x1 x2 (mul3 x3 x4 x5))))))`
- 实际过程：36次生成仅5条库；hint声称mul3定义退化/目标不可证，依据来自LLM invalid而非模型。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 (add3 x y Z) z Z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (add3 (add3 x y z) Z Z) (add3 x (add3 y z Z) Z)))；另3条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat) (w Nat)) (= (mul3 x y (mul3 z w Z)) (mul3 x (mul3 y z w) Z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 y x z)))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (mul3 a (mul3 b c d) e) (mul3 (mul3 a b c) d e))) → The goal asserts associativity of `mul3`, but `mul3` is only given by a raw case-splitting axiom with no algebraic (distributivity/associativity) law relating it to `add3`; the le…
- 子节点否定记录（来源未必是solver反例）：The target associativity law for mul3 is not derivable from the given axioms; the recursive definition of mul3 is not a genuine multiplication definition (it forces many cases to Z), and the previousl
- 已生成的solver hint：The goal is genuinely unprovable from the given mul3 axiom (the definition is a degenerate case-split that forces most products to Z and gives no algebraic law). Repeated attempts at full associativity/commutativity/rotation of mul3 have all failed (invalid) or timed o…
- 理想证明路线及改进：首先隔离未验证否定；以原定义的constructor正规形建立乘法分配/重括号链，设置同义结合律交换循环的退出条件。

#### standard/weird_nat_mul3_comm12 — P1

- 日志：A/T/L/P=20/7/6/0; 1203.26s; timeout; H=4；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm12/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm12/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm12/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 y x z)))))`
- 实际过程：库已经覆盖零例和add3交换，但S/S子目标被以递归不对称否定；hint又猜复杂p(p x)形状。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 y x z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 Z y z) (mul3 y Z z)))；另4条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 x z y)))；(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 Z x y) (mul3 x Z y)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x (S y) z) (mul3 (S y) x z))) → The goal asserts commutativity of mul3 in its first two arguments for non-degenerate (S-headed) arguments, but the definition of mul3 is asymmetric in its first two arguments and …
- 子节点否定记录（来源未必是solver反例）：The CURRENT goal is a variable-swapping symmetry variant of the unprovable mul3/add3 cyclic definition; its child lemma was marked invalid for exactly this reason (mul3 is only given a self-referentia
- 已生成的solver hint：The goal is commutativity of mul3 in its first two arguments. The library already has the Z-degenerate cases (mul3 Z y z = mul3 y Z z, mul3 x y Z = mul3 x Z y, mul3 Z x y = mul3 x Z y, mul3 x y Z = mul3 y x Z). The missing step is the S-headed swap of the first two arg…
- 理想证明路线及改进：由程序而非LLM执行构造子代入与selector化简，输出精确S/S/S展开，再让LLM只补加法重排桥。

#### standard/weird_nat_mul3_comm13 — P1

- 日志：A/T/L/P=19/4/6/0; 1203.27s; timeout; H=4；失败节点 6。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm13/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm13/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm13/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 z y x)))))`
- 实际过程：库已证明三个zero-annihilation事实，诊断却给出mul3 Z(SZ)Z=SZ的矛盾说法；hint还声称两次三循环等于反转。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 x z y)))；(forall ((a Nat) (b Nat) (c Nat)) (= (add3 a b c) (add3 b a c)))；另4条。最近/代表性候选：(forall ((x Nat) (y Nat)) (= (mul3 x y Z) Z))；(forall ((x Nat) (z Nat)) (= (mul3 x Z z) Z))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 y x z))) → The function mul3 is asymmetric. When x=Z and y=S y', mul3 Z y z reduces to S(add3 Z y' z), but mul3 y Z z (with second arg Z) reduces to Z. E.g. mul3 Z (S Z) Z = S Z while mul3 (…
- 子节点否定记录（来源未必是solver反例）：The function mul3 is asymmetric. When x=Z and y=S y', mul3 Z y z reduces to S(add3 Z y' z), but mul3 y Z z (with second arg Z) reduces to Z. E.g. mul3 Z (S Z) Z = S Z while mul3 (S Z) Z Z = Z, so mul3
- 已生成的solver hint：The goal mul3 x y z = mul3 z y x is a full reversal. The library now has add3 commutativity/associativity and the zero-argument mul3 facts. The last round's commutativity lemmas (swap first two / first and third) were shown invalid, so plain pairwise swaps are not the …
- 理想证明路线及改进：先检测诊断与已证库直接冲突；参数置换用实际置换组合校验，三循环不能生成奇置换。走有证据的交换子目标，不继承错误群关系。

#### standard/weird_nat_mul3_comm23 — P1

- 日志：A/T/L/P=14/3/6/1; 1024.17s; attempts_exhausted; H=2；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm23/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm23/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_comm23/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 x z y)))))`
- 实际过程：add3两两交换已证，主缺口仍是mul3(Sx)y z；hint围绕不成立的乘法=加法恒等式解释。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 x z y)))；(forall ((y Nat) (z Nat)) (= (mul3 Z y z) (mul3 Z z y)))；另4条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 z y x)))；(forall ((y Nat) (z Nat)) (= (mul3 (S Z) y z) (mul3 (S Z) z y)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 x z y))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：Expanding mul3 (S x) y z via A2 requires the unprovable identity mul3 (S Z) y z = add3 y z Z, which contradicts the defining axioms; the same invalid reason as the child lemma L2_1 propagates to the C
- 已生成的solver hint：The library already contains the add3 commutativity/rotation axioms (x y z = x z y, = y x z, = z y x), so re-proving those is wasted. The goal is commutativity of mul3 in its 2nd/3rd arguments, and the only revival candidate is a specialized expansion of mul3 (S Z) (S …
- 理想证明路线及改进：从实际全S展开化简，隔离mul3(1,y,z)基础乘积与一般递归项，直接对比交换后的残差。

#### standard/weird_nat_mul3_rot — P1

- 日志：A/T/L/P=33/4/6/0; 1202.42s; timeout; H=3；失败节点 6。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_rot/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_rot/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_rot/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 y x z)))))`
- 实际过程：实际目标是交换前两参，不是由文件名猜测的三循环；库6条主要是add3换序。 已证库关键片段：(forall ((a Nat) (b Nat) (c Nat)) (= (add3 a b c) (add3 b a c)))；(forall ((a Nat) (b Nat) (c Nat)) (= (add3 a b c) (add3 a c b)))；另4条。最近/代表性候选：(forall ((a Nat) (b Nat) (c Nat)) (= (add3 a b c) (add3 b a c)))；(forall ((a Nat) (b Nat) (c Nat)) (= (add3 a b c) (add3 a c b)))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat)) (= (mul3 a b c) (mul3 a c b))) → The goal requires commutativity of mul3, but the recursive definition is asymmetric; the proposed symmetry lemmas (mul3 a b c = mul3 a (S b) c and mul3 a b c = mul3 a b (S c)) con…
- 子节点否定记录（来源未必是solver反例）：The goal requires commutativity of mul3, but the recursive definition is asymmetric; the proposed symmetry lemmas (mul3 a b c = mul3 a (S b) c and mul3 a b c = mul3 a b (S c)) contradict the axioms (c
- 理想证明路线及改进：以SMT目标为准，复用经过验证的构造子交换路线；避免命名诱导及反复加add3已证变体。

#### standard/weird_nat_mul3_rrot — P1

- 日志：A/T/L/P=30/7/3/0; 1202.73s; timeout; H=9；失败节点 10。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_rrot/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_rrot/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_rrot/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 z x y)))))`
- 实际过程：只有add3循环/交换与mul3零例；LLM以pathological asymmetric定义判交换子目标不可证。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 y z x)))；(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 x z y)))；另1条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 z x y)))；(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 y z x)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 x z y))) → The mul3 definition is a pathological asymmetric nested ite; the goal requires a y/z symmetry of mul3 that is not derivable from the axioms (all prior helper-lemma attempts were m…
- 子节点否定记录（来源未必是solver反例）：The essential recurrence/helper lemmas needed to establish commutativity of mul3 (lemmas 3 and 4, which express mul3 x y (S z) in terms of mul3 x y z) contradict the axioms, indicating mul3 does not h
- 理想证明路线及改进：先证明足够的参数交换桥，再组合成目标循环；保留递归参数的泛化与实际小项IH，不把定义非对称当成性质非对称。

#### standard/weird_nat_mul3_same — P1

- 日志：A/T/L/P=48/14/28/10; 1203.31s; timeout; H=6；失败节点 17。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_same/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_same/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3_same/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3acc x y z)))))`
- 实际过程：48次生成14棵树、28条库、10个子目标成功；add3=add3acc已证后仍积累巨型同余/自反包装。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x (S y) z) (S (add3acc x y z))))；(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc Z (S y) z) (add3acc Z y (S z))))；另26条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3acc x y z)))。
- 子节点否定记录（来源未必是solver反例）：Using lib_18 (add3acc (mul3 x y z) Z Z = mul3 x y z), the CURRENT goal reduces exactly to (mul3acc x y z = mul3 x y z), which is strict ancestor A0; no independent proof exists without restating that
- 理想证明路线及改进：一旦底层加法桥入库，规范化双方递归展开，明确列出剩余mul3/mul3acc的较小调用关系；设证明里程碑并预留父目标重试预算。

#### standard/weird_nat_mul3acc_assoc1 — P2

- 日志：A/T/L/P=5/0/2/0; 707.56s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc1/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc1/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc1/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x1 Nat) (x2 Nat) (x3acc Nat) (x4 Nat) (x5 Nat)) (= (mul3acc (mul3acc x1 x2 x3acc) x4 x5) (mul3acc x1 x2 (mul3acc x3acc x4 x5))))))`
- 实际过程：库只有末参0和重复特例；候选将第三参增加1误写成加x和y被反驳。 已证库关键片段：(forall ((x Nat) (y Nat)) (= (mul3acc x y Z) Z))；(forall ((x Nat)) (= (mul3acc x (S Z) Z) Z))。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y (S z)) (add3acc (mul3acc x y z) (mul3acc x y (S Z)) Z)))；(forall ((x Nat)) (= (mul3acc x (S Z) Z) Z))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y (S z)) (add3acc (mul3acc x y z) x y))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：累积参数名字不等于数学累积语义；按真实定义建立增量（应涉及x*y的现有表达），先代数语义桥后结合律。

#### standard/weird_nat_mul3acc_assoc2 — P2

- 日志：A/T/L/P=11/1/4/0; 647.87s; attempts_exhausted；失败节点 1。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc2/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc2/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc2/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x1 Nat) (x2 Nat) (x3acc Nat) (x4 Nat) (x5 Nat)) (= (mul3acc (mul3acc x1 x2 x3acc) x4 x5) (mul3acc x1 (mul3acc x2 x3acc x4) x5)))))`
- 实际过程：库4条中含完全自反式与末参Z特例，未建立一般mul3acc代数。 已证库关键片段：(forall ((a Nat) (b Nat) (c Nat)) (= (mul3acc (mul3acc a b c) Z Z) (mul3acc a (mul3acc b c Z) Z)))；(forall ((a Nat) (b Nat) (c Nat) (d Nat)) (= (mul3acc (mul3acc a b c) d Z) (mul3acc a (mul3acc b c d) Z)))；另2条。最近/代表性候选：(forall ((a Nat) (b Nat) (c Nat) (d Nat)) (= (mul3acc (mul3acc a b c) d Z) (mul3acc a (mul3acc b c d) Z)))；(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (mul3acc (mul3acc a b c) d (S Z)) (mul3acc a (mul3acc b c d) (S Z))))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (mul3acc (mul3acc a b c) d e) (mul3acc a (mul3acc b c d) e))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：The recursion for mul3acc is only defined via an ite on (is-S x), (is-S y), (is-S z) and inner (is-S (p x)) cases, but the proof goal requires associativity involving an accumulator term (S e) and arb
- 理想证明路线及改进：过滤逻辑自反/纯包装但保留有用构造子式；以真实constructor展开建立可复用代数节点，不继续增加零外壳。

#### standard/weird_nat_mul3acc_assoc3 — P2

- 日志：A/T/L/P=6/1/1/0; 739.66s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc3/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc3/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_assoc3/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x1 Nat) (x2 Nat) (x3acc Nat) (x4 Nat) (x5 Nat)) (= (mul3acc x1 (mul3acc x2 x3acc x4) x5) (mul3acc x1 x2 (mul3acc x3acc x4 x5))))))`
- 实际过程：唯一库是加零包装；LLM给出的乘法结合反例依赖错误展开。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc x y (add3acc Z Z z))))。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc x y (add3acc Z Z z))))；(forall ((x Nat) (y Nat) (z Nat) (w Nat)) (= (mul3acc x y (mul3acc z w x)) (mul3acc z w (mul3acc x y x))))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc (mul3acc x y (S Z)) Z z))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：mul3acc does not compute x*y*z (e.g. mul3acc (S (S Z)) (S (S Z)) (S Z) evaluates to 2, not 4), so the claimed associativity identity is not derivable from the given axioms; the only library lemma is t
- 理想证明路线及改进：核验反例后恢复候选资格，先建立add3acc正规形/分配桥。该题仍属长链难例，不能估计一次hint即可恢复。

#### standard/weird_nat_mul3acc_comm12 — P1

- 日志：A/T/L/P=6/0/4/0; 510.29s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm12/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm12/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm12/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc y x z)))))`
- 实际过程：4条add3acc代数已证，但没有mul3acc全S的规范展开；root0树。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y z) (add3acc Z x (add3acc Z y z))))；(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y z) (add3acc Z (add3acc Z x y) z)))；另2条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y z) (add3acc y x z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc x z y)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc y x z))) → Same as original goal
- 理想证明路线及改进：补可直接从定义验证的全S展开，将交换问题降到add3acc重排与较小调用交换。允许证明frontier处理此结构化候选。

#### standard/weird_nat_mul3acc_comm13 — P1

- 日志：A/T/L/P=24/5/2/0; 1200.22s; timeout; H=3；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm13/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm13/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm13/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc z y x)))))`
- 实际过程：库仅两个零例，反复把交换后的successor在不同参数间直接搬移。 已证库关键片段：(forall ((y Nat) (z Nat)) (= (mul3acc z y Z) Z))；(forall ((y Nat) (z Nat)) (= (mul3acc Z y z) Z))。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y z) (add3acc y x z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc y x z)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc (S x) y z) (mul3acc x (S y) z))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal (mul3acc x y z) = (mul3acc y z x) is not a theorem; the necessary decomposition lemma relating mul3acc (S x) y z to sums of mul3acc was refuted against the axioms, and the definition is cycli
- 理想证明路线及改进：用小构造子实例筛掉不成立的搬移，再以全S展开和真实交换关系推进，避免相似外形替代数学关系。

#### standard/weird_nat_mul3acc_comm23 — P1；相对M2回退

- 日志：A/T/L/P=6/0/0/0; 815.74s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm23/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm23/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_comm23/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc x z y)))))`
- 实际过程：M2成功但v5失败；本题没有hint诊断，库0，不能归因于hint文字带偏。 已证库关键片段：无已验证库引理。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y z) (add3acc y x z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc y x z)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc x z y))) → Same as original goal
- 理想证明路线及改进：M2库显示关键是全S展开、add3acc第二/三参交换、mul3acc(1,y,z)交换。将此提炼成通用constructor-normalization经验并在当前理论重证。

#### standard/weird_nat_mul3acc_rot — P1

- 日志：A/T/L/P=16/10/5/4; 1200.23s; timeout; H=4；失败节点 8。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_rot/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_rot/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_rot/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc y x z)))))`
- 实际过程：已证5条加法accumulator交换；乘法交换子目标被LLM以定义不对称否定。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y (S z)) (add3acc x (S y) z)))；(forall ((y Nat) (z Nat)) (= (add3acc Z y (S z)) (add3acc y Z (S z))))；另3条。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x y z) (add3acc y x z)))。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (add3acc (mul3acc x y Z) z Z))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The function mul3acc is defined by an asymmetric accumulator recursion that treats the second and third arguments in structurally distinct branches (the (is-S (p y)) branch differs from the (is-S (p z
- 理想证明路线及改进：保留底层成功，验证乘法的构造子展开与小项IH；实际目标也是交换前两参，应由公式驱动。

#### standard/weird_nat_mul3acc_rrot — P1

- 日志：A/T/L/P=26/8/3/0; 1200.24s; timeout; H=10；失败节点 7。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_rrot/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_rrot/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_mul3acc_rrot/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc z x y)))))`
- 实际过程：successor搬移引理已证，主交换却进入两个被LLM否定的分支。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc (S x) y z) (add3acc x (S y) z)))；(forall ((x Nat) (y Nat) (z Nat)) (= (add3acc x (S y) z) (add3acc x y (S z))))；另1条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat)) (= (mul3acc x y z) (mul3acc x z y))) → mul3acc's recursive definition is not symmetric in its second
- 子节点否定记录（来源未必是solver反例）：mul3acc is defined by an asymmetric accumulator-style recursion; its commutativity (mul3acc x y z = mul3acc y x z) is not a consequence of the given axioms, and the only attempted helper (add3acc asso
- 理想证明路线及改进：不要把可证明的加法acc搬移直接套到乘法；用已证加法性质简化全S展开，再证明乘法置换。

#### standard/weird_nat_op_assoc — P2

- 日志：A/T/L/P=5/0/2/0; 1007.75s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_assoc/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_assoc/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_assoc/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (op (op a b Z Z) c d e) (op a (op b c Z Z) d e)))))`
- 实际过程：2条库含自反式及op Z Z Z e包装；一般代数关系没有进展。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat) (x2 Nat) (y2 Nat)) (= (op x y z x2) (op x y z x2)))；(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (op (op a b Z Z) c d e) (op (op a b Z Z) c d (op Z Z Z e))))。最近/代表性候选：(forall ((x Nat) (y Nat) (z Nat) (x2 Nat) (y2 Nat)) (= (op x y z x2) (op x y z x2)))；(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (op (op a b Z Z) c d e) (op (op a b Z Z) c d (op Z Z Z e))))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat)) (= (op (op a b Z Z) c d e) (op a (op b c Z Z) d e))) → Same as original goal
- 理想证明路线及改进：把op的四参递归整理为现有符号可表达的加法/乘法组合桥，先证明第三参/第四参successor搬移和二参乘积关系；无定义的plus不能凭空使用。

#### standard/weird_nat_op_assoc2 — P2

- 日志：A/T/L/P=7/1/2/1; 753.63s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_assoc2/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_assoc2/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_assoc2/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (a Nat) (b Nat) (c Nat) (d Nat)) (= (op (op x a a a) b c d) (op a (op b x b b) c d)))))`
- 实际过程：有op的acc分离桥，另有占位式forall ...；嵌套op目标尚无规范语义。 已证库关键片段：(forall ((x Nat) (y Nat) (z Nat) (acc Nat)) (= (op x y z acc) (op Z Z (op x y z Z) acc)))；(forall ((x Nat) (y Nat) (z Nat) (acc Nat)) (= (op Z y z acc) (ite (is-S z) (op Z y (p z) (S acc)) acc)))。最近/代表性候选：(forall ...)；(forall ((x Nat) (y Nat) (z Nat) (acc Nat)) (= (op Z y z acc) (ite (is-S z) (op Z y (p z) (S acc)) acc)))。
- 根节点筛除记录：(forall ((x Nat)(a Nat)(b Nat)(c Nat)(d Nat)) (= (op (op x a a a) b c d) (op a (op b x b b) c d))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：The commutativity claim fails. Counterexample: x=S Z, y=S(S Z), z=Z, acc=Z. The function evaluates to `y` when z < x, and to `x` when z < y (with x ≤ z or y ≤ z giving acc+z). Here left = op (S Z) (S(
- 理想证明路线及改进：沿已证acc分离继续提炼op组合的代数接口，类型/语法错在同一attempt修复，避免再换一个等价五变量根公式。

#### standard/weird_nat_op_comm_comm — P1

- 日志：A/T/L/P=6/1/0/0; 402.45s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_comm_comm/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_comm_comm/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_015055_autoproof/standard/weird_nat_op_comm_comm/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((a Nat) (b Nat) (c Nat) (d Nat)) (= (op a b c d) (op b a d c)))))`
- 实际过程：六次均主要生成与根等价的式子被筛掉，未进入有用性证明。 已证库关键片段：无已验证库引理。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((x Nat) (y Nat) (z Nat) (x2 Nat)) (= (op x y z x2) (op y x x2 z))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：The goal requires symmetry (commutativity) of the first two arguments of op, but op's defining axiom only recurses on its first (and third) argument; it never reduces on the second argument, so the re
- 理想证明路线及改进：要求给出具体constructor残差/参数转移关系，不允许只重排量词复述根目标；目标相同应标cycle/redundant而不是数学invalid。

### DTT（8题）
#### dtt-leon/amortize-queue-goal6 — P1；相对M2回退

- 日志：A/T/L/P=6/0/4/0; 668.02s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/amortize-queue-goal6/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/amortize-queue-goal6/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/amortize-queue-goal6/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((q Queue) (n Int)) (= (qlen (enqueue q n)) (+ 1 (qlen q)))) ))`
- 实际过程：M2成功；v5库已含len/append、len/qreva、len/qrev，但缺len非负与带域条件的plus后继律，未触发hint。 已证库关键片段：(forall ((x Lst) (y Lst)) (= (len (append x y)) (+ (len x) (len y))))；(forall ((x Lst) (y Lst)) (= (len (qreva x y)) (+ (len x) (len y))))；另2条。最近/代表性候选：(forall ((x Lst)) (= (len (qrev x)) (len x)))；(forall ((z Int) (y Lst)) (= (len (qrev (cons z y))) (+ 1 (len y))))。
- 理想证明路线及改进：从待用公理的前提反向生成len≥0，再证明有保护条件的plus(n,m+1)关系；不按函数名筛掉间接的plus/len依赖。本次已独立证成len非负和保护条件下的plus后继桥，但加入v5库后3秒根查询仍超时；不能计为已恢复。

#### dtt-clam/goal32 — P1；相对M2回退

- 日志：A/T/L/P=16/7/7/0; 1200.21s; timeout; H=1；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-clam/goal32/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-clam/goal32/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-clam/goal32/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Lst)) (= (rotate (len x) x) x)) ))`
- 实际过程：M2成功；rotate(len x)(append x y)=append y x 被LLM给出左右实际相等的伪反例否定。 已证库关键片段：(forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z))))；(forall ((x Lst)) (= (append x nil) x))；另5条。最近/代表性候选：(forall ((x Lst) (a Int) (w Lst)) (= (rotate (len x) (append x (cons a w))) (append (cons a w) x)))。
- 根节点筛除记录：(forall ((x Lst) (y Lst)) (= (rotate (len x) (append x y)) (append y x))) → The goal is false: with x = cons a nil and y = nil, len x = 1, so rotate 1 (append x nil) = rotate 1 (cons a nil) = rotate 0 (append nil (cons a nil)) = cons a nil, while append n…
- 子节点否定记录（来源未必是solver反例）：The goal is false: with x = cons a nil and y = nil, len x = 1, so rotate 1 (append x nil) = rotate 1 (cons a nil) = rotate 0 (append nil (cons a nil)) = cons a nil, while append nil (cons a nil) = con
- 已生成的solver hint：The previous attempts all try to prove a rotate/append identity directly by fixing a specific decomposed list. The goal (rotate (len x) x) = x is best reached by first establishing the two basic rotate laws, which are simple consequences of the axioms and are likely wh…
- 理想证明路线及改进：恢复广义append旋转桥；M2使用k≥0时rotate(k+len x)(append x w)=rotate k(append w x)，再取k=0。先核验反例，不重发根目标hint。

#### dtt-isa/goal47 — P1；相对M2回退

- 日志：A/T/L/P=6/0/2/0; 381.05s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal47/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal47/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal47/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((a Tree)) (= (height (mirror a)) (height a))) ))`
- 实际过程：M2成功；v5已证明带n,m≥0的nmax交换，但没有height≥0，0棵树、无hint。 已证库关键片段：(forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (nmax x y) (nmax y x))))；(forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (+ 1 (nmax x y)) (+ 1 (nmax y x)))))。最近/代表性候选：(forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (nmax x y) (nmax y x))))；(forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (+ 1 (nmax x y)) (+ 1 (nmax y x)))))。
- 根节点筛除记录：(forall ((a Tree)) (= (height (mirror a)) (height a))) → Same as original goal
- 理想证明路线及改进：补height≥0以解锁已有的带域保护nmax交换。本次3秒短验证中：非负引理独立证成；将其与v5已证库合并后根目标也unsat。通用机制是前提闭包，而非mirror专用hint。

#### dtt-isa/goal64 — P1

- 日志：A/T/L/P=6/0/4/0; 555.47s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal64/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal64/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal64/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((n Int) (xs Lst)) (=> (and (>= n 0) (less n (len xs)) ) (= (last (drop n xs)) (last xs)))) ))`
- 实际过程：库已含n<len时drop非空，以及drop非空时last保持；仍根未成。 已证库关键片段：(forall ((x Int) (y Lst)) (=> (not (= y nil)) (= (last (cons x y)) (last y))))；(forall ((n Int) (xs Lst)) (=> (and (>= n 0) (< n (len xs))) (not (= (drop n xs) nil))))；另2条。最近/代表性候选：(forall ((n Int) (xs Lst) (ys Lst)) (=> (and (>= n 0) (= (drop n xs) (cons (head (drop n xs)) ys)) (= ys nil)) (= (last (drop n xs)) (head (drop n xs)))))；(forall ((n Int) (xs Lst)) (=> (and (>= n 0) (not (= (drop n xs) nil))) (= (last (drop n xs)) (last xs))))。
- 理想证明路线及改进：完成less到内建<的条件桥、len非负，生成可实例化的两步组合；然后优先重试根，而非继续提出相近last等式。

#### dtt-isa/goal87 — P1

- 日志：A/T/L/P=19/3/5/3; 1056.45s; attempts_exhausted；失败节点 5。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal87/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal87/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-isa/goal87/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((xs Lst) (ys Lst)) (=> (= (len xs) (len ys)) (= (zip (rev xs) (rev ys)) (zrev (zip xs ys))))) ))`
- 实际过程：已有len/rev、zappend代数；zip的append-singleton候选先丢失等长条件，修正后仍有子目标否定传播。 已证库关键片段：(forall ((xs Lst) (ys Lst)) (= (len (append xs ys)) (+ (len xs) (len ys))))；(forall ((xs Lst)) (= (len (rev xs)) (len xs)))；另3条。最近/代表性候选：(forall ((xs Lst) (ys Lst) (x Int) (y Int)) (=> (= (len xs) (len ys)) (= (zip (append xs (cons x nil)) (append ys (cons y nil))) (zappend (zip xs ys) (zcons (mkpair x y) znil…；(forall ((a ZLst) (b ZLst)) (= (zrev (zappend a b)) (zappend (zrev b) (zrev a))))。
- 根节点筛除记录：(forall ((xs Lst) (ys Lst) (x Int) (y Int)) (= (zip (append xs (cons x nil)) (append ys (cons y nil))) (zappend (zip xs ys) (zcon… → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The proposed inductive helper lemmas for the zip/append/zappend property were all refuted as contradicting the given axioms, indicating the claimed zipping relationship does not follow from the provid
- 理想证明路线及改进：保留同步等长前提，先证zip(append xs[a],append ys[b])的zappend桥，再证明zrev/append和len/rev，沿单一依赖链合成。

#### dtt-leon/heap-goal10 — P1

- 日志：A/T/L/P=20/6/7/3; 1093.21s; attempts_exhausted；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal10/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal10/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal10/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Heap)) (=> (hasLeftistProperty x) (= (len (heapsorta x)) (hsize x)))) ))`
- 实际过程：hsize非负、merge/mergea大小等已证；heapsorta递归子目标因要用祖先性质而被判invalid。 已证库关键片段：(forall ((h Heap)) (>= (hsize h) 0))；(forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus n m) (plus m n))))；另5条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((l Heap) (r Heap)) (= (len (heapsorta (merge l r))) (plus (len (heapsorta l)) (len (heapsorta r))))) → The goal is missing the necessary `hasLeftistProperty` invariant; `len (heapsorta h) = hsize h` is false for arbitrary heaps, and the only fix is the strict ancestor A0 which cann…
- 子节点否定记录（来源未必是solver反例）：The CURRENT goal is the induction step of ancestor A0 `(forall ((x Heap)) (=> (hasLeftistProperty x) (= (len (heapsorta x)) (hsize x))))`; it cannot be proved without invoking A0 on the subtrees `l` a
- 理想证明路线及改进：证明merge保持leftist及size严格下降，在较小堆上合法应用IH；库增长后优先完成父级，不再把整个heapsorta大小命题写成child。

#### dtt-leon/heap-goal12 — P1

- 日志：A/T/L/P=41/19/9/6; 1200.51s; timeout; H=12；失败节点 6。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal12/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal12/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal12/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Heap) (l Lst) (v Int)) (= (len (qheapsorta x (cons v l))) (+ 1 (len (qheapsorta x l))))) ))`
- 实际过程：41次生成19棵树、6个子目标成功；曾出现自由v和len(Heap)类型错误。根题本身不带leftist前提。 已证库关键片段：(forall ((n Int) (m Int) (p Int)) (=> (and (>= n 0) (>= m 0) (>= p 0)) (= (plus (plus n m) p) (plus n (plus m p)))))；(forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus (+ 1 n) m) (+ 1 (plus n m)))))；另7条。最近/代表性候选：(forall ((a Heap) (b Heap)) (= (len (qheapsorta (merge a b) (cons v nil))) (+ 1 (len (qheapsorta (merge a b) nil)))))；(forall ((h Heap) (y Lst)) (= (len (merge h hleaf)) (hsize h)))。
- 根节点筛除记录：(forall ((h Heap) (a Lst) (b Int)) (= (len (qheapsorta h (cons b a))) (+ 1 (len (qheapsorta h a))))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：the goal is not independently provable by any non-ancestor lemma; it is the merge-specialization of ancestor A1 combined with library lemma lib_8, and its only useful helper is the strict ancestor A1,
- 理想证明路线及改进：先拦截作用域/类型错；围绕qheapsorta的列表acc增量做泛化证明。不要把heap10/13的leftist前提盲目加到本题从而只证弱化目标。

#### dtt-leon/heap-goal13 — P1

- 日志：A/T/L/P=6/0/1/0; 665.78s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal13/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal13/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_025851_dtt/dtt-leon/heap-goal13/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((l Lst) (x Heap)) (=> (hasLeftistProperty x) (= (len (qheapsorta x l)) (plus (hsize x) (len l))))) ))`
- 实际过程：只收集到plus局部后继关系，未形成hsize/len域闭包或qheapsorta累积不变量。 已证库关键片段：(forall ((a Int) (b Int) (c Int)) (=> (and (>= a 0) (>= b 0) (>= c 0)) (= (plus a (+ 1 b)) (plus (+ 1 a) b))))。最近/代表性候选：(forall ((h1 Heap) (h2 Heap)) (= (hsize (merge h1 h2)) (plus (hsize h1) (hsize h2))))；(forall ((k Int) (v Int) (l Heap) (r Heap) (x Lst)) (=> (hasLeftistProperty (heap k v l r)) (= (len (qheapsorta (heap k v l r) x)) (plus (hsize (heap k v l r)) (len x)))))。
- 根节点筛除记录：(forall ((a Int) (b Int) (c Int)) (= (plus (plus a b) c) (plus (+ 1 a) (+ b c)) )) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：先验证度量非负、merge大小与不变量，再证明len(qheapsorta h l)=plus(hsize h,len l)的合法递归步；按前提依赖组织候选。

### ind-ben（10题）
#### generated_add_24sym/0 — P1

- 日志：A/T/L/P=6/0/8/0; 603.65s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/nat/generated_add_24sym/0/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/nat/generated_add_24sym/0/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/nat/generated_add_24sym/0/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((v0 nat) (v1 nat) (v2 nat) (v3 nat) (v4 nat) (v5 nat) (v6 nat) (v7 nat) (v8 nat)) (= (add (add (add (s zero) (add (s (add (s v6) v7)) (add v3 (s v4)))) (s (s (s v2)))) (s (add (s (add (s v1) v8)) (s (add (s v5) (add (s v4) v0)))))) (s (s (add (add (s (s (s …`
- 实际过程：已有8条add结合/后继展开与单位，但缺交换律；巨型表达式仍直接交给LLM比较。 已证库关键片段：(forall ((x nat) (y nat) (z nat)) (= (add (add x y) z) (add x (add y z))))；(forall ((x nat)) (= (add x zero) x))；另6条。最近/代表性候选：(forall ((x nat) (y nat)) (= (add (s x) y) (s (add x y))))；(forall ((x nat) (y nat) (z nat)) (= (add (add x y) (s z)) (s (add (add x y) z))))。
- 根节点筛除记录：(forall ((v0 nat) (v1 nat) (v2 nat) (v3 nat) (v4 nat) (v5 nat) (v6 nat) (v7 nat) (v8 nat)) (= (add (add (add (s zero) (add (s (ad… → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：先证add交换，再在已证AC下做有证明依据的扁平化/排序/后继计数规范化；不能对任意符号默认AC。

#### crafted_rotate/0 — P1

- 日志：A/T/L/P=6/0/5/0; 639.47s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/0/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/0/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/0/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (flatten0 (rotateLeft x)) (flatten0 x)) )))`
- 实际过程：已证app结合与单步中序重括号；缺递归rotateLeft全局不变式。 已证库关键片段：(forall ((l list) (m list) (n list)) (= (app (app l m) n) (app l (app m n))))；(forall ((p tree) (a nat) (q tree) (b nat) (r tree)) (= (flatten0 (node (node p a q) b r)) (flatten0 (node p a (node q b r)))))；另3条。最近/代表性候选：(forall ((p tree) (a nat) (q tree) (b nat) (r tree)) (= (flatten0 (node (node p a q) b r)) (app (app (flatten0 p) (cons a (flatten0 q))) (cons b (flatten0 r)))))；(forall ((p tree) (a nat) (q tree) (b nat) (r tree)) (= (flatten0 (node p a (node q b r))) (app (flatten0 p) (cons a (app (flatten0 q) (cons b (flatten0 r)))))))。
- 理想证明路线及改进：区分单次rotation与反复rotateLeft：按右脊节点数下降（可由定义提出度量）做良基归纳，局部中序等式提供语义保持。

#### crafted_even/1 — P1

- 日志：A/T/L/P=57/27/29/12; 1201.43s; timeout; H=2；失败节点 15。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/nat/crafted_even/1/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/nat/crafted_even/1/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/nat/crafted_even/1/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x nat) (y nat)) (=> (or (even x) (even y)) (even (mul x y))) )))`
- 实际过程：M2成功；v557次生成27棵树、29条库，仍把偶数乘积子目标经错误推演判invalid。 已证库关键片段：(forall ((x nat) (y nat)) (= (add (s (s x)) y) (s (s (add x y)))))；(forall ((n nat) (y nat)) (=> (even n) (even (add (add n y) y))))；另27条。最近/代表性候选：(forall ((x nat) (y nat)) (=> (even x) (even (mul x y))))。
- 根节点筛除记录：(forall ((x nat) (y nat)) (=> (even x) (even (add x y)))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal is false: e.g. x = s(s(zero)) is even, but mul x y = add (mul (s zero) y) y = add (add (mul zero y) y) y = add (add zero y) y = add y y, and y = s(zero) gives add (s(zero)) (s(zero)) = s (add
- 理想证明路线及改进：M2有even(add a b)=(even a=even b)及mul后继奇偶桥；优先证明这个观察层代数，按两个析取前提分别关闭乘积偶性。

#### crafted_rotate/1 — P1；相对M2回退

- 日志：A/T/L/P=13/6/4/0; 1201.41s; timeout；失败节点 7。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/1/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/1/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/1/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (flatten2 (rotateLeft x) nil) (flatten0 x)) )))`
- 实际过程：flatten2 t acc=app(flatten0 t,acc)已证；子目标仍被LLM声称rotateLeft缺constructor定义而放弃。 已证库关键片段：(forall ((xs list) (ys list) (zs list)) (= (app (app xs ys) zs) (app xs (app ys zs))))；(forall ((t tree) (r list)) (= (flatten2 t r) (app (flatten0 t) r)))；另2条。最近/代表性候选：(forall ((xs tree) (y nat) (ys list)) (= (flatten2 (rotateLeft xs) (cons y ys)) (app (flatten0 xs) (cons y ys))))；(forall ((xs list) (ys list) (zs list)) (= (app (app xs ys) zs) (app xs (app ys zs))))。
- 子节点否定记录（来源未必是solver反例）：rotateLeft has no axiom covering (node (node p x q) y Nil), so flatten0(rotateLeft(node p x q)) = flatten0(node p x q) is not derivable; the goal is unprovable from the given axioms.
- 理想证明路线及改进：先修树/list参数类型混用，利用累积桥将问题规约到rotateLeft中序保持；校验完整构造子覆盖后建立良基证明，不重复flatten2桥。

#### crafted_assorted/18 — P2

- 日志：A/T/L/P=6/0/3/0; 606.06s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/list/crafted_assorted/18/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/list/crafted_assorted/18/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/list/crafted_assorted/18/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((xs lst)) (=> (and (= (rev xs) xs) (exists ((k nat)) (= (len xs) (s (mul (s (s zero)) k))))) (exists ((mid nat)) (and (exists ((k nat)) (= (cnt xs mid) (s (mul (s (s zero)) k)))) (forall ((x nat)) (=> (not (= x mid)) (exists ((k nat)) (= (cnt xs x) (mul (s …`
- 实际过程：已生成exists形式，不能说系统不会提出存在引理；一些候选把head当奇数出现次数的唯一元素。 已证库关键片段：(forall ((x lst) (y lst)) (= (len (app x y)) (add (len x) (len y))))；(forall ((x lst)) (= (len (rev x)) (len x)))；另1条。最近/代表性候选：(forall ((xs lst)) (=> (and (= (rev xs) xs) (exists ((k nat)) (= (len xs) (s (mul (s (s zero)) k))))) (forall ((x nat)) (=> (not (= x (get xs zero))) (exists ((k nat)) (= (cn…；(forall ((xs lst)) (=> (= (rev xs) xs) (= (get xs zero) (get (rev xs) zero))))。
- 根节点筛除记录：(forall ((x lst) (y lst) (z nat)) (= (cnt (app x y) z) (add (cnt x z) (cnt y z)))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：需要中间元素见证及回文首尾配对分解，沿配对归纳维护其余元素偶计数；先检查cnt的具体参数/定义。属需要见证构造的新能力，不是文本hint微调。

#### crafted_rotate/2 — P1；相对M2回退

- 日志：A/T/L/P=6/0/5/0; 565.49s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/2/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/2/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/2/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (flatten0 (rotateRight x)) (flatten0 x)) )))`
- 实际过程：M2成功且v5无hint；5条库有局部rotateRight/flatten展开，没有覆盖全node的保持引理。 已证库关键片段：(forall ((l1 list) (l2 list) (l3 list)) (= (app (app l1 l2) l3) (app l1 (app l2 l3))))；(forall ((p tree) (x nat) (q tree) (y nat) (r tree)) (= (flatten0 (node (node p x q) y r)) (flatten0 (node p x (node q y r)))))；另3条。最近/代表性候选：(forall ((p tree) (x nat) (q tree) (y nat) (r tree)) (= (flatten0 (rotateRight (node p x (node q y r)))) (flatten0 (rotateRight (node (node p x q) y r)))))；(forall ((p tree) (x nat) (q tree)) (= (flatten0 (node p x q)) (app (flatten0 p) (cons x (flatten0 q)))))。
- 根节点筛除记录：(forall ((p tree) (x nat)) (= (flatten0 (node p x Nil)) (flatten0 (node Nil x p)))) → contradicts axioms (cvc=unsat)
- 理想证明路线及改进：M2已证明flatten0(rotateRight(node p x q))=flatten0(node p x q)；用constructor-case/frontier推进这条并确保合法递归，而不是继续增加重括号式。

#### crafted_rotate/4 — P1

- 日志：A/T/L/P=13/2/8/2; 842.02s; attempts_exhausted；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/4/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/4/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/4/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (flatten0 (rotateLeft x)) (flatten2 x nil)) )))`
- 实际过程：flatten2/flatten0完整桥已入库，8条库仍在两个rotateLeft嵌套node的保持式间切换；最终NO_ACTION。 已证库关键片段：(forall ((l list) (m list) (n list)) (= (app (app l m) n) (app l (app m n))))；(forall ((t tree) (r list)) (= (flatten2 t r) (app (flatten0 t) r)))；另6条。最近/代表性候选：(forall ((p tree) (x nat) (q tree) (y nat) (r tree)) (= (flatten0 (rotateLeft (node p x (node q y r)))) (flatten0 (node p x (node q y r)))))；(forall ((p tree) (x nat) (q tree) (y nat) (r tree)) (= (flatten0 (rotateLeft (node (node p x q) y r))) (flatten0 (node (node p x q) y r))))。
- 理想证明路线及改进：冻结已完成flatten连接，只保留rotateLeft保持为活动缺口；父目标重试与分支覆盖检查优于再复活等价节点。

#### crafted_rotate/5 — P1

- 日志：A/T/L/P=29/23/7/1; 1200.26s; timeout; H=5；失败节点 4。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/5/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/5/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/5/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (flatten2 (rotateLeft x) nil) (flatten2 x nil)) )))`
- 实际过程：7条库含acc泛化和rotation相容；LLM错误声称rotateLeft在左子树为node时没有定义。 已证库关键片段：(forall ((xs list) (ys list) (zs list)) (= (app (app xs ys) zs) (app xs (app ys zs))))；(forall ((t tree) (r list)) (= (flatten2 t r) (app (flatten2 t nil) r)))；另5条。最近/代表性候选：(forall ((p tree) (x nat) (q tree) (y nat) (r tree) (acc list)) (= (flatten2 (rotateLeft (node (node p x q) y r)) acc) (flatten2 (node p x (node q y r)) acc)))；(forall ((p tree) (x nat) (q tree) (y nat) (r tree) (acc list)) (= (flatten2 (node (node p x q) y r) acc) (flatten2 (node p x (node q y r)) acc)))。
- 根节点筛除记录：(forall ((p tree) (x nat) (q tree)) (= (flatten2 (rotateLeft (node p x q)) nil) (flatten2 (node p x q) nil))) → The rotateLeft function is under-specified — no axiom reduces `rotateLeft (node (node p x q) y r)` (where the left child is a node), so a model can assign it an arbitrary value (e…
- 子节点否定记录（来源未必是solver反例）：The rotateLeft function is under-specified — no axiom reduces `rotateLeft (node (node p x q) y r)` (where the left child is a node), so a model can assign it an arbitrary value (e.g. Nil), making the
- 已生成的solver hint：The library already contains the key rotateLeft restructuring axiom and the flatten2/rotateLeft commutation lemma. The remaining gap is the base case: for a tree whose right child is a leaf, rotateLeft is identity and flatten2 is unchanged. The revival candidates all s…
- 理想证明路线及改进：构造子覆盖按右子树Nil/node完整检查即可驳回该解释；随后对右脊下降证明任意acc下的flatten2保持，不能把全式否定写回父节点。

#### crafted_rotate/6 — P1；相对M2回退

- 日志：A/T/L/P=23/15/13/4; 1200.14s; timeout; H=7；失败节点 6。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/6/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/6/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/6/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (flatten0 (rotateRight x)) (flatten2 x nil)) )))`
- 实际过程：M2成功；v5已有13条库、4个子目标成功，含flatten2/flatten0及两个rotateRight分支连接，却总时限失败。 已证库关键片段：(forall ((l list) (m list) (r list)) (= (app (app l m) r) (app l (app m r))))；(forall ((a nat) (l list) (r list)) (= (app (cons a l) r) (cons a (app l r))))；另11条。最近/代表性候选：无可复用失败候选。
- 理想证明路线及改进：这是组合/调度近成功题：统一等式方向、检查分支覆盖后以完整库早重试根；缓存已证节点，避免重复两个flatten方向。

#### crafted_rotate/8 — P1

- 日志：A/T/L/P=16/6/8/0; 1089.59s; attempts_exhausted; H=6；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/8/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/8/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_033050_ind-ben/tree/crafted_rotate/8/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x tree)) (= (size (rotateLeft x)) (size x)) )))`
- 实际过程：size构造子与重括号、add代数已证；一般node的size保持仅因难证被记invalid。 已证库关键片段：(forall ((a nat) (b nat) (c nat)) (= (add (add a b) c) (add a (add b c))))；(forall ((a nat) (b nat)) (= (add a (s b)) (s (add a b))))；另6条。最近/代表性候选：(forall ((p tree) (x nat)) (= (size (rotateLeft (node p x Nil))) (size (node p x Nil))))；(forall ((p tree) (v nat) (q tree) (w nat) (r tree)) (= (size (rotateLeft (node (node p v q) w r))) (size (node (node p v q) w r))))。
- 根节点筛除记录：(forall ((p tree) (v nat) (q tree)) (= (size (rotateLeft (node p v q))) (size (node p v q)))) → The current goal (forall ((p tree) (v nat) (q tree)) (= (size (rotateLeft (node p v q))) (size (node p v q)))) is not provable from the given axioms. The rotateLeft function is de…
- 子节点否定记录（来源未必是solver反例）：The current goal (forall ((p tree) (v nat) (q tree)) (= (size (rotateLeft (node p v q))) (size (node p v q)))) is not provable from the given axioms. The rotateLeft function is defined recursively but
- 已生成的solver hint：The library already proves the Nil case and the top-level rotateLeft unfolding equality for size. The missing step for the general goal is the size preservation under the outer rotateLeft recursion when the right child is again a node: the rotateLeft axiom rewrites (no…
- 理想证明路线及改进：先形成单步size不变，再对rotateLeft终止度量归纳；需程序计算残差与较小递归目标，不要只复活同一node命题。

### vmcai15-dt（12题）
#### leon/bsearch-tree-goal4 — P1

- 日志：A/T/L/P=6/0/6/0; 610.44s; attempts_exhausted；失败节点 0。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/bsearch-tree-goal4/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/bsearch-tree-goal4/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/bsearch-tree-goal4/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((t Tree) (n Nat)) (leq (tsize (tremove t n)) (tsize t)) )))`
- 实际过程：库有leq/plus单调与节点size比较，但没有删除分支大小关系，root0树。 已证库关键片段：(forall ((a Nat) (b Nat) (c Nat)) (=> (leq a b) (leq (plus c a) (plus c b))))；(forall ((a Nat) (b Nat)) (=> (leq a b) (leq (succ a) (succ b))))；另4条。最近/代表性候选：(forall ((d Nat) (l Tree) (r Tree) (i Nat) (l2 Tree)) (=> (leq (tsize l2) (tsize l)) (leq (tsize (node d l2 r)) (tsize (node d l r)))))；(forall ((d Nat) (l Tree) (r Tree) (i Nat) (r2 Tree)) (=> (leq (tsize r2) (tsize r)) (leq (tsize (node d l r2)) (tsize (node d l r)))))。
- 根节点筛除记录：(forall ((t Tree) (n Nat)) (leq (tsize (tremove t n)) (tsize t))) → Same as original goal
- 理想证明路线及改进：按tremove实际分支提取左右子树大小下降/重建单调；补leq传递与plus上下文单调，然后闭合constructor归纳。

#### leon/bsearch-tree-goal5 — P1；相对M2回退

- 日志：A/T/L/P=20/13/2/0; 1132.14s; attempts_exhausted; H=5；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/bsearch-tree-goal5/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/bsearch-tree-goal5/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/bsearch-tree-goal5/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((l Lst) (t Tree)) (leq (tsize (tremove-all t l)) (tsize t)) )))`
- 实际过程：单次tremove大小不增已入库；less/leq传递被LLM说不成立，M2成功库恰含这两条。 已证库关键片段：(forall ((a Nat) (b Nat)) (= (less (succ a) (succ b)) (less a b)))；(forall ((t Tree) (n Nat)) (leq (tsize (tremove t n)) (tsize t)))。最近/代表性候选：(forall ((t Tree) (n Nat)) (leq (tsize (tremove t n)) (tsize t)))；(forall ((l Lst) (t Tree) (n Nat)) (leq (tsize (tremove-all (tremove t n) l)) (tsize (tremove t n))))。
- 根节点筛除记录：(forall ((a Nat) (b Nat) (c Nat)) (=> (and (leq a b) (leq b c)) (leq a c))) → the goal requires transitivity of "less", which is not derivable from the given axioms (only A1-A3 define "less"); the corresponding child lemma was marked invalid.
- 子节点否定记录（来源未必是solver反例）：The goal requires transitivity of `leq` (chaining `leq (tsize (tremove-all ...)) (tsize (tremove t n))` with `leq (tsize (tremove t n)) (tsize t)`), which depends on transitivity of `less` — exactly t
- 已生成的solver hint：The library already has the per-element bound (forall ((t Tree) (n Nat)) (leq (tsize (tremove t n)) (tsize t))). The remaining gap is chaining leq along the list recursion of tremove-all, which needs transitivity of less/leq. The historical candidates on less-transitiv…
- 理想证明路线及改进：反例必须验证；恢复leq传递并对删除列表归纳，组合两次不等式。此题是经验继承应优先检索关系闭包的强案例。

#### isa/goal55 — P1；相对M2回退

- 日志：A/T/L/P=25/12/6/0; 1201.50s; timeout; H=8；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal55/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal55/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal55/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((i Nat) (j Nat) (k Nat)) (= (minus (minus i j) k) (minus (minus i k) j)) )))`
- 实际过程：M2成功；v5多为minus末尾zero包装，hint复活successor形式的整个交换目标；plus在当前理论不可用。 已证库关键片段：(forall ((n Nat) (m Nat)) (= (minus (minus n (succ m)) zero) (minus (minus n zero) (succ m))))；(forall ((n Nat) (m Nat)) (= (minus (succ n) (succ m)) (minus n m)))；另4条。最近/代表性候选：(forall ((n Nat)) (= (minus n zero) n))；(forall ((n Nat) (m Nat)) (= (minus (minus n (succ m)) zero) (minus n (succ m))))。
- 根节点筛除记录：(forall ((n Nat) (m Nat) (p Nat)) (= (minus (minus n m) p) (minus (minus n p) m))) → Same as original goal
- 子节点否定记录（来源未必是solver反例）：The goal (minus (minus n (succ m)) p) = (minus (minus n p) (succ m)) requires swapping the order of two successive subtractions, but the only axioms (A1,A2,A3) give no commutativity/reassociation for
- 已生成的solver hint：The goal is a subtraction-order swap. The library now has the succ-step axiom and the zero-right axiom for minus, so re-try the succ-form of the swap (the historical unproved candidate), which is the direct step case needed to induct on the second argument of the inner…
- 理想证明路线及改进：M2关键是minus(minus a b)(succ c)=minus(minus a(succ b))c的successor转移桥。用现有minus关系修订候选，不引入无定义plus。

#### nosg/goal62 — P1

- 日志：A/T/L/P=17/7/7/1; 1200.23s; timeout; H=4；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal62/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal62/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal62/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Lst) (y Nat)) (=> (sorted x) (sorted (insort y x))) )))`
- 实际过程：已证sorted-tail、less/leq及部分插入分支，缺完整head下界/递归tail闭合；诊断中还有错误插入顺序。 已证库关键片段：(forall ((x Nat) (y Nat)) (=> (not (less x y)) (leq y x)))；(forall ((z Nat) (w Lst)) (=> (sorted (cons z w)) (sorted w)))；另5条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((a Nat) (y Nat) (x Lst)) (=> (sorted (cons a x)) (leq a (head (insort y x))))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The goal is falsifiable — e.g. take y greater than z (with a ≤ z), then insort y (cons z w) puts y before z, and since a ≤ z but not necessarily a ≤ y, the result may have a before y and y before z, v
- 理想证明路线及改进：分离插入前后两分支：less时直接cons，另一分支用tail的合法IH与head(insort)下界；不把sorted-insort祖先原样当库公理。

#### isa/goal74 — P1

- 日志：A/T/L/P=33/26/15/12; 1203.03s; timeout; H=1；失败节点 12。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal74/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal74/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal74/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((i Nat) (xs Lst)) (= (rev (drop i xs)) (take (minus (len xs) i) (rev xs))) )))`
- 实际过程：33次生成26棵树、12个子目标成功；len(rev)=len因某种plus证明路线不可用被判invalid。 已证库关键片段：(forall ((xs Lst) (ys Lst)) (= (take (len xs) (append xs ys)) xs))；(forall ((n Nat) (xs Lst) (ys Lst)) (= (take n (append xs ys)) (append (take n xs) (take (minus n (len xs)) ys))))；另13条。最近/代表性候选：(forall ((xs Lst) (ys Lst)) (= (take (len xs) (append xs ys)) xs))；(forall ((n Nat) (xs Lst) (ys Lst)) (= (take n (append xs ys)) (append (take n xs) (take (minus n (len xs)) ys))))。
- 根节点筛除记录：(forall ((xs Lst)) (= (len (rev xs)) (len xs))) → proving (len (rev xs)) = (len xs) requires the length-of-append property (len (append xs ys)) = (len xs) + (len ys), but the function "plus" used to express addition is only decla…
- 子节点否定记录（来源未必是solver反例）：proving (len (rev xs)) = (len xs) requires the length-of-append property (len (append xs ys)) = (len xs) + (len ys), but the function "plus" used to express addition is only declared with no defining
- 理想证明路线及改进：保存take/drop/append边界条件，改用singleton-append的len后继桥证明rev长度；一种证明路线缺符号不意味着命题为假。父目标收尾须保留预算。

#### isa/goal76 — P1

- 日志：A/T/L/P=10/2/4/4; 734.22s; attempts_exhausted；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal76/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal76/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal76/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((i Nat) (xs Lst)) (= (rev (take i xs)) (drop (minus (len xs) i) (rev xs))) )))`
- 实际过程：len/rev等4条pin已证；drop/append singleton 的有界桥尚未闭合，曾因少边界前提被否定。 已证库关键片段：(forall ((x Nat) (p Lst) (q Lst)) (= (len (append p (cons x q))) (succ (len (append p q)))))；(forall ((p Lst)) (= (len (append p nil)) (len p)))；另2条。最近/代表性候选：(forall ((ys Lst)) (= (len (rev ys)) (len ys)))；(forall ((i Nat) (xs Lst)) (= (take i (rev xs)) (rev (drop (minus (len xs) i) xs))))。
- 根节点筛除记录：(forall ((k Nat) (ys Lst) (x Nat)) (= (drop k (append ys (cons x nil))) (append (drop k ys) (cons x nil)))) → contradicts axioms (cvc=unsat)
- 子节点否定记录（来源未必是solver反例）：The identity (take i xs) = (rev (drop (minus (len xs) i) (rev xs)))
- 理想证明路线及改进：针对i≤len和i>len分支分别证明drop-append桥，复用已证len/rev；避免在对偶take-rev目标之间来回递归。

#### nosg/goal8 — P1；相对M2回退

- 日志：A/T/L/P=16/9/3/1; 1200.23s; timeout; H=1；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal8/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal8/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal8/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat) (z Lst)) (= (drop x (drop y z)) (drop y (drop x z))) )))`
- 实际过程：M2成功；v5库有drop successor转移但还有自反式，尚缺完成组合的单步drop桥。 已证库关键片段：(forall ((x Nat) (y Nat)) (= (drop (succ x) (drop (succ y) nil)) (drop (succ y) (drop (succ x) nil))))；(forall ((x Nat) (y Nat) (z Lst)) (= (drop (succ x) (drop y z)) (drop (succ x) (drop y z))))；另1条。最近/代表性候选：无可复用失败候选。
- 子节点否定记录（来源未必是solver反例）：The goal fails when x=zero: LHS reduces to drop y' w while RHS reduces to drop (succ y') w, which differ (e.g., x=zero, y=succ zero, z=cons a nil gives drop zero (cons a nil) = cons a nil vs drop (suc
- 理想证明路线及改进：沿M2的drop(succ a)w=drop a(drop1 w)、drop1(drop b w)=drop(succ b)w构建可合成桥；不只复活整个双drop交换。

#### isa/goal80 — P1；相对M2回退

- 日志：A/T/L/P=21/15/7/3; 1201.38s; timeout; H=2；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal80/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal80/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/isa/goal80/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((l Lst)) (sorted (sort l)) )))`
- 实际过程：M2成功；v5已有头部界和sorted-tail，但子节点被说“插入可能破坏sorted”。 已证库关键片段：(forall ((i Nat) (x Nat) (y Lst)) (=> (and (= (sorted (cons x y)) true) (not (less i x))) (= (leq x i) true)))；(forall ((x Nat) (y Nat)) (=> (not (less x y)) (leq y x)))；另5条。最近/代表性候选：无可复用失败候选。
- 子节点否定记录（来源未必是solver反例）：the remaining obligation (sorted (insort i y)) = true requires (leq (head y) i), which is not implied by the hypotheses (= (sorted (cons x y)) true) and (leq x i); x and (head y) are unrelated, so the
- 理想证明路线及改进：用程序生成带 sorted(insort i tail) 的合法归纳步，然后组合已证head界。必须保留IH作用域，不能无条件引用当前祖先定理。

#### nosg/goal84 — P1；相对M2回退

- 日志：A/T/L/P=40/37/3/0; 1201.42s; timeout; H=9；失败节点 3。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal84/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal84/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/clam/nosg/goal84/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Nat) (y Nat)) (= (mult (fac x) y) (qfac x y)) )))`
- 实际过程：40次生成37棵树、0个子目标成功，库仅乘零与plus交换；M2有乘法交换、分配、结合。 已证库关键片段：(forall ((n Nat)) (= (mult n zero) zero))；(forall ((n Nat) (m Nat)) (= (mult (plus n m) zero) zero))；另1条。最近/代表性候选：无可复用失败候选。
- 子节点否定记录（来源未必是solver反例）：The goal asserts commutativity of `mult`, but the recursive definition only unfolds `mult` on its first argument. No axioms establish commutativity (e.g., no commutativity of `plus` or helper lemma fo
- 理想证明路线及改进：证明qfac累积不变量真正需要的是乘法重括号；建立plus基础→mult分配→mult结合的里程碑链，阻断qfac等价变体扩张。

#### leon/heap-goal10 — P1

- 日志：A/T/L/P=36/23/6/2; 1203.28s; timeout; H=10；失败节点 7。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal10/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal10/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal10/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Heap)) (=> (hasLeftistProperty x) (= (len (heapsorta x)) (hsize x))) )))`
- 实际过程：库已有merge大小及leftist保持，36次生成23棵树却只有2个child成功。 已证库关键片段：(forall ((k Nat) (v Nat) (l Heap) (r Heap)) (=> (hasLeftistProperty (heap k v l r)) (= (hsize (heap k v l r)) (succ (plus (hsize l) (hsize r))))))；(forall ((l Heap) (r Heap)) (=> (and (hasLeftistProperty l) (hasLeftistProperty r)) (= (hsize (merge l r)) (plus (hsize l) (hsize r)))))；另4条。最近/代表性候选：无可复用失败候选。
- 根节点筛除记录：(forall ((l Heap) (r Heap)) (=> (and (hasLeftistProperty l) (hasLeftistProperty r)) (= (len (heapsorta (merge l r))) (hsize (merg… → The goal (len (heapsorta (merge l r))) = (hsize (merge l r)) requires the mergea invariant (len (heapsorta (mergea v x y))) = succ(plus (hsize x)(hsize y)), which was already trie…
- 子节点否定记录（来源未必是solver反例）：The goal (len (heapsorta (merge l r))) = (hsize (merge l r)) requires the mergea invariant (len (heapsorta (mergea v x y))) = succ(plus (hsize x)(hsize y)), which was already tried (L1_1_1) and failed
- 理想证明路线及改进：以size下降验证对merge后较小堆的IH，再合成heapsorta长度；不需要额外猜一个与目标等价的mergea全局定理。

#### leon/heap-goal12 — P1

- 日志：A/T/L/P=12/3/5/0; 1202.42s; timeout; H=1；失败节点 2。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal12/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal12/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal12/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((x Heap) (l Lst) (v Nat)) (=> (hasLeftistProperty x) (= (len (qheapsorta x (cons v l))) (succ (len (qheapsorta x l))))) )))`
- 实际过程：库已有merge大小/保持，但qheapsorta cons-acc长度桥依然未证。 已证库关键片段：(forall ((n Nat) (m Nat)) (= (plus n (succ m)) (succ (plus n m))))；(forall ((n Nat) (m Nat) (p Nat)) (= (plus (plus n m) p) (plus n (plus m p))))；另3条。最近/代表性候选：无可复用失败候选。
- 理想证明路线及改进：对堆的递归下降泛化acc，同时保留leftist前提；证明局部递归步，避免把acc增量桥仅改名为子目标。

#### leon/heap-goal13 — P1

- 日志：A/T/L/P=25/14/7/0; 1200.18s; timeout; H=1；失败节点 5。目标：[SMT根目标](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal13/template.smt2>)；[失败引理/求解器记录](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal13/failed_lemmas.json>)；[完整提示及生成过程](<//wsl.localhost/Ubuntu/home/tsc/LLM4Ind/experiments/results/ours_full706_deepseekv4flash_cvc5_full_default_llmhint_v5_nohd_noadv_p20_nothink/20260927_040411_vmcai15-dt/leon/heap-goal13/llm_prompts.txt>)。
- 目标概要：`(assert (not (forall ((l Lst) (x Heap)) (=> (hasLeftistProperty x) (= (len (qheapsorta x l)) (plus (hsize x) (len l)))) )))`
- 实际过程：已证qheapsorta对cons acc的长度增加1；仍缺acc=nil基线与堆大小连接，诊断把缺桥当假。 已证库关键片段：(forall ((a Nat) (b Nat)) (= (plus a (succ b)) (succ (plus a b))))；(forall ((m Nat) (n Nat)) (= (plus m n) (plus n m)))；另5条。最近/代表性候选：(forall ((m Nat) (n Nat)) (= (plus m n) (plus n m)))；(forall ((a Nat) (b Nat) (c Nat)) (= (plus (plus a b) c) (plus a (plus b c))))。
- 根节点筛除记录：(forall ((x Heap) (y Heap) (l Lst)) (=> (and (hasLeftistProperty x) (hasLeftistProperty y)) (= (len (qheapsorta (merge x y) l)) (… → The goal is not a theorem of the given axioms. The only counting axiom for qheapsorta is (lib_7) which handles an explicit cons argument: len(qheapsorta h (cons v l)) = succ(len(q…
- 子节点否定记录（来源未必是solver反例）：The axioms only provide the incremental counting property len(qheapsorta h (cons v l)) = succ(len(qheapsorta h l)) (lib_7) and never connect len(qheapsorta h l) to hsize(h)+len(l) for arbitrary l or f
- 已生成的solver hint：The goal is exactly a generalised qheapsorta-length theorem, so the proof should proceed by the qheapsorta recursion on the heap, using the NEW library lemma len(qheapsorta h (cons v l)) = succ(len(qheapsorta h l)) and the merge size/hLeftist lemmas. The candidate (for…
- 理想证明路线及改进：先证明qheapsorta(h,nil)的长度基线（或与heapsorta的可验证连接），再借已证acc增量与plus递推完成一般acc。

## 7. 复核边界

根目标/已证库/尝试统计以本轮目录为准。失败库里的candidate只是“未证或timeout”，不表示为真；LLM无效理由不是cvc5反例。输入修复后的短测试不改变CSV成绩。建议复现时保存规范化SMT输入并用同样的查询修复baseline与v5，然后重新跑全部多profile证明。报告中对未知结果明确标为候选改进，未作恢复率外推。
