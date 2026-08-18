import re
import logging
import sys
import json
import itertools
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Tuple, Optional, Dict, Any
from logger_config import setup_colored_logger
from env_config import setup_environment, setup_model
from vampire_runner import (
    run_vampire_with_timeout,
    run_vampire,
    run_vampire_diagnostic,
    compute_progress_score,
    derive_repair_hints,
    VampireResult,
)

# 配置彩色日志
logger = setup_colored_logger()
config = setup_environment()

# 初始化模型
llm = setup_model(config)

# Cap how much solver feedback we inject into prompts.
_MAX_REPAIR_HINTS = 4
_MAX_PROGRESS_LEMMAS = 6
_PROGRESS_SCORE_THRESHOLD = 0.5
_DIAGNOSTIC_TIMEOUT = 3
_MAX_SUBSET_LEMMAS = 4  # exhaustive pairs only if len(lemmas) <= this

# 在文件开头添加失败引理管理函数
def get_failed_lemmas_file(base_path: str, goal_name: str) -> Path:
    """获取失败引理记录文件路径，根据目标名称生成对应文件"""
    # 提取目标名称的后缀部分来构建文件名
    if goal_name == "template":
        filename = "failed_lemmas.json"
    else:
        # 提取template后面的部分，如template_1 -> _1, template_1_2 -> _1_2
        suffix = goal_name.replace("template", "")
        filename = f"failed_lemmas{suffix}.json"
    
    return Path(base_path) / filename

def _empty_failed_data() -> dict:
    return {
        "invalid_lemmas": [],
        "useless_lemma_groups": [],
        "progress_lemmas": [],
        "repair_hints": [],
    }

def load_failed_lemmas(base_path: str, goal_name: str) -> dict:
    """加载失败引理记录（含 solver-guided repair hints）"""
    failed_file = get_failed_lemmas_file(base_path, goal_name)
    if failed_file.exists():
        try:
            with open(failed_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            # Backward compatible defaults
            data.setdefault("invalid_lemmas", [])
            data.setdefault("useless_lemma_groups", [])
            data.setdefault("progress_lemmas", [])
            data.setdefault("repair_hints", [])
            return data
        except Exception as e:
            logging.warning(f"加载失败引理文件出错: {e}")
    return _empty_failed_data()

def save_failed_lemmas(base_path: str, goal_name: str, failed_data: dict):
    """保存失败引理记录"""
    failed_file = get_failed_lemmas_file(base_path, goal_name)
    try:
        with open(failed_file, 'w', encoding='utf-8') as f:
            json.dump(failed_data, f, ensure_ascii=False, indent=2)
        logging.info(f"保存失败引理到: {failed_file.name}")
    except Exception as e:
        logging.error(f"保存失败引理文件出错: {e}")

def add_invalid_lemma(base_path: str, goal_name: str, lemma: str, reason: str):
    """添加无效引理记录"""
    failed_data = load_failed_lemmas(base_path, goal_name)
    lemma_record = {"lemma": lemma, "reason": reason}
    if lemma_record not in failed_data["invalid_lemmas"]:
        failed_data["invalid_lemmas"].append(lemma_record)
        save_failed_lemmas(base_path, goal_name, failed_data)
        logging.info(f"记录无效引理到{goal_name}: {reason} - {lemma[:50]}...")

def add_useless_lemma_group(base_path: str, goal_name: str, lemma_group: List[str],
                            meta: Optional[dict] = None):
    """添加无用引理组合记录（可附带 Vampire 失败元信息）"""
    failed_data = load_failed_lemmas(base_path, goal_name)
    record: Any = lemma_group
    if meta:
        record = {"lemmas": lemma_group, **meta}
    # Avoid exact duplicates (compare lemma lists)
    existing = failed_data["useless_lemma_groups"]
    for item in existing:
        lemmas = item if isinstance(item, list) else item.get("lemmas", [])
        if lemmas == lemma_group:
            return
    existing.append(record)
    save_failed_lemmas(base_path, goal_name, failed_data)
    logging.info(f"记录无用引理组合到{goal_name}: {len(lemma_group)}条引理")

def add_progress_lemma(base_path: str, goal_name: str, lemma: str,
                       score: float, signals: List[str]):
    """记录对卡住目标有“进展”但尚未证出的引理（供下一轮优先复用/强化）"""
    failed_data = load_failed_lemmas(base_path, goal_name)
    record = {"lemma": lemma, "score": score, "signals": signals}
    # Replace existing entry for same lemma
    failed_data["progress_lemmas"] = [
        r for r in failed_data["progress_lemmas"] if r.get("lemma") != lemma
    ]
    failed_data["progress_lemmas"].append(record)
    # Keep top-N by score
    failed_data["progress_lemmas"].sort(key=lambda r: r.get("score", 0), reverse=True)
    failed_data["progress_lemmas"] = failed_data["progress_lemmas"][:_MAX_PROGRESS_LEMMAS]
    save_failed_lemmas(base_path, goal_name, failed_data)
    logging.info(f"记录进展引理到{goal_name}: score={score:.2f} signals={signals}")

def add_repair_hints(base_path: str, goal_name: str, hints: List[dict]):
    """追加 solver-guided repair hints（去重、截断）"""
    if not hints:
        return
    failed_data = load_failed_lemmas(base_path, goal_name)
    existing = failed_data["repair_hints"]
    existing_keys = {(h.get("kind"), h.get("detail", "")[:80]) for h in existing}
    for hint in hints:
        key = (hint.get("kind"), hint.get("detail", "")[:80])
        if key not in existing_keys:
            existing.append(hint)
            existing_keys.add(key)
    failed_data["repair_hints"] = existing[-_MAX_REPAIR_HINTS:]
    save_failed_lemmas(base_path, goal_name, failed_data)

def format_solver_feedback_for_prompt(failed_data: dict) -> str:
    """把 Vampire 失败/进展信号格式化进下一轮 LLM prompt。"""
    parts: List[str] = []

    if failed_data.get("invalid_lemmas"):
        parts.append(
            "\n\n; IMPORTANT: The following lemmas are INVALID or CANNOT be verified. "
            "DO NOT generate these lemmas:"
        )
        for i, record in enumerate(failed_data["invalid_lemmas"], 1):
            parts.append(f"; Invalid lemma {i} ({record['reason']}): {record['lemma']}")

    if failed_data.get("useless_lemma_groups"):
        parts.append(
            "\n; IMPORTANT: The following lemma groups are USELESS for proving the "
            "original goal. DO NOT generate the exact same group:"
        )
        for i, group in enumerate(failed_data["useless_lemma_groups"], 1):
            lemmas = group if isinstance(group, list) else group.get("lemmas", [])
            meta = "" if isinstance(group, list) else (
                f" [vampire_status={group.get('status', '?')}; "
                f"hint={group.get('hint_kind', '')}]"
            )
            parts.append(f"; Useless group {i}{meta}:")
            for j, lemma in enumerate(lemmas, 1):
                parts.append(f";   {j}. {lemma}")

    if failed_data.get("progress_lemmas"):
        parts.append(
            "\n; SOLVER PROGRESS SIGNALS: The following lemmas did NOT finish the proof, "
            "but Vampire statistics suggest they made rewrite/induction progress. "
            "Prefer refining/extending these rather than unrelated lemmas:"
        )
        for i, record in enumerate(failed_data["progress_lemmas"], 1):
            signals = ", ".join(record.get("signals", []))
            parts.append(
                f"; Progress lemma {i} (score={record.get('score', 0):.2f}; {signals}): "
                f"{record['lemma']}"
            )

    if failed_data.get("repair_hints"):
        parts.append(
            "\n; SOLVER-GUIDED REPAIR (from Vampire failure analysis). "
            "Use these hints to choose the NEXT lemmas:"
        )
        for i, hint in enumerate(failed_data["repair_hints"], 1):
            parts.append(f"; Repair hint {i} [{hint.get('kind', '?')}]: {hint.get('detail', '')}")
            focus = hint.get("induction_focus") or []
            if focus:
                parts.append(f";   Induction focus: {'; '.join(focus[:4])}")
            for action in hint.get("suggested_actions", [])[:3]:
                parts.append(f";   -> {action}")

    return "\n".join(parts)

def create_prompt(smt_file_content: str, prompt_mode: str, base_path: str = None, goal_name: str = None, folder_path: str = None) -> list:
    """创建用于 LLM 的结构化消息列表"""
    if folder_path is None:
        raise ValueError("folder path of prompts must be provided")

    with open(f"{folder_path}/{prompt_mode}/system_prompt.txt", "r", encoding="utf-8") as file:
        system_prompt_content = file.read()
    with open(f"{folder_path}/{prompt_mode}/user_prompt.txt", "r", encoding="utf-8") as file:
        user_prompt_content = file.read()
    # 添加失败引理 + Vampire solver-guided 反馈
    failed_info = ""
    if base_path and goal_name:
        failed_data = load_failed_lemmas(base_path, goal_name)
        failed_info = format_solver_feedback_for_prompt(failed_data)
    
    # 构建结构化消息列表
    user_content = user_prompt_content.format(smt_file_content=smt_file_content) + failed_info
    
    messages = [
        {"role": "system", "content": system_prompt_content},
        {"role": "user", "content": user_content}
    ]
    
    return messages

def extract_balanced_forall(assert_not_content: str) -> Optional[str]:
    """提取平衡的 forall 表达式"""
    # 首先定位到 forall 的开始位置
    start_match = re.search(r'\(\s*forall', assert_not_content)
    if not start_match:
        return None
    
    start_pos = start_match.start()
    balance = 0
    end_pos = start_pos
    
    # 从 forall 开始处扫描，找到平衡的右括号
    for i, c in enumerate(assert_not_content[start_pos:]):
        if c == '(':
            balance += 1
        elif c == ')':
            balance -= 1
            if balance == 0:
                end_pos = start_pos + i + 1
                break
    
    return assert_not_content[start_pos:end_pos]

def parse_llm_response(response: str) -> List[str]:
    """解析LLM输出，提取有效断言"""
    pattern = r'; Output begin(.*?); Output end'
    match = re.search(pattern, response, re.DOTALL)
    if not match:
        raise ValueError("响应格式错误，缺少输出标记")

    result = []
    for line in match.group(1).split('\n'):
        line = line.strip()
        if not line:
            continue
        
        # 使用已有的 extract_balanced_forall 函数提取 forall 内容
        # 可以处理 (forall...) 和 (assert (forall...)) 两种情况
        forall_content = extract_balanced_forall(line)
        if forall_content:
            result.append(forall_content)
    
    return result

def _write_combined_smt(
    original_assert: re.Match,
    asserts: List[str],
    original_content: str,
    output_path: Path,
    *,
    named: bool = False,
) -> None:
    """Write SMT file with lemmas inserted into the proof-goal block."""
    if named:
        combined_asserts = "\n".join(
            f"(assert (! {a} :named lemma_{i}))" for i, a in enumerate(asserts, 1)
        )
    else:
        combined_asserts = "\n".join(f"(assert {a})" for a in asserts)

    new_asserts_block = combined_asserts + "\n" + original_assert.group(1)
    new_content = re.sub(
        r'; proof goal\s*\(assert.*?\)\s*; proof goal end',
        f'; proof goal\n{new_asserts_block}\n; proof goal end',
        original_content,
        flags=re.DOTALL,
    )
    output_path.write_text(new_content)


def _lemma_subsets(asserts: List[str]) -> List[List[str]]:
    """Generate singleton (and small pairwise) subsets for usefulness search."""
    subsets: List[List[str]] = [[a] for a in asserts]
    if 2 <= len(asserts) <= _MAX_SUBSET_LEMMAS:
        for a, b in itertools.combinations(asserts, 2):
            subsets.append([a, b])
    return subsets


def _first_datatype_name(smt_content: str) -> Optional[str]:
    m = re.search(r'\(declare-datatypes\s*\(\s*\(\s*(\w+)', smt_content)
    return m.group(1) if m else None


def _is_trivial_equational_lemma(lemma: str) -> bool:
    """Heuristic: forall ... (= t t) style tautologies are never useful progress."""
    compact = re.sub(r'\s+', ' ', lemma.strip())
    # Find top-level equality body after forall vars
    eq = re.search(r'\(\s*=\s*', compact)
    if not eq:
        return False
    # crude balance extract of (= ...)
    start = eq.start()
    bal = 0
    end = None
    for i, ch in enumerate(compact[start:], start):
        if ch == '(':
            bal += 1
        elif ch == ')':
            bal -= 1
            if bal == 0:
                end = i + 1
                break
    if end is None:
        return False
    body = compact[start + 2:end - 1].strip()  # inside (= ...)
    # split into two args at top-level space
    bal = 0
    parts = []
    cur = []
    for ch in body:
        if ch == '(':
            bal += 1
            cur.append(ch)
        elif ch == ')':
            bal -= 1
            cur.append(ch)
        elif ch == ' ' and bal == 0:
            if cur:
                parts.append(''.join(cur).strip())
                cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append(''.join(cur).strip())
    return len(parts) >= 2 and parts[0] == parts[1]


def analyze_lemma_progress(
    original_assert: re.Match,
    asserts: List[str],
    original_content: str,
    work_dir: Path,
    goal_name: str,
    base_path: str,
) -> Tuple[List[str], VampireResult]:
    """
    Diagnostic pass: compare baseline vs each lemma subset.
    Records progress lemmas + repair hints. Returns progressive lemmas and baseline result.
    """
    baseline_path = work_dir / f"{goal_name}_diag_baseline.smt2"
    baseline_path.write_text(original_content)
    baseline = run_vampire_diagnostic(
        baseline_path, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=True
    )
    add_repair_hints(base_path, goal_name, derive_repair_hints(baseline, context="baseline_goal"))

    # Control: quantified reflexivity on first datatype (closer to a useless forall lemma).
    dt = _first_datatype_name(original_content) or "Nat"
    control_lemma = f"(forall ((x {dt})) (= x x))"
    control_path = work_dir / f"{goal_name}_diag_control.smt2"
    _write_combined_smt(
        original_assert, [control_lemma], original_content, control_path, named=False
    )
    control = run_vampire_diagnostic(
        control_path, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=False
    )

    progressive: List[Tuple[float, str, List[str]]] = []
    for idx, subset in enumerate(_lemma_subsets(asserts), 1):
        if all(_is_trivial_equational_lemma(a) for a in subset):
            logging.info("诊断子集#%d 跳过：平凡重言式引理", idx)
            continue
        cand_path = work_dir / f"{goal_name}_diag_subset_{idx}.smt2"
        _write_combined_smt(original_assert, subset, original_content, cand_path, named=False)
        cand = run_vampire_diagnostic(
            cand_path, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=False
        )
        score, signals = compute_progress_score(baseline, cand, control=control)
        logging.info(
            "诊断子集#%d score=%.2f signals=%s lemmas=%d",
            idx, score, signals, len(subset),
        )
        if score >= _PROGRESS_SCORE_THRESHOLD:
            for lemma in subset:
                if _is_trivial_equational_lemma(lemma):
                    continue
                progressive.append((score, lemma, signals))
                add_progress_lemma(base_path, goal_name, lemma, score, signals)

    # Unique lemmas keeping best score order
    seen = set()
    ordered: List[str] = []
    for score, lemma, _ in sorted(progressive, key=lambda x: -x[0]):
        if lemma not in seen:
            seen.add(lemma)
            ordered.append(lemma)
    return ordered, baseline


def verify_combined_lemmas(
    original_assert: re.Match,
    asserts: List[str],
    original_content: str,
    output_path: Path,
    *,
    base_path: str = None,
    goal_name: str = None,
) -> Tuple[bool, List[str], Optional[VampireResult]]:
    """
    验证引理组合有用性，并在失败时做子集搜索 / 进展评分 / repair hints。

    Returns:
        (useful, selected_lemmas, result)
        selected_lemmas: on success, lemmas that appear in Vampire unsat core when available;
                         otherwise the original asserts. On failure, progressive lemmas (may be empty).
    """
    combined_timeout = config['COMBINED_CVC_TIMEOUT']
    work_dir = output_path.parent
    gname = goal_name or output_path.stem

    # 1) Full set with named lemmas → prove + optional ucore filtering
    named_path = work_dir / f"{output_path.stem}_named.smt2"
    _write_combined_smt(original_assert, asserts, original_content, named_path, named=True)
    ucore_result = run_vampire(named_path, timeout=combined_timeout, collect_ucore=True)

    if ucore_result.proved:
        used = []
        if ucore_result.used_lemma_names:
            for name in ucore_result.used_lemma_names:
                m = re.fullmatch(r"lemma_(\d+)", name)
                if m:
                    idx = int(m.group(1)) - 1
                    if 0 <= idx < len(asserts):
                        used.append(asserts[idx])
        selected = used if used else list(asserts)
        # Also write the non-named combined file for debugging compatibility
        _write_combined_smt(original_assert, selected, original_content, output_path, named=False)
        logging.info(
            "组合引理证出目标；ucore 保留 %d/%d 条引理",
            len(selected), len(asserts),
        )
        return True, selected, ucore_result

    # 2) Fallback prove without ucore (same lemmas) in case ucore mode misfires
    _write_combined_smt(original_assert, asserts, original_content, output_path, named=False)
    plain_result = run_vampire(output_path, timeout=combined_timeout, collect_stats=True)
    if plain_result.proved:
        logging.info("组合引理证出目标（非 ucore 路径）")
        return True, list(asserts), plain_result

    # 3) Subset prove search: any singleton/pair that already proves the goal?
    for idx, subset in enumerate(_lemma_subsets(asserts), 1):
        sub_path = work_dir / f"{output_path.stem}_subset_{idx}.smt2"
        _write_combined_smt(original_assert, subset, original_content, sub_path, named=False)
        sub_res = run_vampire(sub_path, timeout=max(10, combined_timeout // 2), collect_stats=False)
        if sub_res.proved:
            logging.info("子集引理证出目标: %d 条", len(subset))
            _write_combined_smt(original_assert, subset, original_content, output_path, named=False)
            return True, list(subset), sub_res

    # 4) Not useful enough to prove: diagnostic progress + repair hints
    progressive: List[str] = []
    baseline = VampireResult(status="unknown")
    if base_path and goal_name:
        progressive, baseline = analyze_lemma_progress(
            original_assert, asserts, original_content, work_dir, gname, base_path
        )
        hint_kind = "no_progress"
        if progressive:
            hint_kind = "partial_progress"
        add_useless_lemma_group(
            base_path,
            goal_name,
            asserts,
            meta={
                "status": plain_result.status,
                "hint_kind": hint_kind,
                "progressive_count": len(progressive),
            },
        )
        # Extra repair hint summarizing this failed usefulness check
        add_repair_hints(base_path, goal_name, [{
            "kind": hint_kind,
            "context": "usefulness_check",
            "detail": (
                "The full lemma group did not help Vampire prove the goal. "
                + (
                    f"{len(progressive)} lemma(s) showed partial rewrite/induction progress; "
                    "refine them or add bridging lemmas."
                    if progressive else
                    "No lemma subset showed measurable progress; try a different lemma shape "
                    "(generalization / rewrite bridge)."
                )
            ),
            "induction_focus": baseline.induction_focus[:6],
            "suggested_actions": [
                "Build on progress lemmas if any are listed above",
                "Target induction focus terms reported by Vampire",
                "Do not repeat the same useless lemma group",
            ],
        }])

    return False, progressive, plain_result


def perform_initial_verification(goal_smt_file: Path) -> bool:
    """执行初始验证检查"""
    default_timeout = config['DEFAULT_CVC_TIMEOUT']
    logging.info(f"🔍执行初始检查, 目标文件: {goal_smt_file}")
    result = run_vampire(goal_smt_file, default_timeout, collect_stats=True)
    if result.proved:
        logging.info("✅ 原目标直接验证成功!")
        return True

    logging.error(
        "Vampire验证未通过 (status=%s)，开始生成新引理...",
        result.status,
    )
    return False


def seed_baseline_repair_hints(base_path: str, goal_name: str, goal_smt_file: Path) -> None:
    """在首次求助于 LLM 前，用 Vampire 诊断跑一遍，写入 repair hints。"""
    diag = run_vampire_diagnostic(
        goal_smt_file, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=True
    )
    add_repair_hints(base_path, goal_name, derive_repair_hints(diag, context="initial_goal"))
    if diag.induction_focus:
        logging.info("初始归纳焦点: %s", diag.induction_focus[:4])


def extract_original_goal(smt_content: str) -> Tuple[re.Match, str]:
    """提取原始目标断言和forall表达式"""
    original_assert = re.search(
        r'; proof goal\s*(\(assert.*?\))\s*; proof goal end',
        smt_content,
        flags=re.DOTALL
    )
    original_forall = extract_balanced_forall(original_assert.group(1))
    logging.info(f"提取到原始目标: {original_assert.group(1)}, forall 表达式: {original_forall}")
    return original_assert, original_forall

def generate_lemmas_with_llm(smt_content: str, prompt_strategy: str, goal_smt_file: Path, base_path: str, goal_name: str, folder_path: str) -> List[str]:
    """使用LLM生成引理"""
    logging.info(f"即将使用LLM生成引理, 目标文件: {goal_smt_file}, 提示策略: {prompt_strategy}")
    messages = create_prompt(smt_content, prompt_strategy, base_path, goal_name, folder_path)
    response = llm.invoke(messages)
    extracted_asserts = parse_llm_response(response.content)
    
    # # print("LLM response:", response)
    # logging.info(f"LLM response: {response.content}")
    logging.info("从大模型返回中提取引理: %s", extracted_asserts)
    
    return extracted_asserts

def normalize_formula(formula: str) -> str:
    """增强的公式标准化函数"""
    # 1. 清理空白字符
    formula = re.sub(r'\s+', ' ', formula.strip())
    
    # 2. 查找forall关键字
    forall_pos = formula.find('forall')
    if forall_pos == -1:
        return formula
    
    # 3. 手动解析变量定义部分
    ptr = forall_pos + len('forall')
    while ptr < len(formula) and formula[ptr] in ' \t\n':
        ptr += 1
    
    if ptr >= len(formula) or formula[ptr] != '(':
        return formula
    
    # 找到变量定义部分的结束位置
    balance = 0
    var_def_start = ptr
    for i in range(ptr, len(formula)):
        if formula[i] == '(':
            balance += 1
        elif formula[i] == ')':
            balance -= 1
            if balance == 0:
                var_def_end = i + 1
                break
    else:
        return formula
    
    # 提取变量定义和公式体
    var_section = formula[var_def_start+1:var_def_end-1]
    body_start = var_def_end
    while body_start < len(formula) and formula[body_start] in ' \t\n':
        body_start += 1
    
    # 找到公式体
    balance = 0
    body_end = len(formula)
    for i in range(body_start, len(formula)):
        if formula[i] == '(':
            balance += 1
        elif formula[i] == ')':
            balance -= 1
            if balance == 0:
                body_end = i + 1
                break
    
    body = formula[body_start:body_end]
    
    # 4. 解析变量定义
    var_defs = re.findall(r'\(\s*(\w+)\s+(\w+)\s*\)', var_section)
    if not var_defs:
        return formula
    
    # 5. 创建变量映射
    var_map = {var: f'a{i}' for i, (var, _) in enumerate(var_defs)}
    
    # 6. 替换变量
    normalized_body = body
    for old_var, new_var in sorted(var_map.items(), key=lambda x: -len(x[0])):
        normalized_body = re.sub(rf'\b{re.escape(old_var)}\b', new_var, normalized_body)
    
    # 7. 重构公式
    normalized_vars = ' '.join(f'({var_map[var]} {typ})' for var, typ in var_defs)
    return f'(forall ({normalized_vars}) {normalized_body})'

def extract_equality_parts(formula: str):
    """提取等式的左右两部分"""
    # 查找最外层的等式
    eq_start = formula.rfind('(=')
    if eq_start == -1:
        return None, None
    
    # 找到等式的结束位置
    balance = 0
    eq_end = len(formula)
    for i in range(eq_start, len(formula)):
        if formula[i] == '(':
            balance += 1
        elif formula[i] == ')':
            balance -= 1
            if balance == 0:
                eq_end = i + 1
                break
    
    # 提取等式内容（去掉 "(= " 和 ")"）
    eq_content = formula[eq_start + 3:eq_end - 1].strip()
    
    # 手动解析左右两部分
    balance = 0
    parts = []
    current_part = ""
    
    for char in eq_content:
        if char == '(':
            balance += 1
            current_part += char
        elif char == ')':
            balance -= 1
            current_part += char
        elif char == ' ' and balance == 0:
            if current_part.strip():
                parts.append(current_part.strip())
                current_part = ""
        else:
            current_part += char
    
    if current_part.strip():
        parts.append(current_part.strip())
    
    if len(parts) >= 2:
        return parts[0], parts[1]
    return None, None

def normalize_equality_order(formula: str) -> str:
    """标准化等式的左右顺序"""
    # 提取等式的左右部分
    left, right = extract_equality_parts(formula)
    if left is None or right is None:
        return formula
    
    # 按字典序排序，确保相同的等式有统一的顺序
    if left <= right:
        return formula  # 已经是标准顺序
    else:
        # 交换左右顺序 - 需要找到并替换完整的等式部分
        eq_start = formula.rfind('(=')
        if eq_start == -1:
            return formula
            
        # 找到等式的结束位置
        balance = 0
        eq_end = len(formula)
        for i in range(eq_start, len(formula)):
            if formula[i] == '(':
                balance += 1
            elif formula[i] == ')':
                balance -= 1
                if balance == 0:
                    eq_end = i + 1
                    break
        
        # 构造新的等式
        new_equality = f'(= {right} {left})'
        return formula[:eq_start] + new_equality + formula[eq_end:]

def are_formulas_equivalent(formula1: str, formula2: str) -> bool:
    """增强的公式等价性检查"""
    try:
        # 1. 标准化两个公式
        norm1 = normalize_formula(formula1)
        norm2 = normalize_formula(formula2)
        
        # 2. 标准化等式顺序
        norm1 = normalize_equality_order(norm1)
        norm2 = normalize_equality_order(norm2)
        
        # 3. 比较标准化后的公式
        return norm1 == norm2
        
    except Exception as e:
        print(f"标准化过程出错: {e}，回退到简单比较")
        return formula1.strip() == formula2.strip()

def validate_lemmas_against_original(extracted_asserts: List[str], original_forall: str, base_path: str, goal_name: str) -> bool:
    """增强的引理验证函数"""
    for i, assert_stmt in enumerate(extracted_asserts, 1):
        if are_formulas_equivalent(assert_stmt, original_forall):
            logging.error(f"引理 {i} 与原目标相同，生成失败")
            add_invalid_lemma(base_path, goal_name, assert_stmt, "Same as original goal")
            return False
    return True


def create_validation_files(extracted_asserts: List[str], smt_content: str, 
                          smt_file_path: Path, goal_smt_name: str) -> List[Path]:
    """创建引理有效性验证文件"""
    valid_check_paths = []
    for i, assert_stmt in enumerate(extracted_asserts, 1):
        valid_content = re.sub(
            r'; proof goal\s*\(assert.*?\)\s*; proof goal end',
            f'; proof goal\n(assert {assert_stmt})\n; proof goal end',
            smt_content,
            flags=re.DOTALL
        )
        valid_path = smt_file_path / f"{goal_smt_name}_valid_{i}.smt2"
        valid_path.write_text(valid_content)
        valid_check_paths.append(valid_path)
    return valid_check_paths


def verify_single_lemma(valid_path: Path) -> Tuple[Path, VampireResult]:
    """验证单个引理的有效性（assert lemma 若 unsat ⇒ 与公理矛盾 ⇒ invalid）"""
    logging.info(f"开始检查有效性: {valid_path.name}")
    result = run_vampire(valid_path, timeout=1, collect_stats=False)
    logging.info(
        f"检查有效性: {valid_path.name} 结束，proved={result.proved} status={result.status}"
    )
    return valid_path, result


def validate_lemmas_parallel(valid_check_paths: List[Path], base_path: str, goal_name: str) -> bool:
    """并行验证引理有效性"""
    invalid_lemmas = []
    max_workers = min(len(valid_check_paths), 4)
    
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_path = {executor.submit(verify_single_lemma, path): path 
                         for path in valid_check_paths}
        
        for future in as_completed(future_to_path):
            try:
                valid_path, result = future.result()
                if result.proved:
                    logging.warning(f"发现无效引理: {valid_path.name}")
                    invalid_lemmas.append(valid_path)
                    lemma_content = extract_lemma_from_file(valid_path)
                    if lemma_content:
                        add_invalid_lemma(
                            base_path, goal_name, lemma_content,
                            f"contradicts axioms (vampire={result.status})",
                        )
                elif result.status == "error":
                    logging.error(f"引理检查出错: {valid_path.name}: {result.error}")
                    invalid_lemmas.append(valid_path)
                    lemma_content = extract_lemma_from_file(valid_path)
                    if lemma_content:
                        add_invalid_lemma(
                            base_path, goal_name, lemma_content,
                            f"vampire error: {result.error}",
                        )
                else:
                    logging.error(
                        f"暂时无法过滤引理: {valid_path.name} (status={result.status})"
                    )
            except Exception as e:
                path = future_to_path[future]
                logging.error(f"验证引理 {path.name} 时发生异常: {e}")
                invalid_lemmas.append(path)
                lemma_content = extract_lemma_from_file(path)
                if lemma_content:
                    add_invalid_lemma(base_path, goal_name, lemma_content, f"验证异常: {e}")
    
    if invalid_lemmas:
        logging.error("存在不合法引理，需要重新生成")
        return False
    return True

def extract_lemma_from_file(file_path: Path) -> str:
    """从验证文件中提取引理内容"""
    try:
        content = file_path.read_text()
        match = re.search(r'; proof goal\s*\(assert\s+(.+?)\)\s*; proof goal end', content, re.DOTALL)
        if match:
            return match.group(1).strip()
    except Exception as e:
        logging.error(f"提取引理内容失败: {e}")
    return None


def generate_formal_proof_files(extracted_asserts: List[str], smt_content: str,
                        smt_file_path: Path, goal_smt_name: str) -> List[str]:
    """生成正式验证文件（取反的引理）"""
    generated_files = []
    for i, assert_stmt in enumerate(extracted_asserts, 1):
        lemma_content = re.sub(
            r'; proof goal\s*\(assert.*?\)\s*; proof goal end',
            f'; proof goal\n(assert (not {assert_stmt}))\n; proof goal end',
            smt_content,
            flags=re.DOTALL
        )
        lemma_path = smt_file_path / f"{goal_smt_name}_{i}.smt2"
        lemma_path.write_text(lemma_content)
        generated_files.append(lemma_path.name.split('.')[0])
        logging.info(f"生成验证文件: {lemma_path.name}")
    return generated_files


def quick_run(base_path: str, goal_smt_name: str, prompt_strategy: str, folder_path: str, baseline_only: bool = False) -> Tuple[bool, List[str], List[str]]:
    """快速运行函数, 返回验证结果、子目标文件和生成的引理"""
    smt_file_path = Path(base_path)
    goal_smt_file = smt_file_path / f"{goal_smt_name}.smt2"
    smt_content = goal_smt_file.read_text()

    # 步骤1: 初始验证检查
    if baseline_only:
        # 在baseline模式下，使用task_timeout作为超时时间
        task_timeout = config['TASK_TIMEOUT']
        logging.info(f"🔍 Baseline模式: 执行初始验证检查，超时时间: {task_timeout}秒")
        result = run_vampire(goal_smt_file, task_timeout, collect_stats=True)
        if result.proved:
            logging.info("✅ Baseline模式: 初始验证成功!")
        else:
            logging.info("❌ Baseline模式: 初始验证失败 (status=%s)", result.status)
        return result.proved, [], []
    
    # 步骤2: 提取原始目标
    original_assert, original_forall = extract_original_goal(smt_content)

    # 步骤2.5: 首次求助 LLM 前写入 Vampire 诊断反馈（若尚无 repair_hints）
    failed_data = load_failed_lemmas(base_path, goal_smt_name)
    if not failed_data.get("repair_hints"):
        seed_baseline_repair_hints(base_path, goal_smt_name, goal_smt_file)
    
    # 步骤3: 使用LLM生成引理
    extracted_asserts = generate_lemmas_with_llm(smt_content, prompt_strategy, goal_smt_file, base_path, goal_smt_name, folder_path)

    # 如果没有生成引理，尝试延长时间重新验证
    if not extracted_asserts:
        logging.info("大模型未返回引理，尝试提高时间限制重新验证原目标")
        retry_timeout = config['RETRY_CVC_TIMEOUT']
        retry = run_vampire(goal_smt_file, retry_timeout, collect_stats=True)
        if retry.proved:
            logging.info("原目标提高时间到%d秒后验证成功!", retry_timeout)
            return True, [], []
        return False, [], []

    # TODO: 去掉这一部分做消融实验↓
    # 步骤4: 验证引理是否与原目标相同
    if not validate_lemmas_against_original(extracted_asserts, original_forall, base_path, goal_smt_name):
        return False, [], extracted_asserts

    # 步骤5: 创建验证文件并并行验证引理有效性
    valid_check_paths = create_validation_files(extracted_asserts, smt_content, smt_file_path, goal_smt_name)
    
    if not validate_lemmas_parallel(valid_check_paths, base_path, goal_smt_name):
        return False, [], extracted_asserts


    # 步骤6: 检查引理是否有助于证明原目标（含子集搜索 / ucore / 进展评分）
    combined_path = smt_file_path / f"{goal_smt_name}_with_lemmas.smt2"
    useful, selected_lemmas, _vres = verify_combined_lemmas(
        original_assert,
        extracted_asserts,
        smt_content,
        combined_path,
        base_path=base_path,
        goal_name=goal_smt_name,
    )
    if not useful:
        logging.error("生成引理未能帮助证明原目标（已写入进展/repair反馈）")
        return False, [], extracted_asserts

    logging.info(
        "lemmas有用，保留 %d/%d 条用于子目标生成",
        len(selected_lemmas), len(extracted_asserts),
    )

    # 步骤7: 生成正式验证文件（仅对 ucore/子集保留的引理）
    generated_files = generate_formal_proof_files(
        selected_lemmas, smt_content, smt_file_path, goal_smt_name
    )
    
    return True, generated_files, selected_lemmas

def prove_subgoals_parallel(base_path: str, subgoals: List[str], depth: int = 0, strategy_mode: str = "default", baseline_only: bool = False, parent_lemmas: List[str] = None, parent_goal_name: str = None) -> bool:
    """并行执行多个子目标的验证，如果任何一个失败就立即终止所有进程"""
    if not subgoals:
        return True
    
    logging.info(f"🚀 开始并行验证 {len(subgoals)} 个子目标: {subgoals} (递归深度: {depth})")
    
    # 使用ThreadPoolExecutor进行并行执行
    with ThreadPoolExecutor(max_workers=min(len(subgoals), 4)) as executor:
        # 提交所有任务，传递递增的深度参数
        future_to_subgoal = {executor.submit(prove_run, base_path, subgoal, depth + 1, strategy_mode, baseline_only): subgoal 
                            for subgoal in subgoals}
        
        try:
            # 等待任务完成，一旦有任何失败就立即返回
            for future in as_completed(future_to_subgoal):
                subgoal = future_to_subgoal[future]
                try:
                    result = future.result()
                    if not result:
                        logging.error(f"💥 子目标 {subgoal} 验证失败，终止所有并行任务")
                        # 记录导致子目标失败的引理 + Vampire 诊断到父目标
                        if parent_lemmas and parent_goal_name:
                            for lemma in parent_lemmas:
                                add_invalid_lemma(
                                    base_path, parent_goal_name, lemma,
                                    f"导致子目标{subgoal}验证失败",
                                )
                            subgoal_file = Path(base_path) / f"{subgoal}.smt2"
                            if subgoal_file.exists():
                                diag = run_vampire_diagnostic(
                                    subgoal_file,
                                    timeout=_DIAGNOSTIC_TIMEOUT,
                                    show_induction=True,
                                )
                                hints = derive_repair_hints(diag, context=f"subgoal:{subgoal}")
                                hints.append({
                                    "kind": "subgoal_failed",
                                    "context": f"subgoal:{subgoal}",
                                    "detail": (
                                        f"Lemma was useful for the parent goal but its own proof "
                                        f"({subgoal}) failed. Generate easier lemmas, or lemmas that "
                                        f"help prove this subgoal directly."
                                    ),
                                    "induction_focus": diag.induction_focus[:6],
                                    "suggested_actions": [
                                        "Propose a weaker/simpler variant of the failing lemma",
                                        "Add bridging lemmas targeting the subgoal induction focus",
                                    ],
                                })
                                add_repair_hints(base_path, parent_goal_name, hints)
                        # 取消所有未完成的任务
                        for f in future_to_subgoal:
                            if not f.done():
                                f.cancel()
                        return False
                    else:
                        logging.info(f"✅ 子目标 {subgoal} 验证成功")
                except Exception as e:
                    logging.error(f"💥 子目标 {subgoal} 执行异常: {e}，终止所有并行任务")
                    # 记录导致异常的引理到父目标的失败记录中
                    if parent_lemmas and parent_goal_name:
                        for lemma in parent_lemmas:
                            add_invalid_lemma(base_path, parent_goal_name, lemma, f"导致子目标{subgoal}执行异常: {e}")
                    # 取消所有未完成的任务
                    for f in future_to_subgoal:
                        if not f.done():
                            f.cancel()
                    return False
            
            logging.info(f"🌟 所有 {len(subgoals)} 个子目标并行验证通过")
            return True
            
        except KeyboardInterrupt:
            logging.warning("收到中断信号，取消所有并行任务")
            for f in future_to_subgoal:
                if not f.done():
                    f.cancel()
            return False


def prove_run(base_path: str, base_name: str, depth: int = 0, strategy_mode: str = "default", baseline_only: bool = False) -> bool:
    """提示策略的递归验证函数 主程序入口"""
    # 检查递归深度限制
    max_depth = config['MAX_RECURSION_DEPTH']
    if depth >= max_depth:
        logging.warning(f"🚫 达到最大递归深度 {max_depth}，停止处理 {base_name}")
        return False
    
    # 如果是baseline模式，直接调用quick_run进行初始验证
    if baseline_only:
        logging.info(f"🎯 Baseline模式: 开始处理 {base_name}")
        result, _, _ = quick_run(base_path, base_name, "", "", baseline_only=True)
        return result
    
    logging.info(f"开始处理 Path: {base_path}, Name: {base_name} (递归深度: {depth})")

    # 执行初始验证检查
    goal_smt_file = Path(base_path) / f"{base_name}.smt2"
    if perform_initial_verification(goal_smt_file):
        return True

    # 定义prompt策略
    prompt_default_strategies = [
        "prove_prompt_equational_reasoning",
        "prove_prompt_term_rewrite"
    ]

    # 作为ours
    prompts_ours_strategies = [
        "prove_prompt_equational_reasoning",
        "prove_prompt_term_rewrite"
    ]

    prompts_naive_strategies = [
        "prompt_naive" # 这个跑的时候应该是2x3=6次
    ]

    default_prompt_strategies = {
        "folder_path": "./prompts_ours",
        "strategies": prompt_default_strategies,
        "max_attempts": config['MAX_ATTEMPTS_PER_PROMPT']
    }

    ours_prompt_strategies = {
        "folder_path": "./prompts_ours",
        "strategies": prompts_ours_strategies,
        "max_attempts": config['MAX_ATTEMPTS_PER_PROMPT']
    }

    naive_prompt_strategies = {
        "folder_path": "./prompts_naive",
        "strategies": prompts_naive_strategies,
        "max_attempts": config['MAX_ATTEMPTS_PER_PROMPT'] * 2
    }
    
    select_use_prompt_strategies = ours_prompt_strategies

    max_attempts_per_prompt = select_use_prompt_strategies["max_attempts"]

    # 顺序尝试每种prompt策略
    for prompt_idx, prompt_strategy in enumerate(select_use_prompt_strategies["strategies"]):
        logging.info(f"[策略{prompt_idx+1}] 处理 {base_name} - 使用策略 {prompt_strategy}")
        
        # 每种prompt尝试max_attempts_per_prompt次（当前默认参数3次）
        for attempt in range(max_attempts_per_prompt):
            logging.info(f"[主阶段] 处理 {base_name} - 第{attempt+1}/{max_attempts_per_prompt}次尝试({prompt_strategy})")
            try:
                ret, new_subgoals, extracted_asserts = quick_run(base_path, base_name, prompt_strategy, select_use_prompt_strategies["folder_path"], baseline_only=False)
                # ret为True代表发现了可能会有用的子目标 不代表证明成功
                # lemma 被quick filtering了 
                # lemma 是useful的情况下 但是lemma本身没有被验证成功 就给5次
                if ret:
                    logging.info(f"🎯 策略 {prompt_strategy} 第{attempt+1}次尝试搜寻可能有用的引理成功！")
                    
                    # 成功证明的情况，没有subgoal了
                    if not new_subgoals:
                        logging.info(f"🏆 子目标 {base_name} 完成证明！")
                        return True

                    # 处理子目标 - 使用并行执行
                    logging.info(f"🔍 发现子目标: {new_subgoals}")
                    # 传递当前生成的引理和目标名称
                    current_lemmas = extracted_asserts
                    if prove_subgoals_parallel(base_path, new_subgoals, depth, strategy_mode, baseline_only, current_lemmas, base_name):
                        logging.info(f"🌟 所有子目标验证通过，{base_name} 最终成功")
                        return True
                    else:
                        logging.warning(f"💥 子目标验证失败，继续尝试下一次生成")
                        # 不直接返回False，而是继续下一次尝试
                        continue
                    
            except TimeoutError:
                logging.warning(f"策略 {prompt_strategy} 第{attempt+1}次尝试超时")
                continue
            except Exception as e:
                logging.error(f"策略 {prompt_strategy} 第{attempt+1}次尝试出错: {e}")
                continue
            
        logging.error(f"策略 {prompt_strategy} 所有尝试均失败，切换到下一个策略")

    # 所有策略和尝试都失败了
    logging.error(f"🚫 {base_name} 所有策略均失败")
    return False
