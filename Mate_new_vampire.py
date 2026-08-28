import re
import logging
import sys
import json
import os
import tempfile
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Tuple, Optional, Dict, Any
from logger_config import setup_colored_logger
from env_config import setup_environment, setup_model
from vampire_runner import (
    run_vampire_with_timeout,
    run_vampire,
    run_vampire_diagnostic,
    run_vampire_probe,
    run_vampire_routed,
    compute_progress_score,
    derive_repair_hints,
    vampire_diagnostic_profile,
    VampireResult,
)
from solver_routing import (
    GoalSearchState,
    build_search_state,
    fallback_profiles_for,
    format_routing_for_prompt,
    select_generation_prompt,
    retarget_generation_prompt,
    prompt_kind_signature,
    NO_HELP_PROMPT_SWITCH,
    probe_profile_count,
    probe_timeout_s,
    probes_enabled,
    profile_utility_from_stats,
    rank_profiles_for_attempt,
    recommend_profiles,
    record_pair_attempt,
    record_profile_history,
    collect_feedback_signal_kinds,
    set_routing_candidates,
    routing_enabled,
)
from profile_selector import (
    choose_joint_action,
    llm_selector_enabled,
)
from theory_features import analyze_smt

# 配置彩色日志
logger = setup_colored_logger()
config = setup_environment()

# 初始化模型
llm = setup_model(config)

# Unique repair kinds all go into the prompt; only subgoal_failed is capped.
_MAX_SUBGOAL_FAILED_HINTS = 2
_MAX_PROGRESS_LEMMAS = 6
_PROGRESS_SCORE_THRESHOLD = 0.5
_DIAGNOSTIC_TIMEOUT = 3
# Cheap failure-sidecar: score at most this many singleton lemmas (not pairs).
_MAX_PROGRESS_DIAG_LEMMAS = 3

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
        "progress_routing_signals": [],
        "repair_hints": [],
        "unproved_lemmas": [],
        "routing": {},
        "baseline_diag": {},
        "baseline_diag_short": {},
        "control_diag": {},
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
            data.setdefault("progress_routing_signals", [])
            data.setdefault("repair_hints", [])
            data.setdefault("unproved_lemmas", [])
            data.setdefault("routing", {})
            data.setdefault("baseline_diag", {})
            data.setdefault("baseline_diag_short", {})
            data.setdefault("control_diag", {})
            return data
        except Exception as e:
            logging.warning(f"加载失败引理文件出错: {e}")
    return _empty_failed_data()

def save_failed_lemmas(base_path: str, goal_name: str, failed_data: dict):
    """保存失败引理记录"""
    failed_file = get_failed_lemmas_file(base_path, goal_name)
    tmp_file = None
    try:
        with tempfile.NamedTemporaryFile(
            mode='w',
            encoding='utf-8',
            dir=failed_file.parent,
            prefix=f".{failed_file.name}.",
            suffix=".tmp",
            delete=False,
        ) as f:
            tmp_file = Path(f.name)
            json.dump(failed_data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_file, failed_file)
        logging.info(f"保存失败引理到: {failed_file.name}")
    except Exception as e:
        logging.error(f"保存失败引理文件出错: {e}")
        if tmp_file is not None:
            try:
                tmp_file.unlink()
            except OSError:
                pass

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
                       score: float, signals: List[str],
                       *, profile: Optional[str] = None,
                       profile_scores: Optional[dict] = None):
    """记录对卡住目标有“进展”但尚未证出的引理（供下一轮优先复用/强化）"""
    failed_data = load_failed_lemmas(base_path, goal_name)
    record = {"lemma": lemma, "score": score, "signals": signals}
    if profile:
        record["best_profile"] = profile
    if profile_scores:
        record["profile_scores"] = profile_scores
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

def _compact_repair_hints(hints: List[dict]) -> List[dict]:
    """Keep the latest hint per kind; keep a short window of subgoal_failed."""
    latest: Dict[str, dict] = {}
    order: List[str] = []
    subgoal_failed: List[dict] = []
    for hint in hints:
        kind = str(hint.get("kind") or "")
        if kind == "subgoal_failed":
            subgoal_failed.append(hint)
            continue
        if kind in latest:
            order = [k for k in order if k != kind]
        latest[kind] = hint
        order.append(kind)
    unique = [latest[k] for k in order]
    return unique + subgoal_failed[-_MAX_SUBGOAL_FAILED_HINTS:]


def add_repair_hints(base_path: str, goal_name: str, hints: List[dict]):
    """追加 solver-guided repair hints（去重、截断）"""
    if not hints:
        return
    failed_data = load_failed_lemmas(base_path, goal_name)
    failed_data["repair_hints"] = _compact_repair_hints(
        list(failed_data["repair_hints"]) + list(hints)
    )
    save_failed_lemmas(base_path, goal_name, failed_data)

def add_unproved_lemma(base_path: str, goal_name: str, lemma: str, meta: Optional[dict] = None):
    """Lemma was useful for the parent but its own proof failed — not invalid."""
    failed_data = load_failed_lemmas(base_path, goal_name)
    failed_data.setdefault("unproved_lemmas", [])
    record = {"lemma": lemma, **(meta or {})}
    for item in failed_data["unproved_lemmas"]:
        if item.get("lemma") == lemma:
            return
    failed_data["unproved_lemmas"].append(record)
    save_failed_lemmas(base_path, goal_name, failed_data)


def _lemmas_in_useless_groups(failed_data: dict) -> set:
    members = set()
    for group in failed_data.get("useless_lemma_groups") or []:
        lemmas = group if isinstance(group, list) else group.get("lemmas", [])
        members.update(lemmas)
    return members


def _lemma_for_blocking_subgoal(
    parent_goal_name: str,
    subgoal: str,
    parent_lemmas: List[str],
) -> Optional[str]:
    """Map template_k / parent_k to the k-th parent lemma (1-based)."""
    prefix = f"{parent_goal_name}_"
    if not subgoal.startswith(prefix):
        return None
    rest = subgoal[len(prefix):]
    if not rest.isdigit():
        return None
    idx = int(rest)
    if 1 <= idx <= len(parent_lemmas):
        return parent_lemmas[idx - 1]
    return None

def load_routing_state(base_path: str, goal_name: str) -> GoalSearchState:
    return GoalSearchState.from_dict(load_failed_lemmas(base_path, goal_name).get("routing"))

def save_routing_state(base_path: str, goal_name: str, state: GoalSearchState) -> None:
    failed_data = load_failed_lemmas(base_path, goal_name)
    failed_data["routing"] = state.to_dict()
    save_failed_lemmas(base_path, goal_name, failed_data)

def _diag_profile(base_path: str, goal_name: str) -> Optional[str]:
    return load_routing_state(base_path, goal_name).active_profile


def _compact_vampire_diag(result: VampireResult) -> dict:
    return {
        "proved": result.proved,
        "status": result.status,
        "elapsed": result.elapsed,
        "strategy": result.strategy,
        "stats": dict(result.stats or {}),
        "induction_focus": list(result.induction_focus or []),
        "induction_formulas": list(result.induction_formulas or []),
    }


def _vampire_diag_from_compact(data: Optional[dict]) -> Optional[VampireResult]:
    if not isinstance(data, dict) or "status" not in data:
        return None
    return VampireResult(
        proved=bool(data.get("proved", False)),
        status=str(data.get("status", "unknown")),
        elapsed=float(data.get("elapsed", 0.0) or 0.0),
        strategy=str(data.get("strategy", "")),
        stats=dict(data.get("stats") or {}),
        induction_focus=list(data.get("induction_focus") or []),
        induction_formulas=list(data.get("induction_formulas") or []),
    )


def _load_cached_diag(base_path: str, goal_name: str, key: str) -> Optional[VampireResult]:
    return _vampire_diag_from_compact(load_failed_lemmas(base_path, goal_name).get(key))


def _store_cached_diag(base_path: str, goal_name: str, key: str, result: VampireResult) -> None:
    failed_data = load_failed_lemmas(base_path, goal_name)
    failed_data[key] = _compact_vampire_diag(result)
    save_failed_lemmas(base_path, goal_name, failed_data)


def _record_failed_prove_diagnostics(
    base_path: str,
    goal_name: str,
    result: VampireResult,
    *,
    context: str = "initial_goal",
) -> None:
    """Cache first-prove stats/induction as baseline; do not overwrite later runs."""
    if result.proved:
        return
    if _load_cached_diag(base_path, goal_name, "baseline_diag") is None:
        _store_cached_diag(base_path, goal_name, "baseline_diag", result)
    add_repair_hints(base_path, goal_name, derive_repair_hints(result, context=context))
    if result.induction_focus:
        logging.info("归纳焦点 (%s): %s", context, result.induction_focus[:4])


def _record_subgoal_failure_feedback(
    base_path: str,
    parent_goal_name: str,
    subgoal: str,
    parent_lemmas: List[str],
) -> None:
    """Reuse the child's first-prove diagnostics; fall back to a short diagnostic only if missing."""
    child_profile = load_routing_state(base_path, subgoal).active_profile
    blocking = _lemma_for_blocking_subgoal(parent_goal_name, subgoal, parent_lemmas)
    if blocking is not None:
        add_unproved_lemma(
            base_path, parent_goal_name, blocking,
            {
                "status": "useful_but_unproved",
                "blocking_subgoal": subgoal,
                "profile": child_profile,
            },
        )
    diag = _load_cached_diag(base_path, subgoal, "baseline_diag")
    if diag is None:
        subgoal_file = Path(base_path) / f"{subgoal}.smt2"
        if subgoal_file.exists():
            logging.info("子目标 %s 无缓存诊断，回退短诊断", subgoal)
            diag = run_vampire_diagnostic(
                subgoal_file,
                timeout=_DIAGNOSTIC_TIMEOUT,
                show_induction=True,
                profile=child_profile,
            )
            _store_cached_diag(base_path, subgoal, "baseline_diag", diag)
    if diag is None:
        return
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
    parent_state = load_routing_state(base_path, parent_goal_name)
    child_state = load_routing_state(base_path, subgoal)
    if child_state.active_profile:
        parent_state = record_profile_history(
            parent_state,
            child_state.active_profile or "unknown",
            status="subgoal_failed",
            utility=0.0,
            signals=["subgoal_failed"],
        )
        save_routing_state(base_path, parent_goal_name, parent_state)


def _progress_singleton_lemmas(asserts: List[str]) -> List[str]:
    """Lemmas to score after a failed usefulness check: skip tautologies, cap count."""
    out: List[str] = []
    for lemma in asserts:
        if _is_trivial_equational_lemma(lemma):
            continue
        out.append(lemma)
        if len(out) >= _MAX_PROGRESS_DIAG_LEMMAS:
            break
    return out

def _result_has_stats(result: VampireResult) -> bool:
    return any(int(v or 0) > 0 for v in (result.stats or {}).values())


def record_solver_attempt(
    base_path: Optional[str],
    goal_name: Optional[str],
    *,
    prompt_strategy: Optional[str],
    selected_profile: Optional[str],
    result: VampireResult,
) -> None:
    """Persist one prompt/profile outcome for routing and experiment telemetry."""
    if not base_path or not goal_name:
        return
    state = load_routing_state(base_path, goal_name)
    has_stats = _result_has_stats(result)
    hint_kinds = []
    if has_stats:
        hint_kinds = [
            h.get("kind", "")
            for h in derive_repair_hints(result, context="attempt")
            if h.get("kind")
        ]
    fallback_used = bool(
        result.strategy
        and result.strategy in state.fallback_profiles
        and result.strategy not in state.candidate_profiles
    )
    state = record_pair_attempt(
        state,
        prompt_strategy=prompt_strategy,
        profile=selected_profile or state.active_profile,
        status=result.status,
        proved=result.proved,
        elapsed=result.elapsed,
        utility=None,
        signals=hint_kinds,
        fallback_used=fallback_used,
        winner_profile=result.strategy if result.proved else None,
    )
    save_routing_state(base_path, goal_name, state)

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

    useless_members = _lemmas_in_useless_groups(failed_data)

    if failed_data.get("useless_lemma_groups"):
        parts.append(
            "\n; IMPORTANT: The following lemma GROUPS (combinations) did not prove "
            "the original goal. Do not emit the exact same combination again. "
            "Individual members may still be useful if refined or paired differently:"
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
            "\n; SOLVER PROGRESS SIGNALS: singleton search changes vs control. "
            "This is NOT proof of usefulness; a lemma here can still belong to a "
            "failed combination. Prefer refining these, but do not resend the same group:"
        )
        for i, record in enumerate(failed_data["progress_lemmas"], 1):
            signals = ", ".join(record.get("signals", []))
            profile = record.get("best_profile")
            profile_bit = f"; profile={profile}" if profile else ""
            in_group = (
                "; in_failed_group: refine this lemma, do not resend the whole group"
                if record.get("lemma") in useless_members else ""
            )
            parts.append(
                f"; Progress lemma {i} (score={record.get('score', 0):.2f}; {signals}{profile_bit}{in_group}): "
                f"{record['lemma']}"
            )

    if failed_data.get("unproved_lemmas"):
        parts.append(
            "\n; USEFUL BUT UNPROVED: these lemmas helped the parent goal but their "
            "own proofs timed out. Do not discard them; generate weaker variants or "
            "bridging lemmas for them:"
        )
        for i, record in enumerate(failed_data["unproved_lemmas"], 1):
            parts.append(
                f"; Unproved lemma {i} [{record.get('status', 'unknown')}]: {record.get('lemma')}"
            )

    routing_txt = format_routing_for_prompt(
        GoalSearchState.from_dict(failed_data.get("routing"))
    )
    if routing_txt:
        parts.append(routing_txt)

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
            for schema in (hint.get("induction_formulas") or [])[:2]:
                parts.append(f";   Induction schema: {schema}")
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


def _first_datatype_name(smt_content: str) -> Optional[str]:
    m = re.search(r'\(declare-datatypes\s*\(\s*\(\s*(\w+)', smt_content)
    return m.group(1) if m else None


def _control_lemma(smt_content: str) -> str:
    """Build a well-typed tautological control for ADT or arithmetic goals."""
    sort = _first_datatype_name(smt_content)
    if sort is None:
        if re.search(r"\bInt\b", smt_content):
            sort = "Int"
        elif re.search(r"\bReal\b", smt_content):
            sort = "Real"
    if sort:
        return f"(forall ((x {sort})) (= x x))"
    return "(= true true)"


def _extract_binary_args(compact: str, op: str) -> Optional[Tuple[str, str]]:
    m = re.search(rf"\(\s*{re.escape(op)}\s*", compact)
    if not m:
        return None
    start = m.start()
    bal = 0
    end = None
    for i, ch in enumerate(compact[start:], start):
        if ch == "(":
            bal += 1
        elif ch == ")":
            bal -= 1
            if bal == 0:
                end = i + 1
                break
    if end is None:
        return None
    inner = compact[m.end():end - 1].strip()
    bal = 0
    parts: List[str] = []
    cur: List[str] = []
    for ch in inner:
        if ch == "(":
            bal += 1
            cur.append(ch)
        elif ch == ")":
            bal -= 1
            cur.append(ch)
        elif ch == " " and bal == 0:
            if cur:
                parts.append("".join(cur).strip())
                cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur).strip())
    if len(parts) < 2:
        return None
    return parts[0], parts[1]


def _is_trivial_equational_lemma(lemma: str) -> bool:
    """Skip tautologies: (= t t), (=> P P), and (forall ((x T)) (= x x))."""
    compact = re.sub(r"\s+", " ", lemma.strip())
    for op in ("=", "=>"):
        args = _extract_binary_args(compact, op)
        if args and args[0] == args[1]:
            return True
    return bool(re.search(
        r"\(\s*forall\s*\(\s*\(\s*\w+\s+\w+\s*\)\s*\)\s*\(\s*=\s*(\w+)\s+\1\s*\)\s*\)",
        compact,
    ))


def _cached_diag_for_profile(cached, profile: Optional[str], *, resolver) -> Optional[object]:
    """Reuse a 3s cache only when it was produced by the same diagnostic strategy."""
    want = resolver(profile)
    if cached is None or (cached.strategy or "") != want:
        return None
    return cached


def analyze_lemma_progress(
    original_assert: re.Match,
    asserts: List[str],
    original_content: str,
    work_dir: Path,
    goal_name: str,
    base_path: str,
) -> Tuple[List[str], VampireResult]:
    """Failure sidecar: score singleton lemmas vs a 3s goal-only baseline (not the 60s prove)."""
    diag = _diag_profile(base_path, goal_name)
    want = vampire_diagnostic_profile(diag)
    hint_baseline = _load_cached_diag(base_path, goal_name, "baseline_diag")
    progress_baseline = _cached_diag_for_profile(
        _load_cached_diag(base_path, goal_name, "baseline_diag_short"),
        diag,
        resolver=vampire_diagnostic_profile,
    )
    if progress_baseline is None:
        stale = _load_cached_diag(base_path, goal_name, "baseline_diag_short")
        if stale is not None:
            logging.info(
                "Vampire 3s baseline profile %s → %s，重跑 short diagnostic",
                stale.strategy or "?",
                want,
            )
        baseline_path = work_dir / f"{goal_name}_diag_baseline.smt2"
        baseline_path.write_text(original_content)
        progress_baseline = run_vampire_diagnostic(
            baseline_path, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=True, profile=diag
        )
        _store_cached_diag(base_path, goal_name, "baseline_diag_short", progress_baseline)
        if hint_baseline is None:
            _store_cached_diag(base_path, goal_name, "baseline_diag", progress_baseline)
            add_repair_hints(
                base_path, goal_name,
                derive_repair_hints(progress_baseline, context="baseline_goal"),
            )
            hint_baseline = progress_baseline
        else:
            logging.info("Vampire progress 使用 3s short baseline；60s 结果只用于 repair hint")
    else:
        logging.info("复用缓存的 Vampire 3s progress baseline (profile=%s)", want)
    if hint_baseline is None:
        hint_baseline = progress_baseline

    control = _cached_diag_for_profile(
        _load_cached_diag(base_path, goal_name, "control_diag"),
        diag,
        resolver=vampire_diagnostic_profile,
    )
    if control is None:
        control_lemma = _control_lemma(original_content)
        control_path = work_dir / f"{goal_name}_diag_control.smt2"
        _write_combined_smt(
            original_assert, [control_lemma], original_content, control_path, named=False
        )
        control = run_vampire_diagnostic(
            control_path, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=True, profile=diag
        )
        _store_cached_diag(base_path, goal_name, "control_diag", control)

    progressive: List[Tuple[float, str, List[str]]] = []
    observed_signals: List[str] = []
    for idx, lemma in enumerate(_progress_singleton_lemmas(asserts), 1):
        cand_path = work_dir / f"{goal_name}_diag_lemma_{idx}.smt2"
        _write_combined_smt(original_assert, [lemma], original_content, cand_path, named=False)
        cand = run_vampire_diagnostic(
            cand_path, timeout=_DIAGNOSTIC_TIMEOUT, show_induction=True, profile=diag
        )
        score, signals = compute_progress_score(progress_baseline, cand, control=control)
        observed_signals.extend(signals)
        logging.info(
            "诊断单条#%d score=%.2f signals=%s",
            idx, score, signals,
        )
        if score >= _PROGRESS_SCORE_THRESHOLD:
            progressive.append((score, lemma, signals))
            add_progress_lemma(
                base_path, goal_name, lemma, score, signals, profile=diag
            )

    failed_data = load_failed_lemmas(base_path, goal_name)
    failed_data["progress_routing_signals"] = collect_feedback_signal_kinds(
        extra=observed_signals
    )
    save_failed_lemmas(base_path, goal_name, failed_data)

    seen = set()
    ordered: List[str] = []
    for score, lemma, _ in sorted(progressive, key=lambda x: -x[0]):
        if lemma not in seen:
            seen.add(lemma)
            ordered.append(lemma)
    return ordered, hint_baseline


def verify_combined_lemmas(
    original_assert: re.Match,
    asserts: List[str],
    original_content: str,
    output_path: Path,
    *,
    base_path: str = None,
    goal_name: str = None,
    prompt_strategy: Optional[str] = None,
    solver_profile: Optional[str] = None,
    decision_source: Optional[str] = None,
) -> Tuple[bool, List[str], Optional[VampireResult]]:
    """
    有用性检查，对齐原文：只做一次整组 A∧C→P。
    成功时用同一次 run 的 unsat core 剪枝（不额外超时）。
    失败后不二次满超时、不枚举子集再证明，仅做短诊断写入下一轮。
    """
    combined_timeout = config['COMBINED_CVC_TIMEOUT']
    work_dir = output_path.parent
    gname = goal_name or output_path.stem

    # 1) Full set with named lemmas → prove + optional ucore filtering
    named_path = work_dir / f"{output_path.stem}_named.smt2"
    _write_combined_smt(original_assert, asserts, original_content, named_path, named=True)
    state = load_routing_state(base_path, gname) if base_path else GoalSearchState()
    if solver_profile:
        set_routing_candidates(
            state,
            [solver_profile],
            active_profile=solver_profile,
            active_prompt=prompt_strategy,
        )
        state.decision_source = decision_source or state.decision_source
        if base_path:
            save_routing_state(base_path, gname, state)
    ucore_result = run_vampire_routed(
        named_path, timeout=combined_timeout, state=state, collect_ucore=True
    )
    record_solver_attempt(
        base_path,
        gname,
        prompt_strategy=prompt_strategy,
        selected_profile=solver_profile or state.active_profile,
        result=ucore_result,
    )

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

    # Same lemmas, one attempt: do not re-prove at full timeout or search subsets.
    _write_combined_smt(original_assert, asserts, original_content, output_path, named=False)

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
                "status": ucore_result.status,
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
                    "No lemma showed measurable progress; try a different lemma shape "
                    "(generalization / rewrite bridge)."
                )
            ),
            "induction_focus": baseline.induction_focus[:6],
            "progress_signals": load_failed_lemmas(
                base_path, goal_name
            ).get("progress_routing_signals") or [],
            "suggested_actions": [
                "Build on progress lemmas if any are listed above",
                "Target induction focus terms reported by Vampire",
                "Do not repeat the same useless lemma group",
            ],
        }])

    return False, progressive, ucore_result


def perform_initial_verification(
    goal_smt_file: Path,
    *,
    base_path: Optional[str] = None,
    goal_name: Optional[str] = None,
) -> bool:
    """执行初始验证检查"""
    default_timeout = config['DEFAULT_CVC_TIMEOUT']
    logging.info(f"🔍执行初始检查, 目标文件: {goal_smt_file}")
    routing_state = load_routing_state(str(goal_smt_file.parent), goal_smt_file.stem)
    result = run_vampire_routed(
        goal_smt_file,
        default_timeout,
        collect_stats=True,
        show_induction=True,
        state=routing_state,
    )
    if routing_enabled() and base_path and goal_name:
        record_solver_attempt(
            base_path,
            goal_name,
            prompt_strategy=routing_state.active_prompt,
            selected_profile=routing_state.active_profile,
            result=result,
        )
    if result.proved:
        logging.info("✅ 原目标直接验证成功!")
        return True

    if base_path and goal_name:
        _record_failed_prove_diagnostics(base_path, goal_name, result)
    logging.error(
        "Vampire验证未通过 (status=%s)，开始生成新引理...",
        result.status,
    )
    return False


def seed_baseline_repair_hints(
    base_path: str,
    goal_name: str,
    goal_smt_file: Path,
    *,
    parent_goal_name: Optional[str] = None,
) -> None:
    """首次求助于 LLM 前：理论分流、短 probe。repair hints 来自首次 60s prove。"""
    content = goal_smt_file.read_text(encoding="utf-8")
    features = analyze_smt(content)
    parent_profile = None
    if parent_goal_name:
        parent_profile = load_routing_state(base_path, parent_goal_name).active_profile

    failed_data = load_failed_lemmas(base_path, goal_name)
    hints = failed_data.get("repair_hints") or []
    ranked_state = build_search_state(
        "vampire",
        features,
        hints,
        parent_profile=parent_profile,
    )

    if routing_enabled() and probes_enabled() and not llm_selector_enabled():
        probe_names = recommend_profiles(
            "vampire",
            features,
            hints,
            parent_profile=parent_profile,
        )[0][:probe_profile_count()]
        probes = run_vampire_probe(goal_smt_file, probe_names, timeout=probe_timeout_s())
        utilities: Dict[str, float] = {}
        history = []
        reference_name = next(
            (
                name for name in ("induction_portfolio", "smtcomp", "struct_induction")
                if name in probes
            ),
            next(iter(probes), None),
        )
        reference = probes.get(reference_name) if reference_name else None
        for name, res in probes.items():
            if res.proved:
                util, signals = (100.0, ["proved"])
            elif name == reference_name or reference is None:
                util, signals = (0.0, ["reference_profile"])
            else:
                util, signals = profile_utility_from_stats(
                    backend="vampire",
                    proved=res.proved,
                    status=res.status,
                    stats=res.stats,
                    elapsed=res.elapsed,
                    reference_stats=reference.stats,
                    reference_elapsed=reference.elapsed,
                )
            utilities[name] = util
            history.append({
                "profile": name,
                "status": res.status,
                "utility": round(util, 3),
                "signals": signals[:6],
            })
            logging.info(
                "vampire probe %s utility=%.2f status=%s signals=%s",
                name, util, res.status, signals,
            )
        state = build_search_state(
            "vampire",
            features,
            hints,
            parent_profile=parent_profile,
            utilities=utilities,
            history=history,
        )
    elif llm_selector_enabled():
        ranked_profiles, reasons = recommend_profiles(
            "vampire",
            features,
            hints,
            parent_profile=parent_profile,
        )
        decision = choose_joint_action(
            llm=llm,
            backend="vampire",
            features=features,
            candidate_profiles=ranked_profiles,
            prompt_strategies=[
                "prove_prompt_equational_reasoning",
                "prove_prompt_term_rewrite",
            ],
            hints=hints,
        )
        state = ranked_state
        state.routing_reasons = reasons
        set_routing_candidates(
            state,
            [decision.profile],
            active_profile=decision.profile,
            active_prompt=decision.prompt_strategy,
        )
        state.decision_mode = "llm"
        state.decision_source = decision.source
        state.decision_confidence = decision.confidence
        state.routing_reasons.append(f"decision:{decision.reason}")
    else:
        state = ranked_state

    save_routing_state(base_path, goal_name, state)
    logging.info(
        "vampire routing: active=%s candidates=%s reasons=%s",
        state.active_profile, state.candidate_profiles, state.routing_reasons,
    )


def select_attempt_action(
    base_path: str,
    goal_name: str,
    prompt_strategies: List[str],
    *,
    parent_goal_name: Optional[str] = None,
    preferred_prompt: Optional[str] = None,
) -> Tuple[GoalSearchState, object]:
    """Select the next prompt/profile pair after the latest feedback."""
    goal_file = Path(base_path) / f"{goal_name}.smt2"
    content = goal_file.read_text(encoding="utf-8")
    features = analyze_smt(content)
    failed_data = load_failed_lemmas(base_path, goal_name)
    state = GoalSearchState.from_dict(failed_data.get("routing"))
    parent_profile = state.parent_profile
    if not parent_profile and parent_goal_name:
        parent_profile = load_routing_state(base_path, parent_goal_name).active_profile
    state.backend = "vampire"
    state.theory_features = features.to_dict()
    state.parent_profile = parent_profile
    if not state.fallback_profiles:
        state.fallback_profiles = fallback_profiles_for("vampire")
    hints = failed_data.get("repair_hints") or []
    utilities = {
        item.get("profile"): float(item.get("utility"))
        for item in state.profile_history
        if item.get("profile") and item.get("utility") is not None
    }
    ranked, candidates, reasons = rank_profiles_for_attempt(
        "vampire",
        features,
        hints,
        parent_profile=parent_profile,
        current_profile=state.active_profile,
        progress_lemmas=failed_data.get("progress_lemmas") or [],
        extra_signals=failed_data.get("progress_routing_signals") or [],
        probe_utilities=utilities or None,
    )
    if llm_selector_enabled():
        decision = choose_joint_action(
            llm=llm,
            backend="vampire",
            features=features,
            candidate_profiles=ranked,
            prompt_strategies=prompt_strategies,
            hints=hints,
            history=state.pair_history,
            current_profile=state.active_profile,
            current_prompt=preferred_prompt or state.active_prompt,
        )
        state = set_routing_candidates(
            state,
            [decision.profile],
            active_profile=decision.profile,
            active_prompt=decision.prompt_strategy,
        )
        state.decision_mode = "llm"
    else:
        decision = choose_joint_action(
            llm=None,
            backend="vampire",
            features=features,
            candidate_profiles=candidates,
            prompt_strategies=prompt_strategies,
            hints=hints,
            history=state.pair_history,
            current_profile=state.active_profile,
            current_prompt=preferred_prompt or state.active_prompt,
        )
        state = set_routing_candidates(
            state,
            candidates,
            active_profile=decision.profile,
            active_prompt=decision.prompt_strategy,
        )
        state.decision_mode = "relative"
    state.routing_reasons = (state.routing_reasons + reasons)[-8:]
    state.decision_source = getattr(decision, "source", "static")
    state.decision_confidence = getattr(decision, "confidence", 0.0)
    save_routing_state(base_path, goal_name, state)
    return state, decision


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


def quick_run(
    base_path: str,
    goal_smt_name: str,
    prompt_strategy: str,
    folder_path: str,
    baseline_only: bool = False,
    *,
    solver_profile: Optional[str] = None,
    decision_source: Optional[str] = None,
) -> Tuple[bool, List[str], List[str]]:
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

    # 步骤2.5: 首次求助 LLM 前写入 Vampire 诊断反馈 / 理论分流
    failed_data = load_failed_lemmas(base_path, goal_smt_name)
    if routing_enabled() and not failed_data.get("routing"):
        seed_baseline_repair_hints(base_path, goal_smt_name, goal_smt_file)
    if solver_profile:
        state = load_routing_state(base_path, goal_smt_name)
        set_routing_candidates(
            state,
            [solver_profile],
            active_profile=solver_profile,
            active_prompt=prompt_strategy,
        )
        if decision_source:
            state.decision_source = decision_source
        save_routing_state(base_path, goal_smt_name, state)
    
    # 步骤3: 使用LLM生成引理
    extracted_asserts = generate_lemmas_with_llm(smt_content, prompt_strategy, goal_smt_file, base_path, goal_smt_name, folder_path)

    # 如果没有生成引理，与调用失败一样进入下一 attempt，不加时。
    if not extracted_asserts:
        logging.info("大模型未返回引理，跳过本 attempt（不加时）")
        return False, [], []

    # TODO: 去掉这一部分做消融实验↓
    # 步骤4: 验证引理是否与原目标相同
    if not validate_lemmas_against_original(extracted_asserts, original_forall, base_path, goal_smt_name):
        record_solver_attempt(
            base_path,
            goal_smt_name,
            prompt_strategy=prompt_strategy,
            selected_profile=solver_profile or load_routing_state(
                base_path, goal_smt_name
            ).active_profile,
            result=VampireResult(
                status="invalid_lemma",
                strategy=solver_profile or "",
            ),
        )
        return False, [], extracted_asserts

    # 步骤5: 创建验证文件并并行验证引理有效性
    valid_check_paths = create_validation_files(extracted_asserts, smt_content, smt_file_path, goal_smt_name)
    
    if not validate_lemmas_parallel(valid_check_paths, base_path, goal_smt_name):
        record_solver_attempt(
            base_path,
            goal_smt_name,
            prompt_strategy=prompt_strategy,
            selected_profile=solver_profile or load_routing_state(
                base_path, goal_smt_name
            ).active_profile,
            result=VampireResult(
                status="invalid_lemma",
                strategy=solver_profile or "",
            ),
        )
        return False, [], extracted_asserts


    # 步骤6: 一次整组有用性检查；失败则短诊断反馈（不搜索子集证明）
    combined_path = smt_file_path / f"{goal_smt_name}_with_lemmas.smt2"
    useful, selected_lemmas, _vres = verify_combined_lemmas(
        original_assert,
        extracted_asserts,
        smt_content,
        combined_path,
        base_path=base_path,
        goal_name=goal_smt_name,
        prompt_strategy=prompt_strategy,
        solver_profile=solver_profile,
        decision_source=decision_source,
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
        future_to_subgoal = {
            executor.submit(
                prove_run, base_path, subgoal, depth + 1, strategy_mode, baseline_only, parent_goal_name
            ): subgoal
            for subgoal in subgoals
        }
        
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
                            _record_subgoal_failure_feedback(
                                base_path, parent_goal_name, subgoal, parent_lemmas
                            )
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
                        blocking = _lemma_for_blocking_subgoal(
                            parent_goal_name, subgoal, parent_lemmas
                        )
                        if blocking is not None:
                            add_unproved_lemma(
                                base_path, parent_goal_name, blocking,
                                {"status": "error", "blocking_subgoal": subgoal, "error": str(e)},
                            )
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


def prove_run(base_path: str, base_name: str, depth: int = 0, strategy_mode: str = "default", baseline_only: bool = False, parent_goal_name: Optional[str] = None) -> bool:
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

    goal_smt_file = Path(base_path) / f"{base_name}.smt2"
    if routing_enabled() and not load_failed_lemmas(base_path, base_name).get("routing"):
        seed_baseline_repair_hints(
            base_path, base_name, goal_smt_file, parent_goal_name=parent_goal_name
        )

    # 执行初始验证检查
    if perform_initial_verification(
        goal_smt_file, base_path=base_path, goal_name=base_name
    ):
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

    strategies = select_use_prompt_strategies["strategies"]
    max_attempts_per_prompt = select_use_prompt_strategies["max_attempts"]
    total_attempts = max_attempts_per_prompt * max(1, len(strategies))
    hint_list = load_failed_lemmas(base_path, base_name).get("repair_hints") or []
    current_prompt = select_generation_prompt(strategies, hint_list)
    kind_signature = prompt_kind_signature(hint_list)
    consecutive_no_help = 0

    # Shared 2×3 budget. One kind family picks the template; both families
    # sample once. A later change in that family set can switch immediately.
    # If kinds stay the same, two consecutive empty/invalid/useless attempts
    # toggle the other template. Repair hints still go into the chosen template.
    for attempt in range(total_attempts):
        prompt_strategy = current_prompt
        solver_profile = None
        decision_source = None
        if routing_enabled():
            state, decision = select_attempt_action(
                base_path,
                base_name,
                [current_prompt] if current_prompt else strategies,
                parent_goal_name=parent_goal_name,
                preferred_prompt=current_prompt,
            )
            solver_profile = decision.profile
            decision_source = decision.source
        logging.info(
            "[主阶段] 处理 %s - 第%d/%d次尝试(prompt=%s, profile=%s)",
            base_name,
            attempt + 1,
            total_attempts,
            prompt_strategy,
            solver_profile or "paper_portfolio",
        )
        try:
            ret, new_subgoals, extracted_asserts = quick_run(
                base_path,
                base_name,
                prompt_strategy,
                select_use_prompt_strategies["folder_path"],
                baseline_only=False,
                solver_profile=solver_profile,
                decision_source=decision_source,
            )
            # ret为True代表发现了可能会有用的子目标 不代表证明成功
            # lemma 被quick filtering了
            # lemma 是useful的情况下 但是lemma本身没有被验证成功 就给5次
            if ret:
                consecutive_no_help = 0
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
                logging.warning(f"💥 子目标验证失败，继续尝试下一次生成")
                continue

            consecutive_no_help += 1
            hint_list = load_failed_lemmas(base_path, base_name).get("repair_hints") or []
            nxt, consecutive_no_help, kind_signature, why = retarget_generation_prompt(
                strategies,
                hint_list,
                current_prompt,
                consecutive_no_help,
                kind_signature,
            )
            if why == "consecutive":
                logging.info(
                    "连续空/无效/无用达到%d次，切换 prompt %s → %s",
                    NO_HELP_PROMPT_SWITCH,
                    current_prompt,
                    nxt,
                )
            current_prompt = nxt

        except TimeoutError:
            logging.warning(f"策略 {prompt_strategy} 第{attempt+1}次尝试超时")
            consecutive_no_help = 0
            continue
        except Exception as e:
            logging.error(f"策略 {prompt_strategy} 第{attempt+1}次尝试出错: {e}")
            consecutive_no_help = 0
            continue

    # 所有策略和尝试都失败了
    logging.error(f"🚫 {base_name} 所有策略均失败")
    # Paper Algorithm 1 returns False here. The original implementation then
    # retried the same SMT at RETRY_CVC_TIMEOUT (100s). That step is not in
    # the paper: this node already had a 60s initialCheck on the same file.
    # Keep the helper below (commented) in case we want to restore it.
    # return _retry_original_after_llm_exhausted(base_path, base_name)
    return False


# def _retry_original_after_llm_exhausted(base_path: str, goal_name: str) -> bool:
#     """After every LLM attempt on this node failed, retry the original goal once."""
#     goal_smt_file = Path(base_path) / f"{goal_name}.smt2"
#     retry_timeout = config["RETRY_CVC_TIMEOUT"]
#     logging.info("全部 LLM attempt 失败，加时一次再证原目标 timeout=%s", retry_timeout)
#     retry = run_vampire_routed(
#         goal_smt_file,
#         retry_timeout,
#         collect_stats=True,
#         state=load_routing_state(base_path, goal_name),
#     )
#     record_solver_attempt(
#         base_path,
#         goal_name,
#         prompt_strategy=None,
#         selected_profile=load_routing_state(base_path, goal_name).active_profile,
#         result=retry,
#     )
#     if retry.proved:
#         logging.info("原目标提高时间到%d秒后验证成功!", retry_timeout)
#         return True
#     return False
