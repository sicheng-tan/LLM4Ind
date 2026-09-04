"""Experiment telemetry: greppable process logs and per-task summaries.

Process logs use the prefix ``[exp]`` so a task ``.log`` can be filtered with
``grep '\\[exp\\]'``. Per-task ``exp_summary.json`` is written at the end of
``prove_run`` (depth 0) and, on runner timeout/error, reconstructed from the
``failed_lemmas*.json`` / ``lemma_library.json`` artifacts already on disk.

The batch CSV keeps the original four columns first (task, result, duration,
relative path) and then adds algorithm fields needed for tables and ablations.
"""

from __future__ import annotations

import csv
import json
import logging
import os
import re
import threading
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

EXP_SUMMARY_FILENAME = "exp_summary.json"
LIBRARY_FILENAME = "lemma_library.json"
COUNTERS_FILENAME = "exp_counters.json"
LLM_PROMPTS_FILENAME = "llm_prompts.txt"
_LEMMA_LOG_CHARS = 4000

CSV_COLUMNS = [
    "task",
    "result",
    "duration_s",
    "relative_path",
    "solved_by",
    "exit_reason",
    "n_llm_attempts",
    "n_empty",
    "n_invalid",
    "n_useless",
    "n_obligation_trees",
    "n_library_lemmas",
    "n_progress_lemmas",
    "n_invalid_lemmas",
    "n_useless_groups",
    "n_unproved",
    "hint_kinds",
    "prompts_used",
    "active_profile",
    "winner_profile",
    "theory",
    "max_goal_depth",
    "n_goals_touched",
    "n_pair_history",
    "llm_s",
    "solver_s",
    "n_llm",
    "n_solver",
    "n_fallback",
    "n_cancelled",
    "n_subgoals_proved",
    "n_subgoals_failed",
    "n_prompt_with_tree",
    "n_prompt_with_lib",
    "n_prompt_with_hints",
    "flags",
    "error",
]

_COUNTER_LOCK = threading.Lock()

_COUNTER_KEYS = (
    "llm_s",
    "solver_s",
    "n_llm",
    "n_solver",
    "n_fallback",
    "n_library_injects",
    "n_prompts",
    "n_prompt_with_tree",
    "n_prompt_with_lib",
    "n_prompt_with_hints",
    "n_prompt_with_progress",
    "n_prompt_with_unproved",
)

_FLAG_ENV = (
    "SOLVER_ROUTING",
    "SOLVER_ROUTING_DECIDER",
    "SOLVER_ROUTING_PROBES",
    "LEMMA_LIBRARY",
    "OBLIGATION_TREE",
    "FEEDBACK_REPAIR_HINTS",
    "FEEDBACK_PROGRESS",
    "PROMPT_RETARGET",
    "UNPROVED_NOT_INVALID",
    "SUBGOAL_SAT_ABORT",
    "LEMMA_DEFINED_SYMBOLS",
    "LLM_LEMMA_DIAGNOSIS",
    "CHILD_LLM_ATTEMPTS",
    "MODEL_TYPE",
    "OPENAI_MODEL",
)

_FAILED_LEMMAS_RE = re.compile(r"^failed_lemmas((?:_\d+)*)\.json$")
_GOAL_SMT_RE = re.compile(r"^template(?:_\d+)*\.smt2$")


def _fmt(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, float):
        return f"{value:.3f}"
    if isinstance(value, (list, tuple)):
        return ",".join(str(item) for item in list(value)[:12])
    if isinstance(value, dict):
        return ",".join(f"{key}:{val}" for key, val in list(value.items())[:8])
    text = str(value).replace("\n", " ").replace("\r", " ")
    return text[:240]


def log_exp(event: str, **fields: Any) -> None:
    """One greppable line for a pipeline event. Skip empty/None fields."""
    parts = [f"{key}={_fmt(val)}" for key, val in fields.items() if val is not None and val != ""]
    if parts:
        logging.info("[exp] %s %s", event, " ".join(parts))
    else:
        logging.info("[exp] %s", event)


def _counters_path(folder: str) -> Path:
    return Path(folder) / COUNTERS_FILENAME


def _empty_counters() -> Dict[str, float]:
    return {key: 0.0 if key.endswith("_s") else 0 for key in _COUNTER_KEYS}


def load_counters(folder: str) -> Dict[str, Any]:
    path = _counters_path(folder)
    data = _empty_counters()
    if not path.exists():
        return data
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return data
    if isinstance(payload, dict):
        for key in _COUNTER_KEYS:
            if key in payload:
                data[key] = payload[key]
    return data


def bump_counters(folder: Optional[str], **delta: Any) -> Dict[str, Any]:
    """Add into ``exp_counters.json``. Safe for parallel subgoal threads."""
    if not folder:
        return _empty_counters()
    with _COUNTER_LOCK:
        data = load_counters(folder)
        for key, value in delta.items():
            if key not in data:
                data[key] = 0
            data[key] = data[key] + value
        try:
            _counters_path(folder).write_text(
                json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8"
            )
        except OSError:
            pass
        return data


def add_llm_time(folder: Optional[str], seconds: float) -> None:
    if folder and seconds and seconds > 0:
        bump_counters(folder, llm_s=round(float(seconds), 3), n_llm=1)


def _compact_formula(formula: str, limit: int = _LEMMA_LOG_CHARS) -> str:
    text = re.sub(r"\s+", " ", (formula or "").strip())
    if len(text) <= limit:
        return text
    return text[: limit - 3] + "..."


def _llm_prompts_path(folder: str) -> Path:
    return Path(folder) / LLM_PROMPTS_FILENAME


def _next_llm_call_index(folder: str) -> int:
    """1-based index of the next LLM prompt dump. Caller must hold ``_COUNTER_LOCK``."""
    path = _llm_prompts_path(folder)
    if not path.exists():
        return 1
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return 1
    return text.count("\n===== LLM CALL ") + 1


def _format_llm_prompt_dump(
    *,
    call_index: int,
    goal: str,
    strategy: str,
    prompt_folder: str,
    smt_file: str,
    elapsed: float,
    system_text: str,
    user_text: str,
    lemmas: Sequence[str],
    parse_error: Optional[str],
    raw: str = "",
) -> str:
    header = [
        "",
        f"===== LLM CALL {call_index} =====",
        f"goal: {goal}",
        f"strategy: {strategy}",
        f"prompt_folder: {prompt_folder or ''}",
        f"smt_file: {Path(smt_file).name if smt_file else ''}",
        f"elapsed_s: {round(float(elapsed or 0), 3)}",
    ]
    if parse_error:
        header.append(f"parse_error: {parse_error}")
    header.extend(
        [
            "",
            "----- SYSTEM -----",
            system_text or "",
            "",
            "----- USER -----",
            user_text or "",
            "",
            "----- RAW RESPONSE -----",
            raw if raw else "(empty)",
            "",
            f"----- EXTRACTED LEMMAS (n={len(lemmas)}) -----",
        ]
    )
    if lemmas:
        header.extend(str(item) for item in lemmas)
    elif not parse_error:
        header.append("(none)")
    header.append("")
    return "\n".join(header)


def record_llm_generation(
    folder: Optional[str],
    *,
    goal: str,
    strategy: str,
    prompt_folder: str = "",
    smt_file: str = "",
    system_text: str = "",
    user_text: str = "",
    feedback: str = "",
    lemmas: Optional[Sequence[str]] = None,
    elapsed: float = 0.0,
    parse_error: Optional[str] = None,
    raw: str = "",
) -> Dict[str, Any]:
    """Dump the full LLM input and the raw model reply, plus extracted lemmas.

    ``feedback`` is already inside ``user_text``; it is accepted for callers
    but not written separately.
    """
    del feedback
    lemmas = [str(item) for item in (lemmas or []) if item]
    raw_text = str(raw or "")
    call_index = 0
    if folder:
        try:
            with _COUNTER_LOCK:
                call_index = _next_llm_call_index(folder)
                dump = _format_llm_prompt_dump(
                    call_index=call_index,
                    goal=goal,
                    strategy=strategy,
                    prompt_folder=prompt_folder,
                    smt_file=smt_file,
                    elapsed=elapsed,
                    system_text=system_text,
                    user_text=user_text,
                    lemmas=lemmas,
                    parse_error=parse_error,
                    raw=raw_text,
                )
                with _llm_prompts_path(folder).open("a", encoding="utf-8") as handle:
                    handle.write(dump)
        except OSError:
            call_index = 0
    log_exp(
        "llm_call",
        goal=goal,
        strategy=strategy,
        call=call_index or None,
        n=len(lemmas),
        elapsed=round(float(elapsed or 0), 3),
        prompt_file=LLM_PROMPTS_FILENAME if folder else None,
        parse_error=parse_error,
        raw_chars=len(raw_text) or None,
    )
    if parse_error:
        logging.info(
            "[exp] llm_raw goal=%s chars=%s preview=%s",
            goal,
            len(raw_text),
            _compact_formula(raw_text, 400),
        )
    for index, lemma in enumerate(lemmas, 1):
        logging.info(
            "[exp] llm_lemma goal=%s i=%s n=%s formula=%s",
            goal,
            index,
            len(lemmas),
            _compact_formula(lemma),
        )
    return {
        "call": call_index,
        "goal": goal,
        "strategy": strategy,
        "n": len(lemmas),
        "lemmas": lemmas,
        "parse_error": parse_error or None,
    }


def add_solver_time(folder: Optional[str], seconds: float, *, fallback: bool = False) -> None:
    if not folder:
        return
    delta: Dict[str, Any] = {}
    if seconds and seconds > 0:
        delta["solver_s"] = round(float(seconds), 3)
        delta["n_solver"] = 1
    if fallback:
        delta["n_fallback"] = 1
    if delta:
        bump_counters(folder, **delta)


def log_prompt_blocks(
    folder: Optional[str],
    goal: Optional[str],
    prompt_mode: str,
    feedback_text: str,
) -> Dict[str, bool]:
    """Record which feedback blocks actually went into this LLM prompt."""
    text = feedback_text or ""
    inv = {
        "has_invalid": "INVALID or CANNOT" in text,
        "has_useless": "lemma GROUPS" in text,
        "has_progress": "SOLVER PROGRESS SIGNALS" in text,
        "has_unproved": "USEFUL BUT UNPROVED" in text,
        "has_routing": "SOLVER ROUTING" in text,
        "has_hints": "SOLVER-GUIDED REPAIR" in text,
        "has_lib": "already proved" in text or "LEMMA LIBRARY" in text,
        "has_tree": "Last obligation tree" in text,
    }
    log_exp("prompt_blocks", goal=goal, prompt=prompt_mode, **inv)
    if folder:
        bump_counters(
            folder,
            n_prompts=1,
            n_prompt_with_tree=int(inv["has_tree"]),
            n_prompt_with_lib=int(inv["has_lib"]),
            n_prompt_with_hints=int(inv["has_hints"]),
            n_prompt_with_progress=int(inv["has_progress"]),
            n_prompt_with_unproved=int(inv["has_unproved"]),
        )
    return inv


def log_library_inject(
    folder: Optional[str],
    goal: Optional[str],
    n_lemmas: int,
    where: str,
) -> None:
    if not n_lemmas:
        return
    log_exp("library_inject", goal=goal, n=n_lemmas, where=where)
    if folder:
        bump_counters(folder, n_library_injects=1)


def log_subgoal_split(folder: Optional[str], goal: Optional[str], children: Sequence[dict]) -> None:
    counts = Counter(str(node.get("status") or "") for node in children)
    log_exp(
        "subgoal_status",
        goal=goal,
        n=len(children),
        proved=int(counts.get("proved", 0)),
        failed=int(counts.get("failed", 0)),
        invalid=int(counts.get("invalid", 0)),
        cancelled=int(counts.get("cancelled", 0)),
    )


def ablation_flag_snapshot() -> Dict[str, str]:
    """Current ablation / model flags (defaults match env_config / exp_flags)."""
    defaults = {
        "SOLVER_ROUTING": "on",
        "SOLVER_ROUTING_DECIDER": "relative",
        "SOLVER_ROUTING_PROBES": "on",
        "LEMMA_LIBRARY": "on",
        "OBLIGATION_TREE": "on",
        "FEEDBACK_REPAIR_HINTS": "on",
        "FEEDBACK_PROGRESS": "off",
        "PROMPT_RETARGET": "on",
        "UNPROVED_NOT_INVALID": "on",
        "SUBGOAL_SAT_ABORT": "on",
        "LEMMA_DEFINED_SYMBOLS": "on",
        "LLM_LEMMA_DIAGNOSIS": "on",
        "CHILD_LLM_ATTEMPTS": "2",
        "MODEL_TYPE": "gpt-4o",
        "OPENAI_MODEL": "openai/gpt-5",
    }
    return {name: os.getenv(name, defaults[name]).strip() for name in _FLAG_ENV}


def flags_compact(snapshot: Optional[Dict[str, str]] = None) -> str:
    snap = snapshot or ablation_flag_snapshot()
    return ";".join(f"{key}={snap[key]}" for key in _FLAG_ENV)


def log_run_config(
    *,
    backend: str = "",
    strategy_mode: str = "",
    baseline: bool = False,
    task_timeout: Optional[int] = None,
    extra: Optional[Dict[str, Any]] = None,
) -> None:
    snap = ablation_flag_snapshot()
    fields: Dict[str, Any] = {
        "backend": backend or None,
        "strategy_mode": strategy_mode or None,
        "baseline": baseline,
        "task_timeout": task_timeout,
        "flags": flags_compact(snap),
        "model": snap.get("MODEL_TYPE"),
    }
    if extra:
        fields.update(extra)
    log_exp("run_config", **fields)


def exp_summary_path(folder: str) -> Path:
    return Path(folder) / EXP_SUMMARY_FILENAME


def load_task_summary(folder: str) -> Dict[str, Any]:
    path = exp_summary_path(folder)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def _goal_name_from_failed_file(name: str) -> Optional[str]:
    match = _FAILED_LEMMAS_RE.match(name)
    if not match:
        return None
    suffix = match.group(1)
    return "template" if not suffix else f"template{suffix}"


def _depth_from_goal_name(goal_name: str) -> int:
    if not goal_name or goal_name == "template":
        return 0
    rest = goal_name.replace("template", "", 1).lstrip("_")
    if not rest:
        return 0
    return len([part for part in rest.split("_") if part])


def _hint_kinds(failed_data: dict) -> List[str]:
    kinds: List[str] = []
    seen = set()
    for hint in failed_data.get("repair_hints") or []:
        kind = str(hint.get("kind") or "")
        if kind and kind not in seen:
            seen.add(kind)
            kinds.append(kind)
    return kinds


def _attempt_kinds(failed_data: dict) -> List[str]:
    exp_attempts = failed_data.get("exp_attempts") or []
    if exp_attempts:
        return [str(item.get("kind") or "") for item in exp_attempts if item.get("kind")]
    obligation = failed_data.get("obligation") or {}
    return [
        str(item.get("kind") or "")
        for item in (obligation.get("attempts") or [])
        if item.get("kind")
    ]


def _theory_label(features: Any) -> str:
    if not isinstance(features, dict):
        return ""
    if features.get("mixed_adt_lia"):
        return "mixed_adt_lia"
    if features.get("has_adt") and (features.get("has_int") or features.get("has_linear_arithmetic")):
        return "mixed_adt_lia"
    if features.get("has_adt"):
        return "adt"
    if features.get("has_int") or features.get("has_linear_arithmetic"):
        return "int"
    if features.get("has_real"):
        return "real"
    if features.get("has_bitvec"):
        return "bitvec"
    logic = str(features.get("logic") or "")
    return logic.lower() if logic else "unknown"


def _walk_tree_nodes(tree: Optional[dict]) -> List[dict]:
    if not isinstance(tree, dict):
        return []
    nodes = [tree]
    for child in tree.get("children") or []:
        if isinstance(child, dict):
            nodes.extend(_walk_tree_nodes(child))
    return nodes


def _obligation_trees(data: dict) -> List[dict]:
    trees: List[dict] = []
    obligation = data.get("obligation") or {}
    for attempt in obligation.get("attempts") or []:
        if attempt.get("kind") != "obligation_tree":
            continue
        tree = attempt.get("tree")
        if isinstance(tree, dict):
            trees.append(tree)
    return trees


def _goal_ids_from_tree(tree: dict) -> List[str]:
    ids: List[str] = []
    for node in _walk_tree_nodes(tree):
        node_id = str(node.get("id") or "")
        if node_id:
            ids.append(node_id)
    return ids


def _collect_goal_names(
    folder: str,
    records: Dict[str, dict],
    library: Sequence[dict],
) -> List[str]:
    """Goals from failed_lemmas*, obligation-tree ids, library origins, SMT files."""
    names = set(records)
    for data in records.values():
        for tree in _obligation_trees(data):
            names.update(_goal_ids_from_tree(tree))
    for item in library:
        origin = str(item.get("origin") or "")
        if origin:
            names.add(origin)
    root = Path(folder)
    if root.is_dir():
        for path in root.glob("template*.smt2"):
            if _GOAL_SMT_RE.match(path.name):
                names.add(path.stem)
    return sorted(names)


def _max_goal_depth(
    names: Sequence[str],
    library: Sequence[dict],
) -> int:
    depth = 0
    for name in names:
        depth = max(depth, _depth_from_goal_name(name))
    for item in library:
        origin = str(item.get("origin") or "")
        if origin:
            depth = max(depth, _depth_from_goal_name(origin))
        try:
            depth = max(depth, int(item.get("depth") or 0))
        except (TypeError, ValueError):
            pass
    return depth


def _node_invalid_attempts(data: dict) -> int:
    """Invalid attempt-kinds plus a node_outcome invalid that has no such attempt."""
    kinds = _attempt_kinds(data)
    n = sum(1 for kind in kinds if kind == "invalid")
    outcome = data.get("node_outcome") or {}
    if str(outcome.get("kind") or "") == "invalid" and "invalid" not in kinds:
        n += 1
    return n


def _all_attempt_kinds(records: Dict[str, dict]) -> List[str]:
    kinds: List[str] = []
    for data in records.values():
        kinds.extend(_attempt_kinds(data))
    return kinds


def _all_pair_history(records: Dict[str, dict]) -> List[dict]:
    items: List[dict] = []
    root = records.get("template") or {}
    routing = root.get("routing") if isinstance(root.get("routing"), dict) else {}
    items.extend(routing.get("pair_history") or [])
    for goal, data in records.items():
        if goal == "template":
            continue
        routing = data.get("routing") if isinstance(data.get("routing"), dict) else {}
        items.extend(routing.get("pair_history") or [])
    return items


def _split_child_counts(records: Dict[str, dict]) -> Counter:
    """Subgoal statuses across obligation trees. Dedup nodes that have an id."""
    by_id: Dict[str, str] = {}
    anonymous: Counter = Counter()
    for data in records.values():
        for tree in _obligation_trees(data):
            for child in tree.get("children") or []:
                if not isinstance(child, dict):
                    continue
                for node in _walk_tree_nodes(child):
                    node_id = str(node.get("id") or "")
                    status = str(node.get("status") or "")
                    if node_id:
                        by_id[node_id] = status
                    else:
                        anonymous[status] += 1
    counts: Counter = Counter(by_id.values())
    counts.update(anonymous)
    return counts


def _load_library(folder: str) -> List[dict]:
    payload = _read_json(Path(folder) / LIBRARY_FILENAME)
    if isinstance(payload, dict):
        lemmas = payload.get("lemmas") or []
    elif isinstance(payload, list):
        lemmas = payload
    else:
        lemmas = []
    return [item for item in lemmas if isinstance(item, dict)]


def collect_goal_records(folder: str) -> Dict[str, dict]:
    records: Dict[str, dict] = {}
    root = Path(folder)
    if not root.is_dir():
        return records
    for path in sorted(root.glob("failed_lemmas*.json")):
        goal = _goal_name_from_failed_file(path.name)
        if not goal:
            continue
        data = _read_json(path)
        if isinstance(data, dict):
            records[goal] = data
    return records


def summarize_artifacts(folder: str) -> Dict[str, Any]:
    """Rebuild algorithm counters from on-disk artifacts (works after timeouts)."""
    records = collect_goal_records(folder)
    library = _load_library(folder)
    goal_names = _collect_goal_names(folder, records, library)
    root = records.get("template") or {}
    routing = root.get("routing") if isinstance(root.get("routing"), dict) else {}
    pair_history = _all_pair_history(records)
    kinds = _all_attempt_kinds(records)
    kind_counts = Counter(kinds)
    prompts = []
    seen_prompts = set()
    for item in pair_history:
        prompt = str(item.get("prompt_strategy") or "")
        if prompt and prompt not in seen_prompts:
            seen_prompts.add(prompt)
            prompts.append(prompt)
    winner = ""
    for item in reversed(routing.get("pair_history") or []):
        if item.get("proved") and item.get("winner_profile"):
            winner = str(item.get("winner_profile"))
            break
    n_progress = 0
    n_invalid_lemmas = 0
    n_useless_groups = 0
    n_unproved = 0
    n_invalid = 0
    all_hints: List[str] = []
    hint_seen = set()
    for data in records.values():
        n_progress += len(data.get("progress_lemmas") or [])
        n_invalid_lemmas += len(data.get("invalid_lemmas") or [])
        n_useless_groups += len(data.get("useless_lemma_groups") or [])
        n_unproved += len(data.get("unproved_lemmas") or [])
        n_invalid += _node_invalid_attempts(data)
        for kind in _hint_kinds(data):
            if kind not in hint_seen:
                hint_seen.add(kind)
                all_hints.append(kind)
    split_counts = _split_child_counts(records)
    n_fallback = sum(1 for item in pair_history if item.get("fallback_used"))
    counters = load_counters(folder)
    summary = {
        "n_llm_attempts": len(kinds),
        "n_empty": int(kind_counts.get("empty", 0)),
        "n_invalid": int(n_invalid),
        "n_useless": int(kind_counts.get("useless", 0)),
        "n_obligation_trees": int(kind_counts.get("obligation_tree", 0)),
        "attempt_kinds": kinds,
        "n_library_lemmas": len(library),
        "n_progress_lemmas": n_progress,
        "n_invalid_lemmas": n_invalid_lemmas,
        "n_useless_groups": n_useless_groups,
        "n_unproved": n_unproved,
        "hint_kinds": all_hints,
        "prompts_used": prompts,
        "active_profile": routing.get("active_profile") or "",
        "winner_profile": winner,
        "decision_mode": routing.get("decision_mode") or "",
        "decision_source": routing.get("decision_source") or "",
        "theory": _theory_label(routing.get("theory_features")),
        "max_goal_depth": _max_goal_depth(goal_names, library),
        "n_pair_history": len(pair_history),
        "n_goals_touched": len(goal_names),
        "routing_reasons": list(routing.get("routing_reasons") or [])[-6:],
        "n_cancelled": int(split_counts.get("cancelled", 0)),
        "n_subgoals_proved": int(split_counts.get("proved", 0)),
        "n_subgoals_failed": int(split_counts.get("failed", 0)),
        "n_fallback": int(counters.get("n_fallback") or n_fallback),
        "llm_s": round(float(counters.get("llm_s") or 0), 3),
        "solver_s": round(float(counters.get("solver_s") or 0), 3),
        "n_llm": int(counters.get("n_llm") or 0),
        "n_solver": int(counters.get("n_solver") or 0),
        "n_library_injects": int(counters.get("n_library_injects") or 0),
        "n_prompt_with_tree": int(counters.get("n_prompt_with_tree") or 0),
        "n_prompt_with_lib": int(counters.get("n_prompt_with_lib") or 0),
        "n_prompt_with_hints": int(counters.get("n_prompt_with_hints") or 0),
        "n_prompt_with_progress": int(counters.get("n_prompt_with_progress") or 0),
        "n_prompt_with_unproved": int(counters.get("n_prompt_with_unproved") or 0),
        "n_prompts": int(counters.get("n_prompts") or 0),
    }
    if not summary["n_fallback"]:
        summary["n_fallback"] = n_fallback
    return summary


def solved_by_from_reason(exit_reason: str, proved: bool) -> str:
    if exit_reason == "timeout":
        return "timeout"
    if not proved:
        return "unsolved"
    if exit_reason in ("direct_prove",):
        return "direct"
    if exit_reason in ("baseline_prove", "baseline_fail"):
        return "baseline" if proved else "unsolved"
    if exit_reason in ("llm_no_subgoals", "llm_subgoals"):
        return "llm"
    return "llm" if proved else "unsolved"


def write_task_summary(
    folder: str,
    *,
    proved: bool,
    exit_reason: str,
    error: str = "",
    extra: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Write ``exp_summary.json`` and log a compact ``[exp] task_summary`` line."""
    summary = summarize_artifacts(folder)
    summary.update({
        "proved": bool(proved),
        "exit_reason": exit_reason,
        "solved_by": solved_by_from_reason(exit_reason, proved),
        "error": error or "",
        "flags": flags_compact(),
        "goal": Path(folder).name,
    })
    if extra:
        for key, value in extra.items():
            if value is not None:
                summary[key] = value
    path = exp_summary_path(folder)
    try:
        path.write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    except OSError as exc:
        logging.warning("failed to write %s: %s", path, exc)
    log_exp(
        "task_summary",
        goal=summary.get("goal"),
        proved=proved,
        solved_by=summary.get("solved_by"),
        exit=exit_reason,
        attempts=summary.get("n_llm_attempts"),
        empty=summary.get("n_empty"),
        invalid=summary.get("n_invalid"),
        invalid_lemmas=summary.get("n_invalid_lemmas"),
        useless=summary.get("n_useless"),
        trees=summary.get("n_obligation_trees"),
        lib=summary.get("n_library_lemmas"),
        hints=_fmt(summary.get("hint_kinds")),
        profile=summary.get("active_profile") or None,
        winner=summary.get("winner_profile") or None,
        theory=summary.get("theory") or None,
        depth=summary.get("max_goal_depth"),
        goals=summary.get("n_goals_touched"),
        llm_s=summary.get("llm_s") or None,
        solver_s=summary.get("solver_s") or None,
        fallback=summary.get("n_fallback") or None,
        cancelled=summary.get("n_cancelled") or None,
        sub_proved=summary.get("n_subgoals_proved") or None,
        sub_failed=summary.get("n_subgoals_failed") or None,
        error=error or None,
    )
    return summary


def finalize_root_task(
    folder: str,
    *,
    proved: bool,
    exit_reason: str,
    baseline_only: bool = False,
    strategy_mode: str = "",
    error: str = "",
) -> Dict[str, Any]:
    extra: Dict[str, Any] = {"baseline_only": baseline_only}
    if strategy_mode:
        extra["strategy_mode"] = strategy_mode
    return write_task_summary(
        folder,
        proved=proved,
        exit_reason=exit_reason,
        error=error,
        extra=extra,
    )


def ensure_task_summary(
    folder: str,
    *,
    proved: bool,
    error: str = "",
) -> Dict[str, Any]:
    """If prove_run did not finish (timeout/kill), rebuild a summary from artifacts."""
    existing = load_task_summary(folder)
    if existing.get("exit_reason") and existing.get("exit_reason") != "timeout":
        if error and not existing.get("error"):
            existing["error"] = error
            try:
                exp_summary_path(folder).write_text(
                    json.dumps(existing, ensure_ascii=False, indent=2),
                    encoding="utf-8",
                )
            except OSError:
                pass
        return existing
    exit_reason = "timeout" if error and "超时" in error else ("error" if error else "attempts_exhausted")
    if existing.get("exit_reason") == "timeout" and not error:
        return existing
    return write_task_summary(folder, proved=proved, exit_reason=exit_reason, error=error)


def _task_label(folder: str) -> str:
    parts = folder.rstrip(os.sep).split(os.sep)
    if len(parts) >= 2:
        return os.path.join(parts[-2], parts[-1])
    return os.path.basename(folder)


def csv_row(
    folder: str,
    status: bool,
    duration: float,
    original_root_path: str,
    error: str = "",
) -> List[str]:
    try:
        relative_path = os.path.relpath(folder, original_root_path)
    except ValueError:
        relative_path = folder
    summary = load_task_summary(folder)
    if not summary:
        summary = summarize_artifacts(folder)
    result_str = "unsat" if status else ""
    duration_s = f"{float(duration):.2f}" if duration is not None else ""
    values = {
        "task": _task_label(folder),
        "result": result_str,
        "duration_s": duration_s,
        "relative_path": relative_path,
        "solved_by": summary.get("solved_by") or ("direct" if status and not summary.get("n_llm_attempts") else ("llm" if status else "unsolved")),
        "exit_reason": summary.get("exit_reason") or "",
        "n_llm_attempts": summary.get("n_llm_attempts", ""),
        "n_empty": summary.get("n_empty", ""),
        "n_invalid": summary.get("n_invalid", ""),
        "n_useless": summary.get("n_useless", ""),
        "n_obligation_trees": summary.get("n_obligation_trees", ""),
        "n_library_lemmas": summary.get("n_library_lemmas", ""),
        "n_progress_lemmas": summary.get("n_progress_lemmas", ""),
        "n_invalid_lemmas": summary.get("n_invalid_lemmas", ""),
        "n_useless_groups": summary.get("n_useless_groups", ""),
        "n_unproved": summary.get("n_unproved", ""),
        "hint_kinds": _fmt(summary.get("hint_kinds") or []),
        "prompts_used": _fmt(summary.get("prompts_used") or []),
        "active_profile": summary.get("active_profile") or "",
        "winner_profile": summary.get("winner_profile") or "",
        "theory": summary.get("theory") or "",
        "max_goal_depth": summary.get("max_goal_depth", ""),
        "n_goals_touched": summary.get("n_goals_touched", ""),
        "n_pair_history": summary.get("n_pair_history", ""),
        "llm_s": summary.get("llm_s", ""),
        "solver_s": summary.get("solver_s", ""),
        "n_llm": summary.get("n_llm", ""),
        "n_solver": summary.get("n_solver", ""),
        "n_fallback": summary.get("n_fallback", ""),
        "n_cancelled": summary.get("n_cancelled", ""),
        "n_subgoals_proved": summary.get("n_subgoals_proved", ""),
        "n_subgoals_failed": summary.get("n_subgoals_failed", ""),
        "n_prompt_with_tree": summary.get("n_prompt_with_tree", ""),
        "n_prompt_with_lib": summary.get("n_prompt_with_lib", ""),
        "n_prompt_with_hints": summary.get("n_prompt_with_hints", ""),
        "flags": summary.get("flags") or flags_compact(),
        "error": error or summary.get("error") or "",
    }
    return [str(values[col]) for col in CSV_COLUMNS]


def write_results_csv(
    results: Sequence[Tuple],
    output_path: str,
    original_root_path: str,
) -> str:
    """Write the detailed CSV plus a JSONL of full per-task summaries.

    Each result tuple is ``(folder, status, duration)`` or
    ``(folder, status, duration, error)``.
    """
    sorted_results = sorted(results, key=lambda row: os.path.basename(row[0]))
    with open(output_path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(CSV_COLUMNS)
        for row in sorted_results:
            folder, status, duration = row[0], row[1], row[2]
            error = row[3] if len(row) > 3 else ""
            writer.writerow(csv_row(folder, status, duration, original_root_path, error or ""))
    jsonl_path = str(Path(output_path).with_suffix(".jsonl"))
    with open(jsonl_path, "w", encoding="utf-8") as handle:
        for row in sorted_results:
            folder, status, duration = row[0], row[1], row[2]
            error = row[3] if len(row) > 3 else ""
            payload = load_task_summary(folder) or summarize_artifacts(folder)
            payload = dict(payload)
            payload["task"] = _task_label(folder)
            payload["proved"] = bool(status)
            payload["duration_s"] = round(float(duration), 2) if duration is not None else None
            if error:
                payload["error"] = error
            handle.write(json.dumps(payload, ensure_ascii=False) + "\n")
    return jsonl_path


def print_batch_stats(results: Sequence[Tuple], total_duration: float) -> None:
    total = len(results)
    successful = sum(1 for row in results if row[1])
    by_reason: Counter = Counter()
    by_solved: Counter = Counter()
    timeouts = 0
    for row in results:
        folder = row[0]
        error = row[3] if len(row) > 3 else ""
        summary = load_task_summary(folder)
        by_solved[summary.get("solved_by") or ("llm" if row[1] else "unsolved")] += 1
        by_reason[summary.get("exit_reason") or ""] += 1
        if error and "超时" in str(error):
            timeouts += 1
    print("\n=== 执行完成 ===")
    print(f"总任务数: {total}")
    print(f"成功求解: {successful}")
    print(f"失败任务: {total - successful}")
    if timeouts:
        print(f"超时任务: {timeouts}")
    print(f"总执行时间: {total_duration:.2f}秒")
    if total:
        print(f"平均每任务时间: {total_duration / total:.2f}秒")
    if by_solved:
        parts = ", ".join(f"{name}={count}" for name, count in sorted(by_solved.items()) if name)
        print(f"求解来源: {parts}")
    reasons = {name: count for name, count in by_reason.items() if name}
    if reasons:
        parts = ", ".join(f"{name}={count}" for name, count in sorted(reasons.items()))
        print(f"结束原因: {parts}")
