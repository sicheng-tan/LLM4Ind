"""Fail-fast gates for lemma subgoals: defined symbols, sat abort, LLM reason.

Boolean flags default on (current method). Set them off in paper.env to restore
the original loop. CHILD_LLM_ATTEMPTS=0 keeps the root 2N budget at every depth.
LEMMA_FILTER_DROP keeps remaining members after screening and continues
usefulness; paper.env sets it off so any failing member aborts the group.
The diagnosis suffix is never attached at depth 0; children follow LLM_LEMMA_DIAGNOSIS.
After a child node's attempts are exhausted, one extra diagnosis-only LLM call
judges whether the CURRENT goal is invalid from the parent's accumulated
``invalid_lemmas`` (child write-back), same signal as in-loop diagnosis —
not the obligation tree. Skip when that INVALID list is empty.
``FEEDBACK_PROGRESS`` remains default off.
LLM_PARSE_RETRIES extra LLM calls after a format parse failure stay inside the
same prove-run attempt (HTTP retries are LLM_MAX_RETRIES and unrelated).
"""

from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

from exp_flags import _flag_enabled, feedback_llm_hints_enabled, prompt_advice_enabled
from obligation_tree import (
    compact_formula,
    lemmas_equivalent,
    normalize_lemma_formula,
    obligation_tree_enabled,
)
from prompt_modes import (
    advice_from_failed_data,
    format_advice_lines,
    format_local_vs_parent_lines,
)

_DECLARE_FUN = re.compile(
    r"\(declare-fun\s+([A-Za-z_][A-Za-z0-9_+*/<>=!?-]*)"
)
_DEFINE_FUN = re.compile(
    r"\(define-fun\s+([A-Za-z_][A-Za-z0-9_+*/<>=!?-]*)"
)
_APP = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_+*/<>=!?-]*)")
_PROOF_GOAL = re.compile(
    r"; proof goal\s*.*?; proof goal end",
    flags=re.DOTALL,
)
INVALID_GOAL_TAG = "INVALID_GOAL"
_INVALID_GOAL_LINE = re.compile(
    rf"^[;\s]*{INVALID_GOAL_TAG}\s*:\s*(.+)$",
    flags=re.IGNORECASE,
)

_RESERVED = frozenset({
    "forall", "exists", "assert", "and", "or", "not", "xor", "ite", "let", "as",
    "true", "false", "distinct", "par", "match", "case", "lambda", "!", "_",
    "check-sat", "exit", "set-logic", "set-option", "declare-fun", "define-fun",
    "declare-const", "declare-datatype", "declare-datatypes",
})

DIAGNOSIS_PROMPT_SUFFIX = (
    "\nIf the CURRENT goal is invalid (not a theorem of the given axioms, "
    "for example it is missing hypotheses, it contradicts existing axioms or lemmas, "
    "or a used function is only declared with no defining assert), "
    "emit <output></output> and write one line:\n"
    "; INVALID_GOAL: <short explanation>\n"
    "INVALID_GOAL means the CURRENT goal is not a theorem, not that no helper lemma is needed.\n"
    "If a previously proposed child lemma is marked invalid, use that invalid mark "
    "and its reason to decide whether the CURRENT goal is also invalid "
    "(e.g. it depends on the same missing definition or contradiction).\n"
)

FINAL_DIAGNOSIS_PROMPT_SUFFIX = (
    "\nFINAL CHECK (do not propose lemmas; do not use <lemma> tags).\n"
    "Using INVALID child lemmas and their reasons "
    "(written back when a proposed helper was refuted), "
    "decide whether the CURRENT goal is a theorem of the given axioms.\n"
    "If a previously proposed child lemma is marked invalid, use that mark "
    "and its reason to decide whether the CURRENT goal is also invalid "
    "(e.g. it depends on the same missing definition or contradiction).\n"
    "If it is INVALID (not a theorem), output invalid and write one line:\n"
    "; INVALID_GOAL: <short explanation>\n"
    "If it MAY still be a theorem, output failed.\n"
)

_OPEN_DIAGNOSIS = frozenset({
    "still_open", "open", "still possible", "may still be a theorem", "failed",
})
_FAILED_VERDICTS = frozenset({"failed", "still_open", "open"})
_INVALID_VERDICTS = frozenset({"invalid"})
_VERDICT_LINE = re.compile(
    r"^[;\s]*(invalid|failed|still_open)\s*$",
    flags=re.IGNORECASE,
)

MAX_REASON_CHARS = 200
MAX_MIX_SOURCE_LEMMAS = 6
HD_DIFFICULTY_EXPLAIN = (
    "difficulty: search hotspot intensity from the last solver run; "
    "d= is that intensity, not proof necessity. "
)
HD_AXIOM_GOAL_HINT = (
    "hint: listed axioms are possible starting points; propose lemmas that "
    "help prove the CURRENT goal (a hotspot need not be used)."
)
FORMULA_EVIDENCE_KIND = "solver_formula_evidence"
MAX_FORMULA_EVIDENCE_CHARS = 400
FORMULA_EVIDENCE_EXPLAIN = (
    "Use hotspots as possible starting points, not mandatory dependencies. "
    "Inspect formula conditions and recursive-call arguments. "
    "These samples do not establish that a condition is missing or that "
    "generalization is required. Other axioms may provide essential "
    "intermediate connections."
)
MAX_PARSE_RETRY_SNIPPET = 1500
PARSE_RETRY_USER = (
    "FORMAT ERROR: no usable lemma (missing tags, empty <output>, or unmatched "
    "parentheses). Reply with at least one balanced formula:\n"
    "<output>\n"
    "<lemma>(forall ...)</lemma>\n"
    "</output>\n"
    "Child only, if the CURRENT goal is not a theorem:\n"
    "<output></output>\n"
    "; INVALID_GOAL: <short explanation>"
)
PARSE_ERR_EMPTY = "空引理输出"
PARSE_ERR_UNMATCHED = "引理括号不配平"
PARSE_ERR_MISSING_TAGS = "响应格式错误，缺少输出标记"
MAX_FORALL_CLOSE_REPAIR = 2


def subgoal_sat_abort_enabled() -> bool:
    return _flag_enabled("SUBGOAL_SAT_ABORT")


def defined_symbols_enabled() -> bool:
    return _flag_enabled("LEMMA_DEFINED_SYMBOLS")


def lemma_filter_drop_enabled() -> bool:
    """Drop failing members and continue usefulness on the rest (default on).

    paper.env sets this off: any failing member aborts the whole group.
    """
    return _flag_enabled("LEMMA_FILTER_DROP")


def llm_lemma_diagnosis_enabled() -> bool:
    return _flag_enabled("LLM_LEMMA_DIAGNOSIS")


def should_append_diagnosis_suffix(depth: int = 0) -> bool:
    """Root (depth 0) never gets the diagnosis lines; children follow the flag."""
    if int(depth or 0) <= 0:
        return False
    return llm_lemma_diagnosis_enabled()


def llm_parse_retries() -> int:
    """Extra LLM calls after a format parse failure, same prove-run attempt.

    Default 2 (first call + two retries, 3 total). 0 disables. Does not consume
    another attempt unless those extra calls also fail to parse. Distinct from
    ``LLM_MAX_RETRIES`` (HTTP transport).
    """
    raw = os.getenv("LLM_PARSE_RETRIES")
    if raw is None or str(raw).strip() == "":
        return 2
    try:
        return max(0, int(raw))
    except (TypeError, ValueError):
        return 2


def with_parse_retry_hint(
    messages: Sequence[Dict[str, Any]], previous_raw: str
) -> List[Dict[str, Any]]:
    """Append the failed reply and a format-correction user turn."""
    snippet = (previous_raw or "").strip()
    if len(snippet) > MAX_PARSE_RETRY_SNIPPET:
        snippet = snippet[:MAX_PARSE_RETRY_SNIPPET] + "\n..."
    out = [dict(item) for item in messages]
    if snippet:
        out.append({"role": "assistant", "content": snippet})
    out.append({"role": "user", "content": PARSE_RETRY_USER})
    return out


def child_llm_attempts() -> int:
    """0 / unset-as-default: use the same 2N budget as the root.

    Default is 2 so the current method caps child LLM loops. paper.env should
    set CHILD_LLM_ATTEMPTS=0.
    """
    raw = os.getenv("CHILD_LLM_ATTEMPTS")
    if raw is None or str(raw).strip() == "":
        return 2
    try:
        return max(0, int(raw))
    except (TypeError, ValueError):
        return 2


def node_attempt_plan(depth: int, pack: Dict[str, Any]) -> Tuple[int, int]:
    """Return (total_attempts, max_attempts_per_prompt) for this node."""
    total = int(pack["total_attempts"])
    per = int(pack["max_attempts_per_prompt"])
    cap = child_llm_attempts()
    if depth <= 0 or cap <= 0:
        return total, per
    n_strat = max(1, len(pack.get("strategies") or []))
    capped = min(cap, total)
    per_capped = max(1, capped // n_strat) if n_strat > 1 else capped
    return capped, per_capped


def should_run_final_diagnosis(depth: int = 0, *, has_invalid: bool = True) -> bool:
    """Extra invalid-check LLM call after child attempts are exhausted.

    Requires at least one INVALID lemma on this node (typically written back
    when a child subgoal was refuted). No INVALID evidence → skip the call.
    Independent of ``OBLIGATION_TREE``.
    """
    return (
        int(depth or 0) >= 1
        and llm_lemma_diagnosis_enabled()
        and bool(has_invalid)
    )


def format_diagnosis_invalid_prompt(failed_data: Optional[dict]) -> str:
    """INVALID-only block for the extra invalid-check LLM call.

    Same records as the in-loop INVALID section (child write-back / static
    gates). Omits unproved, repair, progress, routing, and the obligation tree.
    """
    data = failed_data if isinstance(failed_data, dict) else {}
    records = [
        item for item in (data.get("invalid_lemmas") or [])
        if isinstance(item, dict) and str(item.get("lemma") or "").strip()
    ]
    if not records:
        return ""
    parts = [
        "\n\nINVALID: The following lemmas are INVALID or CANNOT be verified. "
        "Do not generate these lemmas, and do not weaken them; use the reason "
        "to judge whether the CURRENT goal is also invalid:"
    ]
    for i, record in enumerate(records, 1):
        reason = str(record.get("reason") or "").strip() or "invalid"
        parts.append(f"  Invalid lemma {i} ({reason}): {record.get('lemma')}")
    return "\n".join(parts)


def parse_llm_reason(raw: Optional[str]) -> Optional[str]:
    """Extract the ``; INVALID_GOAL:`` diagnosis line. Plain ``reason:`` is ignored."""
    if not raw:
        return None
    for line in str(raw).splitlines():
        match = _INVALID_GOAL_LINE.match(line.strip())
        if match:
            reason = match.group(1).strip()
            if reason:
                return reason[:MAX_REASON_CHARS]
    return None


def allow_unmarked_lemma_output(
    raw: Optional[str], *, diagnosis_only: bool = False, depth: int = 0
) -> bool:
    """True when missing lemma output tags should not abort the attempt.

    Final diagnosis never wraps lemmas. Child generation may also emit only
    ``; INVALID_GOAL:`` instead of a lemma block. Root must still produce lemmas.
    """
    if diagnosis_only:
        return True
    if int(depth or 0) <= 0:
        return False
    if not llm_lemma_diagnosis_enabled():
        return False
    return bool(parse_llm_reason(raw))


_OUTPUT_TAG = re.compile(
    r"<\s*(?:output|lemmas)\s*>(.*?)</\s*(?:output|lemmas)\s*>",
    flags=re.DOTALL | re.IGNORECASE,
)
_LEMMA_TAG = re.compile(
    r"<\s*lemma\s*>(.*?)</\s*lemma\s*>",
    flags=re.DOTALL | re.IGNORECASE,
)
_LEGACY_OUTPUT = re.compile(
    r";\s*Output\s+begin(.*?);\s*Output\s+end",
    flags=re.DOTALL | re.IGNORECASE,
)
_FORALL_START = re.compile(r"\(\s*forall")
_NEED_UNKNOWN = re.compile(
    r";\s*Need\s+unknown\s+lemma\s*:?(.*)$",
    flags=re.DOTALL | re.IGNORECASE,
)


def extract_balanced_forall(text: str) -> Optional[str]:
    """Return the first balanced ``(forall ...)`` in ``text``, or None."""
    start_match = _FORALL_START.search(text or "")
    if not start_match:
        return None
    start_pos = start_match.start()
    balance = 0
    for i, ch in enumerate(text[start_pos:]):
        if ch == "(":
            balance += 1
        elif ch == ")":
            balance -= 1
            if balance == 0:
                return text[start_pos:start_pos + i + 1]
    return None


def _paren_balance(text: str) -> int:
    bal = 0
    for ch in text or "":
        if ch == "(":
            bal += 1
        elif ch == ")":
            bal -= 1
    return bal


def try_repair_unbalanced_forall(
    text: str, max_close: int = MAX_FORALL_CLOSE_REPAIR
) -> Optional[str]:
    """Append 1–2 ``)`` if a ``(forall`` prefix is short of a matching close."""
    start = _FORALL_START.search(text or "")
    if not start:
        return None
    chunk = text[start.start():]
    bal = _paren_balance(chunk)
    if 1 <= bal <= max_close:
        return extract_balanced_forall(chunk.rstrip() + (")" * bal))
    return None


def extract_forall_repaired(text: str) -> Tuple[Optional[str], bool]:
    """Return ``(formula, unmatched)``. unmatched means a forall could not be closed."""
    formula = extract_balanced_forall(text)
    if formula:
        return formula, False
    if not _FORALL_START.search(text or ""):
        return None, False
    repaired = try_repair_unbalanced_forall(text)
    if repaired:
        return repaired, False
    return None, True


def _formulas_from_blob(text: str) -> Tuple[List[str], bool]:
    """Extract foralls from lemma tags if present, else scan untagged foralls."""
    tagged = [body.strip() for body in _LEMMA_TAG.findall(text or "") if body.strip()]
    found: List[str] = []
    unmatched = False
    if tagged:
        for body in tagged:
            formula, bad = extract_forall_repaired(body)
            if formula:
                found.append(formula)
            elif bad:
                unmatched = True
        return found, unmatched
    pos = 0
    blob = text or ""
    while True:
        match = _FORALL_START.search(blob, pos)
        if not match:
            break
        formula, bad = extract_forall_repaired(blob[match.start():])
        if formula:
            found.append(formula)
            pos = match.start() + len(formula)
            continue
        unmatched = unmatched or bad
        break
    return found, unmatched


def collect_lemmas(text: str) -> Tuple[List[str], bool]:
    """Salvage lemmas from tags, ``; Need unknown lemma``, then the output block."""
    found: List[str] = []
    unmatched = False
    for body in _LEMMA_TAG.findall(text or ""):
        formula, bad = extract_forall_repaired((body or "").strip())
        if formula:
            found.append(formula)
        elif bad:
            unmatched = True
    if found:
        return found, unmatched
    need = _NEED_UNKNOWN.search(text or "")
    if need:
        extra, bad = _formulas_from_blob(need.group(1))
        found.extend(extra)
        unmatched = unmatched or bad
        if found:
            return found, unmatched
    match = _OUTPUT_TAG.search(text or "")
    blob = match.group(1) if match else None
    if blob is None:
        legacy = _LEGACY_OUTPUT.search(text or "")
        blob = legacy.group(1) if legacy else None
    if blob:
        extra, bad = _formulas_from_blob(blob)
        found.extend(extra)
        unmatched = unmatched or bad
    return found, unmatched


def parse_llm_lemmas(
    response: Optional[str],
    *,
    depth: int = 0,
    diagnosis_only: bool = False,
) -> List[str]:
    """Extract SMT lemmas from an LLM reply.

    Preferred shape::

        <output>
        <lemma>(forall ...)</lemma>
        </output>

    Also accepts ``<lemmas>``, bare ``<lemma>`` tags, ``; Need unknown lemma``
    foralls, and the legacy ``; Output begin`` / ``; Output end`` block.
    Empty tagged output is a parse error unless this is a child ``INVALID_GOAL``
    or a diagnosis-only call. Foralls missing 1–2 ``)`` are repaired.
    """
    text = response or ""
    lemmas, unmatched = collect_lemmas(text)
    if lemmas:
        return lemmas
    if diagnosis_only:
        return []
    has_wrapper = bool(
        _OUTPUT_TAG.search(text) or _LEMMA_TAG.search(text) or _LEGACY_OUTPUT.search(text)
    )
    if unmatched:
        raise ValueError(PARSE_ERR_UNMATCHED)
    if not has_wrapper:
        raise ValueError(PARSE_ERR_MISSING_TAGS)
    if int(depth or 0) >= 1 and parse_llm_reason(text):
        return []
    raise ValueError(PARSE_ERR_EMPTY)


def parse_final_diagnosis(raw: Optional[str]) -> Tuple[str, Optional[str]]:
    """Parse extra-check output into ('invalid'|'failed', reason).

    Unparsed or open verdicts are failed (this node stays failed, not invalid).
    ``still_open`` is accepted as an alias of ``failed``.
    A bare ``; INVALID_GOAL:`` line (no ``invalid`` token) still counts as invalid,
    matching the generation-round diagnosis suffix.
    """
    reason = parse_llm_reason(raw)
    token = None
    for line in str(raw or "").splitlines():
        match = _VERDICT_LINE.match(line.strip())
        if match:
            token = match.group(1).strip().lower()
    key = (reason or "").strip().lower()
    if token in _FAILED_VERDICTS:
        return "failed", None
    if token in _INVALID_VERDICTS:
        if reason and key not in _INVALID_VERDICTS and key not in _OPEN_DIAGNOSIS:
            return "invalid", reason
        return "invalid", None
    if key in _OPEN_DIAGNOSIS:
        return "failed", None
    if reason:
        return "invalid", reason
    return "failed", None


def is_invalid_diagnosis_reason(reason: Optional[str]) -> bool:
    """True when a diagnosis reason means the CURRENT goal is not a theorem."""
    if not reason:
        return False
    key = reason.strip().lower()
    if key in _OPEN_DIAGNOSIS or key.startswith("still_open"):
        return False
    return True


def declared_function_names(smt: str) -> Set[str]:
    return set(_DECLARE_FUN.findall(smt or ""))


def axiomatized_function_names(smt: str) -> Set[str]:
    axioms = _PROOF_GOAL.sub("", smt or "")
    names = set(_DEFINE_FUN.findall(smt or ""))
    for ident in _APP.findall(axioms):
        if ident not in _RESERVED and not ident.startswith("declare-"):
            names.add(ident)
    return names


def undefined_symbols_in_lemma(lemma: str, smt: str) -> List[str]:
    declared = declared_function_names(smt)
    if not declared:
        return []
    axiomatized = axiomatized_function_names(smt)
    used = {
        ident for ident in _APP.findall(lemma or "")
        if ident not in _RESERVED
    }
    return sorted(used & declared - axiomatized)


def lemmas_undefined_symbols(lemmas: Sequence[str], smt: str) -> Dict[str, List[str]]:
    out: Dict[str, List[str]] = {}
    for lemma in lemmas:
        undef = undefined_symbols_in_lemma(lemma, smt)
        if undef:
            out[lemma] = undef
    return out


def _stored_invalid_formula(record: Any) -> str:
    stored = record.get("lemma") if isinstance(record, dict) else record
    return normalize_lemma_formula(str(stored or ""))


def lemma_known_invalid(lemma: str, invalid_lemmas: Sequence[Any]) -> bool:
    """True iff *lemma* matches a stored invalid formula after whitespace collapse.

    Character-level equality only (no substring, no equality-order swap) so a
    different but overlapping formula is not treated as already invalid.
    """
    key = normalize_lemma_formula(lemma)
    if not key:
        return False
    return any(_stored_invalid_formula(record) == key for record in invalid_lemmas or [])


def _stored_unproved_formula(record: Any) -> str:
    stored = record.get("lemma") if isinstance(record, dict) else record
    return str(stored or "")


def lemma_known_unproved(lemma: str, unproved_lemmas: Sequence[Any]) -> bool:
    """True iff *lemma* is whitespace- or α-equivalent to a stored unproved formula."""
    if not str(lemma or "").strip():
        return False
    return any(
        lemmas_equivalent(lemma, _stored_unproved_formula(record))
        for record in unproved_lemmas or []
    )


def drop_equivalent_unproved(
    records: Sequence[Any], formula: str
) -> Tuple[List[Any], int]:
    """Drop unproved records equivalent to *formula*. Returns (kept, n_removed)."""
    kept: List[Any] = []
    n_removed = 0
    for record in records or []:
        if lemmas_equivalent(formula, _stored_unproved_formula(record)):
            n_removed += 1
            continue
        kept.append(record)
    return kept, n_removed


def purge_unproved_equivalent(base_path: str, formula: str) -> int:
    """Drop unproved/revival records equivalent to a proved *formula*."""
    if not str(formula or "").strip():
        return 0
    root = Path(base_path)
    if not root.is_dir():
        return 0
    total = 0
    for path in sorted(root.glob("failed_lemmas*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(data, dict):
            continue
        changed = False
        unproved = data.get("unproved_lemmas") or []
        kept_u, n_u = drop_equivalent_unproved(unproved, formula)
        if n_u:
            data["unproved_lemmas"] = kept_u
            changed = True
        if "revival_lemmas" in data:
            kept_r, n_r = drop_equivalent_unproved(
                data.get("revival_lemmas") or [], formula,
            )
            if n_r:
                data["revival_lemmas"] = kept_r
                changed = True
            total += n_r
        else:
            n_r = 0
        total += n_u
        if not changed:
            continue
        path.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
    return total


REVIVAL_ORIGIN_SITUATION_A = "situation_a"
REVIVAL_ORIGIN_CHILD_PENDING = "child_pending"
MAX_REVIVAL_LEMMAS = 24


def seed_revival_from_unproved(data: dict) -> None:
    """If ``revival_lemmas`` is missing, copy this node's unproved as situation_a.

    Does not walk descendants. Mutates *data* in place.
    """
    if "revival_lemmas" in data:
        data.setdefault("revival_lemmas", [])
        return
    seeded: List[dict] = []
    for rec in data.get("unproved_lemmas") or []:
        if not isinstance(rec, dict):
            continue
        lemma = str(rec.get("lemma") or "").strip()
        if not lemma:
            continue
        item = {
            "lemma": lemma,
            "status": rec.get("status") or "unproved",
            "origin": REVIVAL_ORIGIN_SITUATION_A,
            "source_goal": rec.get("source_goal") or rec.get("blocking_subgoal") or "",
        }
        blocking = rec.get("blocking_subgoal")
        if blocking:
            item["blocking_subgoal"] = blocking
        seeded.append(item)
    data["revival_lemmas"] = seeded[-MAX_REVIVAL_LEMMAS:]


def merge_revival_record(records: Sequence[Any], record: dict) -> List[Any]:
    """Append *record* unless α-equivalent already present; keep newest 24."""
    lemma = str((record or {}).get("lemma") or "").strip()
    if not lemma:
        return list(records or [])
    if lemma_known_unproved(lemma, records):
        return list(records or [])
    out = list(records or []) + [record]
    if len(out) > MAX_REVIVAL_LEMMAS:
        out = out[-MAX_REVIVAL_LEMMAS:]
    return out


def should_promote_child_pending(
    lemma: str,
    *,
    current_goal: Optional[str] = None,
    library: Sequence[Any] = (),
    blocking_lemma: Optional[str] = None,
) -> bool:
    """A child revival formula may enter the parent revival pool.

    No head/locality gate: the child already kept it as diagnoser material.
    Skip only empties, the blocking parent lemma (already situation_a),
    GOAL/library α-equivalents. Missing CURRENT only skips the GOAL check.
    """
    text = str(lemma or "").strip()
    if not text:
        return False
    if blocking_lemma and lemmas_equivalent(text, blocking_lemma):
        return False
    goal = str(current_goal or "").strip()
    if goal and lemmas_equivalent(text, goal):
        return False
    for item in library or []:
        stored = item.get("formula") if isinstance(item, dict) else item
        if lemmas_equivalent(text, str(stored or "")):
            return False
    return True


def add_revival_lemma(
    base_path: str,
    goal_name: str,
    lemma: str,
    *,
    origin: str,
    source_goal: str = "",
    status: str = "unproved",
    blocking_subgoal: Optional[str] = None,
    load_failed_lemmas,
    save_failed_lemmas,
) -> bool:
    """Append one revival record. Returns True if the pool grew."""
    text = str(lemma or "").strip()
    if not text:
        return False
    data = load_failed_lemmas(base_path, goal_name)
    seed_revival_from_unproved(data)
    record: Dict[str, Any] = {
        "lemma": text,
        "status": status or "unproved",
        "origin": origin or REVIVAL_ORIGIN_SITUATION_A,
        "source_goal": source_goal or goal_name,
    }
    if blocking_subgoal:
        record["blocking_subgoal"] = blocking_subgoal
    merged = merge_revival_record(data.get("revival_lemmas") or [], record)
    if merged == list(data.get("revival_lemmas") or []):
        return False
    data["revival_lemmas"] = merged
    save_failed_lemmas(base_path, goal_name, data)
    return True


def promote_child_pending_lemmas(
    base_path: str,
    parent_goal_name: str,
    subgoal: str,
    *,
    blocking_lemma: Optional[str] = None,
    current_goal: Optional[str] = None,
    library: Sequence[Any] = (),
    load_failed_lemmas,
    save_failed_lemmas,
) -> int:
    """Lift the child's diagnoser ``revival_lemmas`` into the parent pool.

    One hop of the child's already-aggregated pool (situation_a plus
    whatever that child inherited). Does not walk descendant files, so a
    deeper tree reuses the same inherit. Does not write parent
    ``unproved_lemmas`` / USEFUL BUT UNPROVED. Skips the blocking parent
    lemma, GOAL, library α-equivalents, and useless-timeout groups.
    """
    child = load_failed_lemmas(base_path, subgoal)
    parent = load_failed_lemmas(base_path, parent_goal_name)
    seed_revival_from_unproved(child)
    seed_revival_from_unproved(parent)
    records = list(parent.get("revival_lemmas") or [])
    n_add = 0
    for rec in child.get("revival_lemmas") or []:
        if not isinstance(rec, dict):
            continue
        lemma = str(rec.get("lemma") or "").strip()
        if not should_promote_child_pending(
            lemma,
            current_goal=current_goal,
            library=library,
            blocking_lemma=blocking_lemma,
        ):
            continue
        record = {
            "lemma": lemma,
            "status": rec.get("status") or "unproved",
            "origin": REVIVAL_ORIGIN_CHILD_PENDING,
            "source_goal": str(rec.get("source_goal") or "").strip() or subgoal,
        }
        blocking = rec.get("blocking_subgoal")
        if blocking:
            record["blocking_subgoal"] = blocking
        merged = merge_revival_record(records, record)
        if len(merged) > len(records):
            n_add += 1
        records = merged
    if not n_add:
        return 0
    parent["revival_lemmas"] = records
    save_failed_lemmas(base_path, parent_goal_name, parent)
    return n_add


def lemmas_known_invalid(
    lemmas: Sequence[str], invalid_lemmas: Sequence[Any]
) -> List[str]:
    return [lemma for lemma in lemmas if lemma_known_invalid(lemma, invalid_lemmas)]


BENIGN_SCREEN_GATES = frozenset({
    "known_invalid",
    "same_as_library",
    "same_as_ancestor",
})


def lemma_same_as_goal(lemma: str, goal: str) -> bool:
    """True if *lemma* is the goal after whitespace collapse or α-normalization."""
    return lemmas_equivalent(lemma, goal)


def drop_failing_members(
    lemmas: Sequence[str],
    reason_for: Callable[[str], Optional[str]],
) -> Tuple[List[str], List[Tuple[str, str]]]:
    """Partition *lemmas* by *reason_for*.

    With ``LEMMA_FILTER_DROP`` on, keep the members that have no reason.
    With it off, any failing member discards the whole group (kept is empty).
    """
    dropped: List[Tuple[str, str]] = []
    kept: List[str] = []
    for lemma in lemmas:
        reason = reason_for(lemma)
        if reason:
            dropped.append((lemma, reason))
        else:
            kept.append(lemma)
    if dropped and not lemma_filter_drop_enabled():
        return [], dropped
    return kept, dropped


def apply_static_lemma_screen(
    lemmas: Sequence[str],
    *,
    original_forall: str,
    smt: str,
    invalid_records: Sequence[Any],
    same_as_goal: Callable[[str, str], bool],
    library_items: Sequence[Any] = (),
    ancestor_stack: Sequence[Any] = (),
) -> Tuple[List[str], List[Tuple[str, str, str]]]:
    """Drop known-invalid / same-as-goal / ancestor-cycle / library / undefined members.

    Returns ``(kept, dropped)`` where each dropped item is
    ``(lemma, reason, gate)``. ``gate`` is ``known_invalid``, ``same_as_goal``,
    ``same_as_ancestor``, ``same_as_library``, or ``undefined_symbol``.
    Known-invalid, library duplicates, and ancestor cycles are not recorded as
    invalid by the caller (ancestor hits are path cycles, often still theorems).
    Library matches always drop only that member.
    """
    from ancestor_stack import lemma_matches_ancestor
    from exp_flags import ancestor_cycle_filter_enabled

    current = list(lemmas)
    dropped: List[Tuple[str, str, str]] = []

    def _stage(gate: str, reason_for: Callable[[str], Optional[str]]) -> bool:
        nonlocal current
        kept, drop = drop_failing_members(current, reason_for)
        for lemma, reason in drop:
            dropped.append((lemma, reason, gate))
        current = kept
        return bool(current)

    if not _stage(
        "known_invalid",
        lambda lemma: "known_invalid" if lemma_known_invalid(lemma, invalid_records) else None,
    ):
        return [], dropped
    if not _stage(
        "same_as_goal",
        lambda lemma: (
            "Same as original goal" if same_as_goal(lemma, original_forall) else None
        ),
    ):
        return [], dropped
    if ancestor_cycle_filter_enabled() and ancestor_stack:
        def _ancestor_reason(lemma: str) -> Optional[str]:
            hit = lemma_matches_ancestor(
                lemma, ancestor_stack, equivalent=same_as_goal
            )
            if not hit:
                return None
            gid = str(hit.get("goal_id") or "")
            depth = hit.get("depth", "?")
            return f"cycle_detected:ancestor={gid}:depth={depth}"

        if not _stage("same_as_ancestor", _ancestor_reason):
            return [], dropped
    if library_items:
        kept_lib: List[str] = []
        for lemma in current:
            matched_id = None
            for item in library_items:
                if not isinstance(item, dict):
                    continue
                formula = str(item.get("formula") or "")
                if formula and same_as_goal(lemma, formula):
                    matched_id = str(item.get("id") or "lib")
                    break
            if matched_id:
                dropped.append(
                    (lemma, f"already_in_library:{matched_id}", "same_as_library")
                )
            else:
                kept_lib.append(lemma)
        current = kept_lib
        if not current:
            return [], dropped
    if defined_symbols_enabled():
        undef_map = lemmas_undefined_symbols(current, smt)

        def _undef_reason(lemma: str) -> Optional[str]:
            names = undef_map.get(lemma)
            if not names:
                return None
            return "undefined_symbol:" + ",".join(names)

        if not _stage("undefined_symbol", _undef_reason):
            return [], dropped
    return current, dropped


def repair_hint_for_prompt(hint: dict) -> bool:
    """Keep current-goal / usefulness ATP hints; drop subgoal copies and subgoal_failed."""
    kind = str((hint or {}).get("kind") or "")
    context = str((hint or {}).get("context") or "")
    if kind == "subgoal_failed" or context.startswith("subgoal:"):
        return False
    if kind in ("no_progress", "partial_progress", "need_rewrite"):
        return False
    return True


_SCREEN_GATE_LABEL = {
    "same_as_library": "already in lemma library",
    "same_as_ancestor": "same as a STRICT ANCESTOR on the proof path",
    "same_as_goal": "same as the CURRENT goal",
}

_STUCK_SKIP_KINDS = frozenset({
    "subgoal_failed",
    "no_progress",
    "partial_progress",
    "need_rewrite",
})


def last_screen_records(
    dropped: Sequence[Tuple[str, str, str]],
) -> List[Dict[str, str]]:
    """JSON records for the latest static-screen drops."""
    records: List[Dict[str, str]] = []
    for lemma, reason, gate in dropped or []:
        records.append({
            "lemma": str(lemma or ""),
            "reason": str(reason or ""),
            "gate": str(gate or ""),
        })
    return records


def compact_repair_snapshot(hints: Sequence[dict]) -> List[dict]:
    """Subset of repair hints stored on a failed combination for the next prompt."""
    snapshot: List[dict] = []
    keep_keys = (
        "kind",
        "context",
        "detail",
        "hard_axioms",
        "hard_axiom_scores",
        "rarely_instantiated",
        "goal_fragments",
        "induction_focus",
        "induction_formulas",
        "source_lemmas",
        "attempt_id",
        "samples",
    )
    for hint in hints or []:
        if not isinstance(hint, dict) or not repair_hint_for_prompt(hint):
            continue
        rec = {key: hint.get(key) for key in keep_keys if hint.get(key) not in (None, "", [])}
        if rec.get("kind"):
            snapshot.append(rec)
    return snapshot


def last_useless_group(failed_data: Optional[dict]) -> Any:
    groups = (failed_data or {}).get("useless_lemma_groups") or []
    return groups[-1] if groups else None


def _group_lemmas(group: Any) -> List[str]:
    if isinstance(group, list):
        return [str(item) for item in group if item]
    if isinstance(group, dict):
        return [str(item) for item in (group.get("lemmas") or []) if item]
    return []


def _exclude_source_lemmas(
    formulas: Sequence[str],
    source_lemmas: Sequence[str],
    *,
    limit: int = 4,
) -> List[str]:
    """Drop current-round candidate lemmas from a hotspot axiom list."""
    sources = [str(item) for item in source_lemmas if item]
    out: List[str] = []
    for formula in formulas:
        if not formula:
            continue
        if any(lemmas_equivalent(formula, src) for src in sources):
            continue
        out.append(formula)
        if len(out) >= limit:
            break
    return out


def format_dropped_line(item: dict) -> Optional[str]:
    """One dropped-lemma line; skip known-invalid (already in the INVALID block)."""
    gate = str((item or {}).get("gate") or "")
    if gate == "known_invalid":
        return None
    lemma = compact_formula((item or {}).get("lemma") or "")
    if not lemma:
        return None
    reason = str((item or {}).get("reason") or "").strip()
    if gate == "same_as_library":
        lib_id = ""
        if reason.startswith("already_in_library:"):
            lib_id = reason.split(":", 1)[-1].strip()
        label = f"already in lemma library {lib_id}".strip()
    elif gate == "undefined_symbol":
        label = (reason or "undefined symbol")[:MAX_REASON_CHARS]
    else:
        label = _SCREEN_GATE_LABEL.get(gate) or (reason or gate or "filtered")
        label = label[:MAX_REASON_CHARS]
    return f"    {lemma}  [{label}]"


def format_stuck_lines(
    hints: Sequence[dict],
    backend: str = "cvc5",
    *,
    omit_axiom_goal_hint: bool = False,
) -> List[str]:
    """Compact solver-stuck lines. ``need_rewrite`` is not shown (disabled)."""
    del backend
    evidence_ids = {
        str(hint.get("attempt_id") or "")
        for hint in (hints or [])
        if isinstance(hint, dict)
        and str(hint.get("kind") or "") == FORMULA_EVIDENCE_KIND
        and hint.get("attempt_id")
    }
    lines: List[str] = []
    for hint in hints or []:
        if not isinstance(hint, dict) or not repair_hint_for_prompt(hint):
            continue
        kind = str(hint.get("kind") or "")
        if kind in _STUCK_SKIP_KINDS:
            continue
        if kind == "high_difficulty_assertions" and evidence_ids:
            if str(hint.get("attempt_id") or "") not in evidence_ids:
                continue
        if kind == "high_difficulty_assertions":
            sources = [
                str(item) for item in (hint.get("source_lemmas") or []) if item
            ]
            shown_hd = _exclude_source_lemmas(
                hint.get("hard_axioms") or [], sources,
            )
            scores = hint.get("hard_axiom_scores") or {}
            if not isinstance(scores, dict):
                scores = {}
            for ax in shown_hd:
                score = scores.get(str(ax))
                if score is None:
                    # Parallel list form: same order as hard_axioms before exclude.
                    raw_hd = [str(x) for x in (hint.get("hard_axioms") or []) if x]
                    raw_sc = hint.get("hard_axiom_score_list") or []
                    if (
                        isinstance(raw_sc, list)
                        and len(raw_sc) == len(raw_hd)
                        and str(ax) in raw_hd
                    ):
                        score = raw_sc[raw_hd.index(str(ax))]
                if score is not None:
                    lines.append(
                        f"    high-difficulty axiom (d={int(score)}): "
                        f"{compact_formula(ax)}"
                    )
                else:
                    lines.append(f"    high-difficulty axiom: {compact_formula(ax)}")
            for ax in (hint.get("rarely_instantiated") or [])[:2]:
                if any(lemmas_equivalent(ax, src) for src in sources):
                    continue
                lines.append(f"    rarely instantiated: {compact_formula(ax)}")
            for frag in (hint.get("goal_fragments") or [])[:2]:
                lines.append(f"    goal fragment: {compact_formula(frag)}")
            if not (
                shown_hd
                or hint.get("rarely_instantiated")
                or hint.get("goal_fragments")
            ):
                lines.append("    high-difficulty assertions (no compact terms)")
            if shown_hd:
                lines.append(f"    {HD_DIFFICULTY_EXPLAIN}")
                if not omit_axiom_goal_hint:
                    lines.append(f"    {HD_AXIOM_GOAL_HINT}")
            continue
        if kind == FORMULA_EVIDENCE_KIND:
            samples = [
                item for item in (hint.get("samples") or [])
                if isinstance(item, dict) and item.get("formula")
            ]
            if not samples:
                continue
            lines.append("    selected solver formulas:")
            for sample in samples[:4]:
                relation = str(sample.get("relation") or "unlinked")
                profile = str(sample.get("profile") or "")
                source = str(sample.get("source") or "")
                bits = [bit for bit in (profile, source, relation) if bit]
                if relation == "matched_quantifier":
                    label = "instance of the hotspot assertion"
                elif relation == "shared_symbols":
                    label = "shares functions with a hotspot; source unconfirmed"
                else:
                    label = "not linked to a hotspot assertion"
                meta = ", ".join(bits)
                lines.append(
                    f"      {compact_formula(sample.get('formula'), MAX_FORMULA_EVIDENCE_CHARS)}"
                    + (f"  [{meta}]" if meta else "")
                )
                lines.append(f"      ({label})")
                related = str(sample.get("related_axiom") or "").strip()
                if related and relation == "matched_quantifier":
                    lines.append(
                        f"      related axiom: {compact_formula(related)}"
                    )
                elif related and relation == "shared_symbols":
                    lines.append(
                        f"      shared-function axiom: {compact_formula(related)}"
                    )
            lines.append(f"    {FORMULA_EVIDENCE_EXPLAIN}")
            continue
        detail = str(hint.get("detail") or "").strip()
        lines.append(f"    {kind}: {detail}" if detail else f"    {kind}")
        focus = hint.get("induction_focus") or []
        if focus:
            lines.append(f"    induction focus: {'; '.join(str(x) for x in focus[:4])}")
        for schema in (hint.get("induction_formulas") or [])[:2]:
            lines.append(f"    induction schema: {schema}")
    return lines


def format_attempt_feedback_for_prompt(
    failed_data: Optional[dict],
    *,
    backend: str = "cvc5",
    include_stuck: bool = True,
    suppress_advice: bool = False,
) -> str:
    """LAST ATTEMPT (latest failed C + screen drops + stuck) or INITIAL SOLVE.

    History of older useless groups stays in json; only the last group is shown.
    When ``FEEDBACK_LLM_HINTS`` is on, program HD / repair / advice / local-vs-parent
    are omitted; SOLVER HINTS is nested under LAST ATTEMPT only if the diagnoser
    produced an injectable block. ``suppress_advice`` is kept for callers.
    """
    from feedback_llm_hints import format_llm_hints_lines, llm_hints_eligible

    data = failed_data if isinstance(failed_data, dict) else {}
    group = last_useless_group(data)
    kept = _group_lemmas(group)
    dropped = [
        item for item in (data.get("last_screen") or [])
        if isinstance(item, dict)
    ]
    status = ""
    group_hints: Optional[Sequence[dict]] = None
    if isinstance(group, dict):
        status = str(group.get("status") or "").strip()
        if "repair_hints" in group:
            group_hints = group.get("repair_hints") or []
    hints: Sequence[dict] = (
        group_hints if group_hints is not None else (data.get("repair_hints") or [])
    )
    llm_rec = data.get("llm_hints") if isinstance(data.get("llm_hints"), dict) else {}
    llm_lines = (
        format_llm_hints_lines(llm_rec, indent="    ")
        if llm_hints_eligible(data) else []
    )
    use_llm_hints = bool(llm_lines)
    # Diagnoser owns HD/repair text. Do not fall back to the program block
    # when the flag is on (including NO_ACTION / skipped diagnoser).
    want_program = (
        include_stuck
        and not use_llm_hints
        and not feedback_llm_hints_enabled()
    )
    want_advice = (
        want_program and prompt_advice_enabled() and not suppress_advice
    )
    want_local = want_program and obligation_tree_enabled()
    advice = (
        advice_from_failed_data(data, backend=backend, has_kept=bool(kept))
        if want_advice else None
    )
    stuck_lines = format_stuck_lines(
        hints, backend, omit_axiom_goal_hint=advice is not None,
    ) if want_program else []
    local_lines = format_local_vs_parent_lines(data) if want_local else []
    advice_lines = format_advice_lines(advice) if want_advice else []
    drop_lines = [line for line in (format_dropped_line(item) for item in dropped) if line]
    has_attempt = bool(kept or drop_lines)
    if (
        not has_attempt
        and not stuck_lines
        and not local_lines
        and not advice_lines
        and not llm_lines
    ):
        return ""

    parts: List[str] = []
    if has_attempt:
        status_bit = f", status={status}" if status else ""
        parts.append(f"\nLAST ATTEMPT (did not prove the CURRENT goal{status_bit}):")
        if kept:
            parts.append("  kept:")
            for i, lemma in enumerate(kept, 1):
                parts.append(f"    {i}. {lemma}")
        else:
            parts.append("  kept: (none; all candidates were filtered)")
        if drop_lines:
            parts.append("  dropped:")
            parts.extend(drop_lines)
        if llm_lines:
            parts.extend(llm_lines)
        elif stuck_lines or local_lines or advice_lines:
            parts.append("  repair hints:")
            parts.extend(stuck_lines)
            parts.extend(local_lines)
            parts.extend(advice_lines)
        parts.append("  You may refine kept lemmas or propose a different set.")
        return "\n".join(parts)

    parts.append(
        "\nINITIAL SOLVE (no candidate lemmas yet; did not prove CURRENT goal):"
    )
    if llm_lines:
        parts.extend(llm_lines)
    else:
        parts.append("  repair hints:")
        parts.extend(stuck_lines)
        parts.extend(local_lines)
        parts.extend(advice_lines)
    parts.append("  Propose auxiliary lemmas that help the solver prove the goal.")
    return "\n".join(parts)


def attach_source_lemmas(
    hints: Sequence[dict],
    lemmas: Optional[Sequence[str]] = None,
    *,
    context: Optional[str] = None,
) -> List[dict]:
    """Copy hints and record which candidate lemmas the mix run used."""
    formulas = [
        normalize_lemma_formula(str(item))
        for item in (lemmas or [])
        if normalize_lemma_formula(str(item))
    ]
    attached: List[dict] = []
    for hint in hints or []:
        rec = dict(hint)
        rec["source_lemmas"] = list(formulas)
        if context:
            rec["context"] = context
        attached.append(rec)
    return attached


def usefulness_source_lemmas(hints: Sequence[dict]) -> List[str]:
    """Candidate lemmas from the latest usefulness-check mix among these hints."""
    found: List[str] = []
    for hint in hints or []:
        if str(hint.get("context") or "") != "usefulness_check":
            continue
        formulas = [
            normalize_lemma_formula(str(item))
            for item in (hint.get("source_lemmas") or [])
            if normalize_lemma_formula(str(item))
        ]
        if formulas:
            found = formulas
    return found


def format_repair_header(backend: str, hints: Sequence[dict]) -> List[str]:
    """Header for the repair block. Usefulness-failed C is listed before the hints."""
    title = f"\nSOLVER-GUIDED REPAIR (from {backend} failure analysis)."
    lemmas = usefulness_source_lemmas(hints)
    if not lemmas:
        return [title + " Use these hints to choose the NEXT lemmas:"]
    lines = [title]
    shown = lemmas[:MAX_MIX_SOURCE_LEMMAS]
    for i, formula in enumerate(shown, 1):
        lines.append(f"  C{i}: {compact_formula(formula)}")
    extra = len(lemmas) - len(shown)
    if extra > 0:
        lines.append(f"  ... and {extra} more")
    lines.append(
        "Failed to prove the goal using the above lemmas and produced hints. "
        "Use these hints to choose the NEXT lemmas:"
    )
    return lines


def tree_status_from_child_data(failed_data: Optional[dict]) -> Tuple[str, str]:
    """Map this child's json to invalid vs failed. Nested descendants are not inherited.

    Two callers:
    - obligation-tree node status (only when ``OBLIGATION_TREE`` is on)
    - parent INVALID vs unproved (independent of the tree flag)
    """
    data = failed_data or {}
    outcome = data.get("node_outcome") or {}
    kind = str(outcome.get("kind") or "")
    reason = str(outcome.get("reason") or "").strip()
    diag_status = str((data.get("baseline_diag") or {}).get("status") or "").lower()
    if kind == "invalid" or diag_status == "sat":
        return "invalid", reason or (
            "solver:sat" if diag_status == "sat" else "invalid"
        )
    return "failed", ""
