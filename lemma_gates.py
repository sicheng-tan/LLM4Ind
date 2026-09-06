"""Fail-fast gates for lemma subgoals: defined symbols, sat abort, LLM reason.

Boolean flags default on (current method). Set them off in paper.env to restore
the original loop. CHILD_LLM_ATTEMPTS=0 keeps the root 2N budget at every depth.
The diagnosis suffix is never attached at depth 0; children follow LLM_LEMMA_DIAGNOSIS.
After a child node's attempts are exhausted, one extra diagnosis-only LLM call
judges whether the CURRENT goal is invalid from the last well-formed obligation
tree only (no invalid/unproved/repair/progress/routing blocks). Skip the extra
call when that tree does not exist.
LLM_PARSE_RETRIES extra LLM calls after a format parse failure stay inside the
same prove-run attempt (HTTP retries are LLM_MAX_RETRIES and unrelated).
"""

from __future__ import annotations

import os
import re
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from exp_flags import _flag_enabled
from obligation_tree import compact_formula, normalize_lemma_formula

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
    "If a previously proposed child lemma is marked invalid, use that invalid mark "
    "and its reason to decide whether the CURRENT goal is also invalid "
    "(e.g. it depends on the same missing definition or contradiction).\n"
)

FINAL_DIAGNOSIS_PROMPT_SUFFIX = (
    "\nFINAL CHECK (do not propose lemmas; do not use <lemma> tags).\n"
    "Using the obligation tree "
    "(especially child lemmas marked invalid and their reasons), "
    "decide whether the CURRENT goal is a theorem of the given axioms.\n"
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
MAX_PARSE_RETRY_SNIPPET = 1500
PARSE_RETRY_USER = (
    "FORMAT ERROR: the previous reply could not be parsed because it was "
    "missing the required output tags. Reply again using exactly:\n"
    "<output>\n"
    "<lemma>(forall ...)</lemma>\n"
    "</output>\n"
    "If you have no lemmas, output <output></output>. "
    "You may still write ; INVALID_GOAL: <short explanation> on its own line "
    "outside the tags. Do not omit the tags."
)


def subgoal_sat_abort_enabled() -> bool:
    return _flag_enabled("SUBGOAL_SAT_ABORT")


def defined_symbols_enabled() -> bool:
    return _flag_enabled("LEMMA_DEFINED_SYMBOLS")


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


def should_run_final_diagnosis(depth: int = 0, *, has_tree: bool = True) -> bool:
    """Extra invalid-check LLM call after child attempts are exhausted.

    Requires a last well-formed obligation tree. Empty / invalid / useless
    attempts do not create one, and the extra call is skipped.
    """
    return (
        int(depth or 0) >= 1
        and llm_lemma_diagnosis_enabled()
        and bool(has_tree)
    )


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
    raw: Optional[str], *, diagnosis_only: bool = False
) -> bool:
    """True when missing lemma output tags should not abort the attempt.

    Final diagnosis never wraps lemmas. Child generation may also emit only
    ``; INVALID_GOAL:`` (the diagnosis suffix) instead of a lemma block.
    """
    if diagnosis_only:
        return True
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


def _foralls_from_text(text: str) -> List[str]:
    tagged = _LEMMA_TAG.findall(text or "")
    if tagged:
        found: List[str] = []
        for body in tagged:
            formula = extract_balanced_forall(body.strip())
            if formula:
                found.append(formula)
        return found
    found = []
    pos = 0
    blob = text or ""
    while True:
        match = _FORALL_START.search(blob, pos)
        if not match:
            break
        formula = extract_balanced_forall(blob[match.start():])
        if not formula:
            break
        found.append(formula)
        pos = match.start() + len(formula)
    return found


def parse_llm_lemmas(response: Optional[str]) -> List[str]:
    """Extract SMT lemmas from an LLM reply.

    Preferred shape::

        <output>
        <lemma>(forall ...)</lemma>
        </output>

    Also accepts ``<lemmas>``, bare ``<lemma>`` tags, and the legacy
    ``; Output begin`` / ``; Output end`` block.
    """
    text = response or ""
    match = _OUTPUT_TAG.search(text)
    if match:
        return _foralls_from_text(match.group(1))
    tagged = _LEMMA_TAG.findall(text)
    if tagged:
        return _foralls_from_text(
            "".join(f"<lemma>{body}</lemma>" for body in tagged)
        )
    legacy = _LEGACY_OUTPUT.search(text)
    if legacy:
        return _foralls_from_text(legacy.group(1))
    raise ValueError("响应格式错误，缺少输出标记")


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


def lemmas_known_invalid(
    lemmas: Sequence[str], invalid_lemmas: Sequence[Any]
) -> List[str]:
    return [lemma for lemma in lemmas if lemma_known_invalid(lemma, invalid_lemmas)]


def repair_hint_for_prompt(hint: dict) -> bool:
    """Keep current-goal / usefulness ATP hints; drop subgoal copies and subgoal_failed."""
    kind = str((hint or {}).get("kind") or "")
    context = str((hint or {}).get("context") or "")
    if kind == "subgoal_failed" or context.startswith("subgoal:"):
        return False
    return True


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
    """Status of THIS child goal only. A nested invalid descendant is not inherited."""
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
