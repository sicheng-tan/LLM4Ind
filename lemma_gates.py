"""Fail-fast gates for lemma subgoals: defined symbols, sat abort, LLM reason.

Boolean flags default on (current method). Set them off in paper.env to restore
the original loop. CHILD_LLM_ATTEMPTS=0 keeps the root 2N budget at every depth.
The diagnosis suffix is never attached at depth 0; children follow LLM_LEMMA_DIAGNOSIS.
After a child node's attempts are exhausted, one extra diagnosis-only LLM call
judges whether the CURRENT goal is invalid from the obligation tree only
(no invalid/unproved/repair/progress/routing blocks).
"""

from __future__ import annotations

import os
import re
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from exp_flags import _flag_enabled

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
_REASON_LINE = re.compile(
    r"^[;\s]*reason\s*:\s*(.+)$",
    flags=re.IGNORECASE,
)

_RESERVED = frozenset({
    "forall", "exists", "assert", "and", "or", "not", "xor", "ite", "let", "as",
    "true", "false", "distinct", "par", "match", "case", "lambda", "!", "_",
    "check-sat", "exit", "set-logic", "set-option", "declare-fun", "define-fun",
    "declare-const", "declare-datatype", "declare-datatypes",
})

DIAGNOSIS_PROMPT_SUFFIX = (
    "\n; If the CURRENT goal is invalid (not a theorem of the given axioms, "
    "for example it is missing hypotheses, it contradicts existing axioms or lemmas, "
    "or a used function is only declared with no defining assert), "
    "output no lemmas and write one line:\n"
    "; reason: <short explanation>\n"
    "; If a previously proposed child lemma is marked invalid, use that invalid mark "
    "and its reason to decide whether the CURRENT goal is also invalid "
    "(e.g. it depends on the same missing definition or contradiction).\n"
)

FINAL_DIAGNOSIS_PROMPT_SUFFIX = (
    "\n; FINAL CHECK (do not propose new lemmas).\n"
    "; Using the obligation tree "
    "(especially child lemmas marked invalid and their reasons), "
    "decide whether the CURRENT goal is a theorem of the given axioms.\n"
    "; If it is INVALID (not a theorem), output invalid and write one line:\n"
    "; reason: <short explanation>\n"
    "; If it MAY still be a theorem, output failed.\n"
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


def should_run_final_diagnosis(depth: int = 0) -> bool:
    """Extra invalid-check LLM call after child attempts are exhausted."""
    return int(depth or 0) >= 1 and llm_lemma_diagnosis_enabled()


def parse_llm_reason(raw: Optional[str]) -> Optional[str]:
    if not raw:
        return None
    for line in str(raw).splitlines():
        match = _REASON_LINE.match(line.strip())
        if match:
            reason = match.group(1).strip()
            if reason:
                return reason[:MAX_REASON_CHARS]
    return None


def parse_final_diagnosis(raw: Optional[str]) -> Tuple[str, Optional[str]]:
    """Parse extra-check output into ('invalid'|'failed', reason).

    Unparsed or open verdicts are failed (this node stays failed, not invalid).
    ``still_open`` is accepted as an alias of ``failed``.
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


def repair_hint_for_prompt(hint: dict) -> bool:
    """Keep current-goal / usefulness ATP hints; drop subgoal copies and subgoal_failed."""
    kind = str((hint or {}).get("kind") or "")
    context = str((hint or {}).get("context") or "")
    if kind == "subgoal_failed" or context.startswith("subgoal:"):
        return False
    return True


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
