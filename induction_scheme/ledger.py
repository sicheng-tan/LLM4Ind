"""Persist / load scheme_attempts ledger and render profiler diagnosis."""

from __future__ import annotations

import logging
from typing import Any, Dict, List, Optional, Sequence

from .constants import SCHEME_ATTEMPTS_KEY
from .types import SchemeAttempt


def load_scheme_attempts(failed_data: Optional[dict]) -> List[SchemeAttempt]:
    data = failed_data if isinstance(failed_data, dict) else {}
    raw = data.get(SCHEME_ATTEMPTS_KEY) or []
    if not isinstance(raw, list):
        return []
    out: List[SchemeAttempt] = []
    for item in raw:
        if isinstance(item, dict):
            out.append(SchemeAttempt.from_dict(item))
    return out


def save_scheme_attempt(
    failed_data: dict,
    attempt: SchemeAttempt,
    *,
    replace_same_goal: bool = True,
) -> dict:
    """Append (or replace latest same goal_name) scheme attempt into failed_data."""
    data = failed_data if isinstance(failed_data, dict) else {}
    entries = list(data.get(SCHEME_ATTEMPTS_KEY) or [])
    payload = attempt.to_dict()
    if replace_same_goal and entries:
        for i in range(len(entries) - 1, -1, -1):
            if isinstance(entries[i], dict) and entries[i].get("goal_name") == attempt.goal_name:
                entries[i] = payload
                data[SCHEME_ATTEMPTS_KEY] = entries
                return data
    entries.append(payload)
    # Keep a bounded tail.
    if len(entries) > 16:
        entries = entries[-16:]
    data[SCHEME_ATTEMPTS_KEY] = entries
    return data


def latest_scheme_attempt(
    failed_data: Optional[dict],
    *,
    goal_name: Optional[str] = None,
) -> Optional[SchemeAttempt]:
    attempts = load_scheme_attempts(failed_data)
    if not attempts:
        return None
    if goal_name:
        for att in reversed(attempts):
            if att.goal_name == goal_name:
                return att
    return attempts[-1]


def harvest_scheme_refuted_to_invalid(
    attempt: SchemeAttempt,
    base_path: Optional[str],
    *,
    goal_name: Optional[str] = None,
) -> int:
    """Record solver-refuted (sat) scheme obligations into ``invalid_lemmas``."""
    if not base_path or not attempt or attempt.skipped:
        return 0
    gname = (goal_name or attempt.goal_name or "").strip()
    if not gname:
        return 0
    try:
        import Mate_new as mate
    except Exception:
        try:
            import Mate_new_vampire as mate  # type: ignore
        except Exception:
            return 0
    n = 0
    for obl in attempt.obligations:
        if obl.status != "invalid" and str(obl.prove_status or "").lower() != "sat":
            continue
        formula = (obl.formula or "").strip()
        if not formula:
            continue
        reason = f"scheme_refuted:{obl.ctor or obl.obl_id or 'obl'}"
        try:
            mate.add_invalid_lemma(base_path, gname, formula, reason)
            n += 1
        except Exception as exc:
            logging.warning("scheme invalid harvest failed: %s", exc)
    return n


def harvest_scheme_proved_to_library(
    attempt: SchemeAttempt,
    base_path: Optional[str],
    *,
    depth: int = 0,
    attempt_n: int = 0,
) -> int:
    """Pin scheme-proved obligations into the lemma library (skip abstract WF)."""
    if not base_path or not attempt or attempt.skipped:
        return 0
    try:
        from obligation_tree import add_proved_lemma, lemma_library_enabled
    except Exception:
        return 0
    if not lemma_library_enabled():
        return 0
    n = 0
    for obl in attempt.obligations:
        if obl.status != "proved" or not (obl.formula or "").strip():
            continue
        # Abstract WF is an induction principle shell, not a reusable lemma.
        if obl.ctor == "wf":
            continue
        lib_id = add_proved_lemma(
            base_path,
            obl.formula,
            origin=f"scheme:{attempt.goal_name}:{obl.obl_id}",
            attempt=attempt_n,
            depth=depth,
            role="pin",
        )
        if lib_id:
            n += 1
    return n


def scheme_prompt_formulas(
    failed_data: Optional[dict],
    *,
    goal_name: Optional[str] = None,
) -> List[str]:
    """Formulas that ``format_scheme_prompt_block`` would show for this node."""
    att = latest_scheme_attempt(failed_data, goal_name=goal_name)
    if att is None or not att.prompt_eligible():
        return []
    out: List[str] = []
    for o in att.obligations:
        if o.status != "proved" or not (o.formula or "").strip():
            continue
        if o.kind in ("base", "step"):
            out.append(o.formula)
        elif (
            o.kind == "measure"
            and o.ctor not in ("nonneg", "wf")
        ):
            out.append(o.formula)
    return out


def filter_library_excluding_current_scheme(
    library: Sequence[Any],
    failed_data: Optional[dict],
    *,
    goal_name: Optional[str] = None,
) -> List[Any]:
    """Drop library rows that duplicate the current node's scheme prompt block.

    Ancestor ``scheme:…`` pins stay. SMT injection is unchanged (full library).
    """
    items = list(library or [])
    if not items:
        return items
    formulas = scheme_prompt_formulas(failed_data, goal_name=goal_name)
    if not formulas:
        return items
    try:
        from obligation_tree import lemmas_equivalent
    except Exception:
        from smt_patterns import normalize_lemma_formula

        def lemmas_equivalent(a: str, b: str) -> bool:  # type: ignore
            return normalize_lemma_formula(a) == normalize_lemma_formula(b)

    return [
        item for item in items
        if not any(
            lemmas_equivalent(str((item or {}).get("formula") or ""), f)
            for f in formulas
        )
    ]


def format_scheme_prompt_block(
    failed_data: Optional[dict],
    *,
    goal_name: Optional[str] = None,
) -> str:
    """Ledger for lemma prompts: **proved** obligations only.

    Keeps induct var / μ headers. Splits measure facts into descent vs semantic.
    Omits open/timeout items. Hard gate-fail suppresses the block.
    """
    from .bridges import bridge_role

    att = latest_scheme_attempt(failed_data, goal_name=goal_name)
    if att is None or not att.prompt_eligible():
        return ""

    struct_proved = [
        o for o in att.obligations
        if o.kind in ("base", "step") and o.status == "proved"
    ]
    meas_proved = [
        o for o in att.obligations
        if o.kind == "measure"
        and o.status == "proved"
        and o.ctor not in ("nonneg", "wf")
        and o.formula
    ]
    if not struct_proved and not meas_proved:
        return ""

    axis = "measure" if att.measure_fun or att.bridge_primary else "structural"
    if struct_proved and meas_proved:
        axis = "structural+measure"
    header_bits = [f"induct=`{att.induct_var}`:`{att.induct_sort}`", f"axis={axis}"]
    if att.measure_fun:
        header_bits.append(f"μ=`{att.measure_fun}`")
    lines = [
        "\nINDUCTION SCHEME (proved short-prove facts for CURRENT goal only):",
        f"  - " + " ".join(header_bits),
    ]
    if struct_proved:
        lines.append(
            "  Proved structural cases "
            f"(induction on `{att.induct_var}` — safe to reuse):"
        )
        for o in struct_proved[:8]:
            if o.formula:
                lines.append(f"  - [{o.kind}@{o.ctor}] {o.formula}")
            else:
                lines.append(f"  - [{o.kind}@{o.ctor}]")

    descent = [o for o in meas_proved if bridge_role(o.ctor) == "descent"]
    semantic = [o for o in meas_proved if bridge_role(o.ctor) == "semantic"]
    other = [
        o for o in meas_proved
        if bridge_role(o.ctor) not in ("descent", "semantic")
    ]
    if descent:
        mu = att.measure_fun or "μ"
        lines.append(
            f"  Proved descent bridges (`{mu}` does not increase on recursive args):"
        )
        for o in descent[:6]:
            lines.append(f"  - [{o.ctor}] {o.formula}")
    if semantic:
        lines.append(
            "  Proved μ-homomorphism / invariant bridges "
            "(safe equalities about μ or guards — prefer these for the root):"
        )
        for o in semantic[:6]:
            lines.append(f"  - [{o.ctor}] {o.formula}")
    if other:
        lines.append("  Proved other measure facts:")
        for o in other[:4]:
            lines.append(f"  - [{o.ctor}] {o.formula}")
    # Strategy hint when measure facts exist but observer lemmas are for the LLM.
    if att.measure_fun or att.bridge_primary:
        lines.append(
            "  Hint: if the goal equates an observer O on a transformer F "
            "(e.g. sorting), prefer lemmas of the form "
            "`(= (O (F x)) (O x))` or `(= (O (O x)) (O x))` — "
            "scheme does not emit those automatically."
        )
    return "\n".join(lines) + "\n"


def scheme_formulas_for_usefulness(_attempt: Optional[SchemeAttempt]) -> List[str]:
    """Scheme obligations never enter usefulness C."""
    return []


def attempt_dict_summary(attempt: SchemeAttempt) -> Dict[str, Any]:
    return {
        "var": attempt.induct_var,
        "sort": attempt.induct_sort,
        "validated": attempt.validated,
        "closed": attempt.closed,
        "close_reason": attempt.close_reason,
        "n_obl": len(attempt.obligations),
        "n_proved": sum(1 for o in attempt.obligations if o.status == "proved"),
        "frontier": list(attempt.frontier_ids),
        "skipped": attempt.skipped,
        "skip_reason": attempt.skip_reason,
    }
