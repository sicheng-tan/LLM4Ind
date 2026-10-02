"""Short-prove scheme obligations with fixed profiles / timeout."""

from __future__ import annotations

import logging
import re
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Callable, List, Optional, Sequence, Tuple

from lemma_harvest import write_negated_lemma_smt

from .constants import (
    GOAL_GATE_TIMEOUT_S,
    PROVE_PROFILES,
    PROVE_TIMEOUT_S,
    SCHEME_PROVE_MAX_OBLS,
    VAMPIRE_PROVE_PROFILES,
)
from .types import SchemeAttempt, SchemeObligation

ProveFn = Callable[[Path, int, Sequence[str]], object]


def default_cvc_prove(smt_path: Path, timeout: int, profiles: Sequence[str]):
    from cvc5_runner import run_cvc

    names = list(profiles) if profiles else list(PROVE_PROFILES)
    return run_cvc(
        smt_path,
        timeout,
        profiles=names,
        collect_stats=False,
        collect_difficulty=False,
    )


def default_vampire_prove(smt_path: Path, timeout: int, profiles: Sequence[str]):
    """Race Vampire scheme profiles (same schedule as usefulness on Vampire Mate)."""
    from vampire_runner import VAMPIRE_PROFILES, run_vampire_race

    names = [p for p in (profiles or ()) if p in VAMPIRE_PROFILES]
    if not names:
        names = list(VAMPIRE_PROVE_PROFILES)
    return run_vampire_race(
        smt_path,
        timeout,
        names,
        collect_stats=False,
        collect_ucore=False,
        show_induction=False,
    )

def _smt_with_measure_prelude(smt_content: str, attempt: SchemeAttempt) -> str:
    prelude = (attempt.measure_prelude or "").strip()
    if not prelude:
        return smt_content
    from obligation_tree import upgrade_smt_logic_for_text

    # UFDT + Int μ helpers must become UFDTLIA before short-prove / gate.
    base = upgrade_smt_logic_for_text(smt_content, prelude)
    if re.search(r";\s*proof goal\b", base, flags=re.IGNORECASE):
        return re.sub(
            r";\s*proof goal\b",
            prelude + "\n; proof goal",
            base,
            count=1,
            flags=re.IGNORECASE,
        )
    return prelude + "\n" + base


def prove_obligations(
    attempt: SchemeAttempt,
    *,
    smt_content: str,
    work_dir: Path,
    goal_name: str,
    prove_fn: Optional[ProveFn] = None,
    timeout_s: int = PROVE_TIMEOUT_S,
    profiles: Sequence[str] = PROVE_PROFILES,
    only: Optional[Sequence[str]] = None,
) -> SchemeAttempt:
    """Short-prove open obligations; update status in place.

    Proves ``nonneg`` / easy ctors first, then injects proved formulas as
    axioms when attempting the remaining bridges (needed so e.g. ``hsize≥0``
    unlocks ``plus`` guards before ``hsize(merge)=+``).
    """
    if not attempt.validated or attempt.skipped:
        return attempt
    prove = prove_fn or default_cvc_prove
    targets = [
        o for o in attempt.obligations
        if o.status not in ("proved", "invalid")
        and (only is None or o.obl_id in only)
    ]
    if not targets:
        return attempt

    work_dir = Path(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)
    smt_use = _smt_with_measure_prelude(smt_content, attempt)

    # Prefer nonneg / R1 bases first; then descent; then R1 step / R2.
    def _prio(o: SchemeObligation) -> Tuple[int, str]:
        c = o.ctor or ""
        if c == "nonneg":
            return (0, o.obl_id)
        if c == "mu_hom_base" or c.endswith("_hleaf") or "hleaf" in o.obl_id:
            return (1, o.obl_id)
        if c.startswith("descent_") or c.endswith("_le"):
            return (2, o.obl_id)
        if c in ("mu_hom_step", "mu_prop_preserve"):
            return (3, o.obl_id)
        if c == "mu_lt" or "merge_lt" in c:
            return (4, o.obl_id)
        return (5, o.obl_id)

    ordered = sorted(targets, key=_prio)
    if len(ordered) > SCHEME_PROVE_MAX_OBLS:
        for o in ordered[SCHEME_PROVE_MAX_OBLS:]:
            if o.status not in ("proved", "invalid"):
                o.status = "frontier"
                o.no_nest = True
                if o.obl_id not in attempt.frontier_ids:
                    attempt.frontier_ids.append(o.obl_id)
        ordered = ordered[:SCHEME_PROVE_MAX_OBLS]

    # Phase 1: prove priority-0/1 in parallel (no cross-deps among them usually)
    early = [o for o in ordered if _prio(o)[0] <= 1]
    late = [o for o in ordered if _prio(o)[0] > 1]

    def _run_batch(batch: List[SchemeObligation], smt: str) -> None:
        if not batch:
            return

        def _one(obl: SchemeObligation):
            path = work_dir / f"{goal_name}__scheme_{obl.obl_id}.smt2"
            write_negated_lemma_smt(smt, obl.formula, path)
            result = prove(path, int(timeout_s), profiles)
            return obl, result

        max_workers = min(4, len(batch))
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            futures = [pool.submit(_one, o) for o in batch]
            for fut in as_completed(futures):
                try:
                    obl, result = fut.result()
                except Exception as exc:
                    logging.warning("scheme prove failed: %s", exc)
                    continue
                proved = bool(getattr(result, "proved", False))
                status = str(getattr(result, "status", "") or "").strip().lower()
                obl.prove_status = status
                obl.prove_elapsed = float(getattr(result, "elapsed", 0.0) or 0.0)
                if proved:
                    obl.status = "proved"
                elif status == "sat":
                    # Negated lemma is sat ⇒ original formula is false.
                    obl.status = "invalid"
                else:
                    obl.status = "failed"

    _run_batch(early, smt_use)

    proved_axioms = [
        o.formula for o in attempt.obligations
        if o.status == "proved" and o.formula
    ]
    smt_late = smt_use
    if proved_axioms and late:
        block = (
            "; induction scheme proved bridges (cascaded)\n"
            + "\n".join(f"(assert {f})" for f in proved_axioms)
            + "\n; induction scheme proved bridges end\n"
        )
        if re.search(r";\s*proof goal\b", smt_use, flags=re.IGNORECASE):
            smt_late = re.sub(
                r";\s*proof goal\b",
                block + "; proof goal",
                smt_use,
                count=1,
                flags=re.IGNORECASE,
            )
        else:
            smt_late = block + smt_use

    _run_batch(late, smt_late)
    return attempt


def write_goal_gate_smt(
    smt_content: str,
    obligations: Sequence[SchemeObligation],
    dest: Path,
) -> bool:
    """Assert base/step as axioms; keep original ``(assert (not G))`` goal.

    Returns False if the SMT has no ``; proof goal`` marker to anchor inserts.
    """
    axioms = "\n".join(
        f"(assert {o.formula})" for o in obligations if o.formula
    )
    if not axioms:
        return False
    if not re.search(r";\s*proof goal\b", smt_content, flags=re.IGNORECASE):
        return False
    gated = re.sub(
        r";\s*proof goal\b",
        (
            "; induction scheme goal-gate axioms (base/step)\n"
            f"{axioms}\n"
            "; induction scheme goal-gate axioms end\n"
            "; proof goal"
        ),
        smt_content,
        count=1,
        flags=re.IGNORECASE,
    )
    Path(dest).write_text(gated, encoding="utf-8")
    return True


def prove_goal_gate(
    attempt: SchemeAttempt,
    *,
    smt_content: str,
    work_dir: Path,
    goal_name: str,
    prove_fn: Optional[ProveFn] = None,
    timeout_s: int = GOAL_GATE_TIMEOUT_S,
    profiles: Sequence[str] = PROVE_PROFILES,
    enabled: bool = True,
) -> SchemeAttempt:
    """Try ``axioms ∧ library ∧ base ∧ step ⊢ G`` (original negated goal).

    ``smt_content`` should already include the lemma library when the caller
    used ``solver_smt_content``. On ``failed``/``error``, sets
    ``goal_gate_status`` so the dispatcher refuses prompt/NEST. On
    ``timeout``, obligations may still short-prove / nest; only
    ``kind=scheme`` close stays blocked until a later gate proves.
    """
    if not enabled:
        attempt.goal_gate_status = "off"
        return attempt
    if not attempt.validated or attempt.skipped or not attempt.obligations:
        attempt.goal_gate_status = "skipped"
        return attempt

    work_dir = Path(work_dir)
    work_dir.mkdir(parents=True, exist_ok=True)
    path = work_dir / f"{goal_name}__scheme_goal_gate.smt2"
    smt_use = _smt_with_measure_prelude(smt_content, attempt)
    if not write_goal_gate_smt(smt_use, attempt.obligations, path):
        attempt.goal_gate_status = "error"
        logging.warning("scheme goal-gate: missing proof-goal markers for %s", goal_name)
        return attempt

    prove = prove_fn or default_cvc_prove
    try:
        result = prove(path, int(timeout_s), profiles)
    except Exception as exc:
        logging.warning("scheme goal-gate failed: %s", exc)
        attempt.goal_gate_status = "error"
        return attempt

    attempt.goal_gate_elapsed = float(getattr(result, "elapsed", 0.0) or 0.0)
    status = str(getattr(result, "status", "") or "").lower()
    if bool(getattr(result, "proved", False)):
        attempt.goal_gate_status = "proved"
    elif status == "timeout":
        attempt.goal_gate_status = "timeout"
    else:
        attempt.goal_gate_status = "failed"
    return attempt


def mark_frontier(attempt: SchemeAttempt, obl_ids: Sequence[str]) -> None:
    for oid in obl_ids:
        if oid not in attempt.frontier_ids:
            attempt.frontier_ids.append(oid)
    by_id = {o.obl_id: o for o in attempt.obligations}
    for oid in obl_ids:
        obl = by_id.get(oid)
        if obl is not None:
            obl.no_nest = True
            if obl.status not in ("proved", "invalid"):
                obl.status = "frontier"
