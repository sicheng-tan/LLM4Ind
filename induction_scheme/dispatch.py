"""Dispatch: short prove, NEST children, frontier backup, parent close."""

from __future__ import annotations

import logging
import threading
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, List, Optional, Sequence, Set

from exp_stats import log_exp

from .constants import (
    DEPTH_COST,
    GOAL_GATE_TIMEOUT_S,
    NEST,
    PROVE_PROFILES,
    PROVE_TIMEOUT_S,
    SCHEME_DISPATCH_KEY,
    SCHEME_PENDING_KEY,
)
from .generate import generate_scheme
from .ledger import save_scheme_attempt, scheme_formulas_for_usefulness
from .prove import mark_frontier, prove_goal_gate, prove_obligations
from .types import SchemeAttempt, SchemeObligation, SchemeRoundResult

ProveFn = Callable[[Path, int, Sequence[str]], object]
ChildProveFn = Callable[..., bool]


@dataclass
class SchemeSession:
    """Background generate+prove overlapping an LLM attempt."""

    future: Optional[Future] = None
    result: Optional[SchemeRoundResult] = None
    _lock: threading.Lock = field(default_factory=threading.Lock)

    def start(self, fn: Callable[[], SchemeRoundResult]) -> None:
        pool = ThreadPoolExecutor(max_workers=1)
        self.future = pool.submit(fn)
        # Don't keep the pool open forever; shutdown after submit with wait=False
        # would cancel — instead attach a done callback to shutdown.
        fut = self.future

        def _shutdown(_f):
            pool.shutdown(wait=False)

        fut.add_done_callback(_shutdown)

    def wait(self, timeout: Optional[float] = None) -> Optional[SchemeRoundResult]:
        with self._lock:
            if self.result is not None:
                return self.result
            if self.future is None:
                return None
            try:
                self.result = self.future.result(timeout=timeout)
            except Exception as exc:
                logging.warning("scheme session failed: %s", exc)
                self.result = None
            return self.result


def run_scheme_round(
    *,
    smt_content: str,
    goal_name: str,
    work_dir: Path,
    mode: str = "structural",
    depth: int = 0,
    nest_budget: int = NEST,
    max_depth: int = 3,
    current_goal: Optional[str] = None,
    prove_fn: Optional[ProveFn] = None,
    do_prove: bool = True,
) -> SchemeRoundResult:
    """Generate + validate + optional short prove. Does not nest or close parent.

    ``mode=both``: short-prove **all** viable axes (structural and measure), then
    merge nest/harvest. Gate hard-fail (sat) drops that axis only; timeout does
    not. Close uses a non-bridge axis that fully proved; bridge-primary never
    closes alone. Winner-take-all was dropped — before prove it is hard to know
    which obligation set is the right one.
    """
    from .generate import generate_scheme, generate_scheme_candidates
    from smt_patterns import normalize_lemma_formula

    mode_l = (mode or "structural").strip().lower()
    work_dir = Path(work_dir)

    if mode_l == "both":
        candidates = generate_scheme_candidates(
            smt_content,
            goal_name=goal_name,
            mode="both",
            depth=depth,
            nest_budget=nest_budget,
            current_goal=current_goal,
        )
    else:
        att0 = generate_scheme(
            smt_content,
            goal_name=goal_name,
            mode=mode_l,
            depth=depth,
            nest_budget=nest_budget,
            current_goal=current_goal,
        )
        candidates = [] if att0.skipped or not att0.validated else [att0]

    if not candidates:
        attempt = generate_scheme(
            smt_content,
            goal_name=goal_name,
            mode=mode_l,
            depth=depth,
            nest_budget=nest_budget,
            current_goal=current_goal,
        )
        assert scheme_formulas_for_usefulness(attempt) == []
        log_exp(
            "scheme_generate",
            goal=goal_name,
            skipped=attempt.skipped,
            skip_reason=attempt.skip_reason,
            validated=attempt.validated,
            errors=",".join(attempt.validate_errors),
        )
        return SchemeRoundResult(attempt=attempt)

    for att in candidates:
        assert scheme_formulas_for_usefulness(att) == []

    if not do_prove:
        return SchemeRoundResult(attempt=candidates[0])

    try:
        from exp_flags import induction_scheme_goal_gate_enabled
        gate_on = induction_scheme_goal_gate_enabled()
    except Exception:
        gate_on = True

    viable: List[SchemeAttempt] = []
    for i, attempt in enumerate(candidates):
        tag = "meas" if attempt.measure_fun else "struct"
        sub = work_dir / f"cand{i}_{tag}"
        soft_gate = bool(getattr(attempt, "bridge_primary", False))
        if gate_on and not soft_gate:
            prove_goal_gate(
                attempt,
                smt_content=smt_content,
                work_dir=sub,
                goal_name=goal_name,
                prove_fn=prove_fn,
                timeout_s=GOAL_GATE_TIMEOUT_S,
                profiles=PROVE_PROFILES,
                enabled=True,
            )
            log_exp(
                "scheme_goal_gate",
                goal=goal_name,
                status=attempt.goal_gate_status,
                elapsed=attempt.goal_gate_elapsed,
                axis=tag,
                measure=attempt.measure_fun or "",
            )
            if attempt.gate_blocks_scheme():
                log_exp(
                    "scheme_goal_gate_block",
                    goal=goal_name,
                    gate=attempt.goal_gate_status,
                    axis=tag,
                )
                continue
        else:
            attempt.goal_gate_status = "skipped" if soft_gate else "off"
            if soft_gate:
                log_exp(
                    "scheme_goal_gate",
                    goal=goal_name,
                    status="skipped",
                    elapsed=0.0,
                    axis=tag,
                    measure=attempt.measure_fun or "",
                    bridge_primary=1,
                )

        prove_obligations(
            attempt,
            smt_content=smt_content,
            work_dir=sub,
            goal_name=goal_name,
            prove_fn=prove_fn,
            timeout_s=PROVE_TIMEOUT_S,
            profiles=PROVE_PROFILES,
        )
        viable.append(attempt)
        log_exp(
            "scheme_prove_axis",
            goal=goal_name,
            axis=tag,
            measure=attempt.measure_fun or "",
            n=len(attempt.obligations),
            n_proved=sum(1 for o in attempt.obligations if o.status == "proved"),
            goal_gate=attempt.goal_gate_status,
            bridge_primary=int(bool(getattr(attempt, "bridge_primary", False))),
        )

    if not viable:
        attempt = candidates[-1]
        return SchemeRoundResult(
            attempt=attempt,
            close_parent=False,
            nest_children=[],
        )

    def _can_close(att: SchemeAttempt) -> bool:
        if getattr(att, "bridge_primary", False):
            return False
        return (
            att.validated
            and att.all_proved()
            and att.goal_gate_ok()
            and not att.gate_blocks_scheme()
            and not att.skipped
            and not att.validate_errors
        )

    # Prefer structural close when both axes fully succeed.
    for att in viable:
        if not att.measure_fun and _can_close(att):
            sides = [a for a in viable if a is not att]
            if sides:
                att = _merge_side_obligations_for_ledger(att, sides)
            return SchemeRoundResult(
                attempt=att, close_parent=True, side_attempts=sides,
            )
    for att in viable:
        if _can_close(att):
            sides = [a for a in viable if a is not att]
            if sides:
                att = _merge_side_obligations_for_ledger(att, sides)
            return SchemeRoundResult(
                attempt=att, close_parent=True, side_attempts=sides,
            )

    # Ledger primary: structural if present, else first viable (often measure).
    primary = next((a for a in viable if not a.measure_fun), None) or viable[0]
    sides = [a for a in viable if a is not primary]

    # Nest: union of unproved obligations across axes (dedupe by formula).
    # Shared depth with the lemma tree: this node always generate+proves;
    # further nested induction is allowed only while another depth slot remains
    # (child at depth+DEPTH_COST can still induct; the leaf cannot nest again).
    nest_children: List[SchemeObligation] = []
    seen_forms: Set[str] = set()
    can_nest = can_afford_nest(depth, max_depth, nest_budget)
    for att in viable:
        if att.gate_blocks_scheme():
            continue
        for obl in att.obligations:
            if obl.status in ("proved", "invalid"):
                continue
            key = normalize_lemma_formula(obl.formula or "")
            if key and key in seen_forms:
                continue
            if key:
                seen_forms.add(key)
            # Measure bridges (descent / R1 / R2) stay on this node: short-prove
            # or frontier. Nest depth is reserved for structural base/step
            # (xs → ys → zs).
            if obl.kind == "measure":
                mark_frontier(att, [obl.obl_id])
                continue
            if can_nest:
                obl.skip_initial = True
                nest_children.append(obl)
            else:
                mark_frontier(att, [obl.obl_id])

    if not can_nest and not nest_children:
        # Frontiers already marked per-axis above when !can_nest.
        pass

    log_exp(
        "scheme_prove",
        goal=goal_name,
        var=primary.induct_var,
        sort=primary.induct_sort,
        n=len(primary.obligations),
        n_proved=sum(1 for o in primary.obligations if o.status == "proved"),
        validated=primary.validated,
        goal_gate=primary.goal_gate_status,
        goal_gate_elapsed=primary.goal_gate_elapsed,
        measure=primary.measure_fun or "",
        bridge_primary=int(bool(getattr(primary, "bridge_primary", False))),
        n_axes=len(viable),
        n_nest=len(nest_children),
    )

    # Fold companion-axis obligations into the ledger attempt so harvest/prompt
    # see measure bridges even when structural is the primary.
    if sides:
        primary = _merge_side_obligations_for_ledger(primary, sides)

    return SchemeRoundResult(
        attempt=primary,
        close_parent=False,
        nest_children=nest_children,
        side_attempts=sides,
    )


def _merge_side_obligations_for_ledger(
    primary: SchemeAttempt,
    sides: Sequence[SchemeAttempt],
) -> SchemeAttempt:
    """Append side-axis obligations with prefixed ids (display/harvest only)."""
    from smt_patterns import normalize_lemma_formula

    seen = {normalize_lemma_formula(o.formula or "") for o in primary.obligations}
    seen.discard("")
    for side in sides:
        tag = "meas" if side.measure_fun else "struct"
        for obl in side.obligations:
            key = normalize_lemma_formula(obl.formula or "")
            if key and key in seen:
                continue
            if key:
                seen.add(key)
            primary.obligations.append(
                SchemeObligation(
                    obl_id=f"{tag}_{obl.obl_id}",
                    kind=obl.kind,
                    ctor=obl.ctor,
                    formula=obl.formula,
                    induct_var=obl.induct_var,
                    induct_sort=obl.induct_sort,
                    inst_term=obl.inst_term,
                    validated=obl.validated,
                    status=obl.status,
                    prove_status=obl.prove_status,
                    prove_elapsed=obl.prove_elapsed,
                )
            )
        if side.measure_fun and not primary.measure_fun:
            primary.measure_fun = side.measure_fun
            primary.measure_ret_sort = side.measure_ret_sort
            primary.measure_prelude = side.measure_prelude or primary.measure_prelude
            primary.bridge_primary = bool(
                primary.bridge_primary or side.bridge_primary
            )
    return primary


def start_scheme_session(
    *,
    smt_content: str,
    goal_name: str,
    work_dir: Path,
    mode: str = "structural",
    depth: int = 0,
    nest_budget: int = NEST,
    max_depth: int = 3,
    current_goal: Optional[str] = None,
    prove_fn: Optional[ProveFn] = None,
) -> SchemeSession:
    session = SchemeSession()

    def _run() -> SchemeRoundResult:
        return run_scheme_round(
            smt_content=smt_content,
            goal_name=goal_name,
            work_dir=work_dir,
            mode=mode,
            depth=depth,
            nest_budget=nest_budget,
            max_depth=max_depth,
            current_goal=current_goal,
            prove_fn=prove_fn,
            do_prove=True,
        )

    session.start(_run)
    return session


def finalize_after_attempt(
    round_result: Optional[SchemeRoundResult],
    *,
    failed_data: dict,
    usefulness_succeeded: bool,
) -> dict:
    """Persist ledger after the LLM/usefulness attempt finishes.

    Parent ``kind=scheme`` close is deferred: set ``scheme_pending_close`` when
    all obligations proved, so the caller can close only after this attempt
    (library may have grown from LLM lemmas). Usefulness success wins.
    """
    if round_result is None:
        return failed_data
    attempt = round_result.attempt
    failed_data = save_scheme_attempt(failed_data, attempt)
    failed_data.pop(SCHEME_PENDING_KEY, None)
    if usefulness_succeeded:
        return failed_data
    # Hard gate: never pending-close on unvalidated / incomplete / gate-blocked schemes.
    if (
        round_result.close_parent
        and attempt.validated
        and attempt.all_proved()
        and attempt.goal_gate_ok()
        and not attempt.gate_blocks_scheme()
        and not attempt.skipped
        and not attempt.validate_errors
    ):
        failed_data[SCHEME_PENDING_KEY] = {
            "reason": "short_prove",
            "goal": attempt.goal_name,
            "goal_gate": attempt.goal_gate_status,
        }
        attempt.closed = True
        attempt.close_reason = "short_prove"
        failed_data = save_scheme_attempt(failed_data, attempt)
    elif round_result.nest_children and not attempt.gate_blocks_scheme():
        # Keep nest enabled for the child; further hops are gated by shared
        # depth (xs → ys → zs), not by zeroing the budget after one hop.
        failed_data[SCHEME_DISPATCH_KEY] = {
            "action": "nest",
            "children": [o.to_dict() for o in round_result.nest_children],
            "nest_budget": attempt.nest_budget,
            "depth_cost": DEPTH_COST,
        }
    return failed_data


def consume_pending_scheme_close(failed_data: dict) -> Optional[str]:
    pending = failed_data.pop(SCHEME_PENDING_KEY, None)
    if isinstance(pending, dict) and pending.get("reason"):
        return str(pending.get("reason"))
    return None


def pop_scheme_dispatch(failed_data: dict) -> dict:
    payload = failed_data.pop(SCHEME_DISPATCH_KEY, None) or {}
    return payload if isinstance(payload, dict) else {}


def run_nest_children(
    *,
    parent_smt_content: str,
    parent_goal: str,
    work_dir: Path,
    children: Sequence[SchemeObligation],
    depth: int,
    nest_budget: int,
    max_depth: int,
    mode: str,
    child_prove_fn: ChildProveFn,
    write_child_smt: Callable[[str, str, Path], None],
) -> bool:
    """Prove nested scheme obligations as scheme-only children. No LLM."""
    if not children:
        return True
    all_ok = True
    for obl in children:
        child_name = f"{parent_goal}__sch_{obl.obl_id}"
        child_path = Path(work_dir) / f"{child_name}.smt2"
        write_child_smt(parent_smt_content, obl.formula, child_path)
        obl.node_id = child_name
        ok = child_prove_fn(
            child_name,
            depth=depth + DEPTH_COST,
            nest_budget=nest_budget,
            skip_initial=obl.skip_initial,
            scheme_only=True,
            mode=mode,
        )
        if ok:
            obl.status = "proved"
        else:
            obl.status = "failed"
            obl.no_nest = True
            all_ok = False
    return all_ok


def frontier_backup_prove(
    attempt: SchemeAttempt,
    *,
    smt_content: str,
    work_dir: Path,
    goal_name: str,
    had_success_child: bool,
    prove_fn: Optional[ProveFn] = None,
) -> bool:
    """Node-end: if ≥1 success child, short-reprove open frontier once.

    No nest, no LLM. Returns True when all frontier obligations are proved
    (caller should close parent along the scheme chain).
    """
    attempt.had_success_child = bool(had_success_child)
    if not had_success_child:
        return False
    frontier = attempt.open_frontier()
    if not frontier:
        # Also allow re-proving any still-failed obligations marked no_nest.
        frontier = [
            o for o in attempt.obligations
            if o.status not in ("proved", "invalid") and o.no_nest
        ]
    if not frontier:
        return attempt.all_proved()

    attempt.backup_ran = True
    ids = [o.obl_id for o in frontier]
    for o in frontier:
        if o.status not in ("proved", "invalid"):
            o.status = "open"
    prove_obligations(
        attempt,
        smt_content=smt_content,
        work_dir=Path(work_dir),
        goal_name=goal_name,
        prove_fn=prove_fn,
        only=ids,
    )
    if all(o.status == "proved" for o in attempt.obligations if o.obl_id in ids):
        for o in attempt.obligations:
            if o.obl_id in ids:
                o.status = "proved"
        if attempt.validated and attempt.all_proved() and not attempt.validate_errors:
            try:
                from exp_flags import induction_scheme_goal_gate_enabled
                if induction_scheme_goal_gate_enabled() and not attempt.goal_gate_ok():
                    prove_goal_gate(
                        attempt,
                        smt_content=smt_content,
                        work_dir=Path(work_dir),
                        goal_name=goal_name,
                        prove_fn=prove_fn,
                        enabled=True,
                    )
            except Exception as exc:
                logging.warning("scheme frontier goal-gate failed: %s", exc)
                attempt.goal_gate_status = "error"
            if not attempt.goal_gate_ok():
                return False
            attempt.closed = True
            attempt.close_reason = "frontier"
            return True
    return False


def can_afford_nest(depth: int, max_depth: int, nest_budget: int) -> bool:
    """Whether this node may spawn scheme-only children for unproved obligations.

    Hard limit: shared ``max_depth`` with the lemma obligation tree. The child
    runs at ``depth + DEPTH_COST`` and may still generate base/step + short-prove;
    nesting from that child is refused only when no deeper slot remains.

    ``nest_budget <= 0`` explicitly disables nesting (tests / callers that want
    frontier-only). A positive budget is a soft enable, not a one-hop fuse.
    """
    if nest_budget <= 0:
        return False
    return depth + DEPTH_COST < max_depth
