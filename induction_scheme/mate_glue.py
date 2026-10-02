"""Shared Mate_new / Mate_new_vampire hooks for InductionScheme."""

from __future__ import annotations

import logging
from pathlib import Path
from typing import Any, Callable, Optional, Sequence

from exp_flags import (
    induction_scheme_enabled,
    induction_scheme_mode,
    should_run_induction_scheme,
)
from lemma_harvest import write_negated_lemma_smt

from .constants import NEST
from .dispatch import (
    SchemeSession,
    consume_pending_scheme_close,
    finalize_after_attempt,
    frontier_backup_prove,
    pop_scheme_dispatch,
    run_nest_children,
    run_scheme_round,
    start_scheme_session,
)
from .ledger import (
    format_scheme_prompt_block,
    harvest_scheme_proved_to_library,
    harvest_scheme_refuted_to_invalid,
    latest_scheme_attempt,
    save_scheme_attempt,
)
from .types import SchemeRoundResult

ProveFn = Callable[[Path, int, Sequence[str]], object]


def scheme_prove_kwargs_for_backend(backend: str) -> dict:
    """Prove fn + profiles for scheme short-prove / gate / frontier.

    Backend must match usefulness (cvc5 Mate → CVC portfolio; Vampire Mate →
    serial tip→portfolio[+Int reserve] when ``VAMPIRE_SERIAL_DUAL=on``, else
    single ``induction_portfolio``). Scheme Vampire wall adds
    ``VAMPIRE_SERIAL_SCHEME_EXTRA_S`` (default +5).
    """
    name = (backend or "cvc5").strip().lower()
    if name in ("vampire", "vamp"):
        from .constants import VAMPIRE_PROVE_PROFILES
        from .prove import default_vampire_prove

        return {
            "prove_fn": default_vampire_prove,
            "profiles": list(VAMPIRE_PROVE_PROFILES),
        }
    from .constants import PROVE_PROFILES
    from .prove import default_cvc_prove

    return {
        "prove_fn": default_cvc_prove,
        "profiles": list(PROVE_PROFILES),
    }


def maybe_start_scheme_session(
    *,
    failed_data: dict,
    smt_content: str,
    goal_name: str,
    work_dir: Path,
    depth: int,
    max_depth: int,
    current_goal: Optional[str] = None,
    nest_budget: int = NEST,
    scheme_only: bool = False,
    prove_fn: Optional[ProveFn] = None,
    profiles: Optional[Sequence[str]] = None,
) -> Optional[SchemeSession]:
    if not should_run_induction_scheme(failed_data, scheme_only=scheme_only):
        return None
    # Depth already at limit: still allow generate+prove, but nest will be denied.
    return start_scheme_session(
        smt_content=smt_content,
        goal_name=goal_name,
        work_dir=work_dir,
        mode=induction_scheme_mode(),
        depth=depth,
        nest_budget=nest_budget,
        max_depth=max_depth,
        current_goal=current_goal,
        prove_fn=prove_fn,
        profiles=profiles,
    )


def barrier_and_finalize(
    session: Optional[SchemeSession],
    *,
    load_failed,
    save_failed,
    usefulness_succeeded: bool,
    base_path: Optional[str] = None,
    depth: int = 0,
) -> Optional[SchemeRoundResult]:
    """Wait for scheme short-prove, persist ledger, harvest proved bridges."""
    if session is None:
        return None
    rr = session.wait()
    data = load_failed()
    data = finalize_after_attempt(
        rr, failed_data=data, usefulness_succeeded=usefulness_succeeded,
    )
    if rr is not None and base_path:
        harvest_scheme_proved_to_library(
            rr.attempt, base_path, depth=depth,
        )
        harvest_scheme_refuted_to_invalid(
            rr.attempt, base_path, goal_name=rr.attempt.goal_name,
        )
    save_failed(data)
    return rr


def scheme_prompt_suffix(
    failed_data: dict,
    *,
    goal_name: Optional[str] = None,
) -> str:
    if not induction_scheme_enabled():
        return ""
    try:
        from exp_flags import induction_scheme_prompt_enabled
        if not induction_scheme_prompt_enabled():
            return ""
    except Exception:
        pass
    return format_scheme_prompt_block(failed_data, goal_name=goal_name)


def library_for_prompt(
    library: Sequence[Any],
    failed_data: Optional[dict],
    *,
    goal_name: Optional[str] = None,
) -> List[Any]:
    """Library rows for the LLM prompt (hide current-node scheme duplicates)."""
    if not induction_scheme_enabled():
        return list(library or [])
    try:
        from exp_flags import induction_scheme_prompt_enabled
        if not induction_scheme_prompt_enabled():
            return list(library or [])
    except Exception:
        pass
    from .ledger import filter_library_excluding_current_scheme

    return filter_library_excluding_current_scheme(
        library, failed_data, goal_name=goal_name,
    )


def try_scheme_close_after_attempt(
    *,
    load_failed,
    save_failed,
    set_outcome,
    goal_name: str,
) -> bool:
    """If pending scheme close was set after this attempt, close the node."""
    data = load_failed()
    reason = consume_pending_scheme_close(data)
    if not reason:
        return False
    save_failed(data)
    set_outcome(kind="scheme", reason=reason, source="induction_scheme")
    logging.info("InductionScheme closed %s (%s) after attempt", goal_name, reason)
    return True


def try_scheme_nest_after_attempt(
    *,
    load_failed,
    save_failed,
    parent_smt_content: str,
    parent_goal: str,
    work_dir: Path,
    depth: int,
    max_depth: int,
    child_prove_fn: Callable[..., bool],
    set_outcome,
    prove_fn: Optional[ProveFn] = None,
    profiles: Optional[Sequence[str]] = None,
) -> bool:
    """Run NEST scheme-only children if dispatch says so. Close parent on full success."""
    data = load_failed()
    dispatch = pop_scheme_dispatch(data)
    save_failed(data)
    if not dispatch or dispatch.get("action") != "nest":
        return False
    children_raw = dispatch.get("children") or []
    from .types import SchemeObligation

    children = [
        SchemeObligation.from_dict(c) if isinstance(c, dict) else c
        for c in children_raw
    ]
    nest_budget = int(dispatch.get("nest_budget") or 0)
    ok = run_nest_children(
        parent_smt_content=parent_smt_content,
        parent_goal=parent_goal,
        work_dir=work_dir,
        children=children,
        depth=depth,
        nest_budget=nest_budget,
        max_depth=max_depth,
        mode=induction_scheme_mode(),
        child_prove_fn=child_prove_fn,
        write_child_smt=lambda smt, formula, dest: write_negated_lemma_smt(
            smt, formula, dest
        ),
    )
    # Update ledger statuses.
    data = load_failed()
    att = latest_scheme_attempt(data, goal_name=parent_goal)
    if att is not None:
        by_id = {o.obl_id: o for o in att.obligations}
        for ch in children:
            if ch.obl_id in by_id:
                by_id[ch.obl_id].status = ch.status
                by_id[ch.obl_id].node_id = ch.node_id
                by_id[ch.obl_id].no_nest = ch.no_nest
        if ok and all(o.status == "proved" for o in att.obligations):
            if not (att.validated and not att.validate_errors and not att.skipped):
                data = save_scheme_attempt(data, att)
                save_failed(data)
                return False
            # Re-check axioms∧base∧step ⊢ G (library may have grown during nest).
            try:
                from exp_flags import induction_scheme_goal_gate_enabled
                from .prove import prove_goal_gate

                if induction_scheme_goal_gate_enabled():
                    prove_goal_gate(
                        att,
                        smt_content=parent_smt_content,
                        work_dir=work_dir,
                        goal_name=parent_goal,
                        prove_fn=prove_fn,
                        profiles=profiles,
                        enabled=True,
                    )
            except Exception as exc:
                logging.warning("scheme nest goal-gate failed: %s", exc)
                att.goal_gate_status = "error"
            if not att.goal_gate_ok():
                data = save_scheme_attempt(data, att)
                save_failed(data)
                logging.info(
                    "InductionScheme nest proved obligations but goal-gate=%s; not closing %s",
                    att.goal_gate_status, parent_goal,
                )
                return False
            att.closed = True
            att.close_reason = "nest"
            data = save_scheme_attempt(data, att)
            save_failed(data)
            set_outcome(kind="scheme", reason="nest", source="induction_scheme")
            logging.info("InductionScheme nest closed parent %s", parent_goal)
            return True
        if not ok:
            from .prove import mark_frontier
            mark_frontier(att, [c.obl_id for c in children if c.status != "proved"])
        data = save_scheme_attempt(data, att)
        save_failed(data)
    return False


def try_frontier_backup_at_node_end(
    *,
    load_failed,
    save_failed,
    smt_content: str,
    goal_name: str,
    work_dir: Path,
    had_success_child: bool,
    set_outcome,
    prove_fn: Optional[ProveFn] = None,
    profiles: Optional[Sequence[str]] = None,
    base_path: Optional[str] = None,
    depth: int = 0,
) -> bool:
    if not induction_scheme_enabled():
        return False
    data = load_failed()
    att = latest_scheme_attempt(data, goal_name=goal_name)
    if att is None or att.closed:
        return False
    closed = frontier_backup_prove(
        att,
        smt_content=smt_content,
        work_dir=work_dir,
        goal_name=goal_name,
        had_success_child=had_success_child,
        prove_fn=prove_fn,
        profiles=profiles,
    )
    bp = base_path or str(work_dir)
    harvest_scheme_proved_to_library(att, bp, depth=depth)
    harvest_scheme_refuted_to_invalid(att, bp, goal_name=goal_name)
    data = save_scheme_attempt(data, att)
    save_failed(data)
    if closed:
        set_outcome(kind="scheme", reason="frontier", source="induction_scheme")
        logging.info("InductionScheme frontier backup closed %s", goal_name)
        return True
    return False


def run_scheme_only_node(
    *,
    smt_content: str,
    goal_name: str,
    work_dir: Path,
    depth: int,
    max_depth: int,
    nest_budget: int,
    skip_initial: bool,
    current_goal: Optional[str],
    load_failed,
    save_failed,
    set_outcome,
    child_prove_fn: Callable[..., bool],
    prove_fn: Optional[ProveFn] = None,
    profiles: Optional[Sequence[str]] = None,
) -> bool:
    """Scheme-only child: generate+prove, optional further nest, no LLM.

    If the goal-gate fails, leave the node **open** and return False (no nest).
    """
    rr = run_scheme_round(
        smt_content=smt_content,
        goal_name=goal_name,
        work_dir=work_dir,
        mode=induction_scheme_mode(),
        depth=depth,
        nest_budget=nest_budget,
        max_depth=max_depth,
        current_goal=current_goal,
        prove_fn=prove_fn,
        profiles=profiles,
        do_prove=True,
    )
    data = load_failed()
    data = finalize_after_attempt(
        rr, failed_data=data, usefulness_succeeded=False,
    )
    harvest_scheme_proved_to_library(
        rr.attempt, str(work_dir), depth=depth,
    )
    harvest_scheme_refuted_to_invalid(
        rr.attempt, str(work_dir), goal_name=goal_name,
    )
    save_failed(data)

    if rr.attempt.gate_blocks_scheme():
        set_outcome(
            kind="open",
            reason=f"scheme_goal_gate_{rr.attempt.goal_gate_status}",
            source="induction_scheme",
        )
        logging.info(
            "scheme-only %s left open (goal-gate=%s)",
            goal_name, rr.attempt.goal_gate_status,
        )
        return False

    if consume_pending_scheme_close(data):
        save_failed(data)
        set_outcome(kind="scheme", reason="short_prove", source="induction_scheme")
        return True

    if try_scheme_nest_after_attempt(
        load_failed=load_failed,
        save_failed=save_failed,
        parent_smt_content=smt_content,
        parent_goal=goal_name,
        work_dir=work_dir,
        depth=depth,
        max_depth=max_depth,
        child_prove_fn=child_prove_fn,
        set_outcome=set_outcome,
        prove_fn=prove_fn,
        profiles=profiles,
    ):
        return True

    # Leaf failure: mark frontier, no LLM.
    return False
