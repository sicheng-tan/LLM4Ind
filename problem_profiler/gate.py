"""Gate: select profile facts safe to inject into lemma-generation prompts."""

from __future__ import annotations

from typing import Optional, Set

from .types import GatedProfileFacts, ProblemProfile


def gate_profile_for_prompt(
    profile: ProblemProfile,
    *,
    current_goal: Optional[str] = None,
) -> GatedProfileFacts:
    """Conservative injection rules.

    - Structural recursion only if the recursive function appears in the goal.
    - Observer only if it has defining equations (structural) and appears in goal.
    - Signature-only / heuristic observers are never injected.
    - Goal relations and function links are not injected (v2; reduce noise).
    - Induction: known base/step and neutral ``attempt=none`` candidates.
    """
    goal_syms = _symbols_from_goal(profile, current_goal)
    gated = GatedProfileFacts()
    if not goal_syms:
        return gated

    for fact in profile.recursion_structure:
        if fact.kind not in (
            "structural_recursion",
            "constructor_case_split",
            "other_decreasing_recursion",
            "mutual_recursion",
        ):
            continue
        if fact.evidence_level not in ("explicit", "structural"):
            if fact.kind != "other_decreasing_recursion":
                continue
        funs = fact.function.split("/")
        if not any(f in goal_syms for f in funs):
            continue
        gated.recursion.append(fact)
        gated.related_formula_ids.extend(fact.source_formula_ids)

    for obs in profile.observer_candidates:
        if obs.evidence_level not in ("explicit", "structural"):
            continue
        if not obs.source_formula_ids:
            continue
        if obs.function not in goal_syms:
            continue
        gated.observers.append(obs)
        gated.related_formula_ids.extend(obs.source_formula_ids)

    # relations / function_links intentionally omitted from injection.

    for att in profile.induction_attempts:
        # Drop binders that are not part of the current goal (profile may
        # have been built from a different / outer SMT goal).
        if att.induct_var and att.induct_var not in goal_syms:
            continue
        if att.base_ctors or att.step_ctors:
            if att.evidence_level not in ("explicit", "structural"):
                continue
            gated.induction_attempts.append(att)
            gated.related_formula_ids.extend(att.source_formula_ids)
        elif att.status == "candidate" and att.evidence_level in (
            "heuristic",
            "structural",
        ):
            gated.induction_attempts.append(att)

    gated.related_formula_ids = sorted({fid for fid in gated.related_formula_ids if fid})
    gated.formula_snippets = []
    return gated


def _symbols_from_goal(profile: ProblemProfile, current_goal: Optional[str]) -> Set[str]:
    from .parse_smt import collect_symbols

    if current_goal:
        return set(collect_symbols(current_goal))
    for rec in profile.formulas:
        if rec.formula_id == profile.goal_formula_id or rec.role == "goal":
            return set(rec.symbols)
    return set()
