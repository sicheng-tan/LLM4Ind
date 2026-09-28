"""Gate: select profile facts safe to inject into lemma-generation prompts."""

from __future__ import annotations

from typing import Optional, Set

from .types import GatedProfileFacts, ProblemProfile


def gate_profile_for_prompt(
    profile: ProblemProfile,
    *,
    current_goal: Optional[str] = None,
) -> GatedProfileFacts:
    """Conservative injection rules (v1).

    - Structural recursion only if the recursive function appears in the goal.
    - Observer only if it has defining equations (structural) and appears in goal.
    - Signature-only / heuristic observers are never injected.
    - Relations only when evidence_level is structural/explicit.
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
            # bare recursive_call: only inject if also in a relation with observer
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

    for rel in profile.goal_relations:
        if rel.evidence_level not in ("explicit", "structural"):
            continue
        if not set(rel.symbols) & goal_syms:
            continue
        gated.relations.append(rel)
        gated.related_formula_ids.extend(rel.formula_ids)

    known_induction = any(
        (a.base_ctors or a.step_ctors)
        and a.evidence_level in ("explicit", "structural")
        for a in profile.induction_attempts
    )
    for att in profile.induction_attempts:
        if att.base_ctors or att.step_ctors:
            if att.evidence_level not in ("explicit", "structural"):
                continue
            gated.induction_attempts.append(att)
            gated.related_formula_ids.extend(att.source_formula_ids)
        elif (
            known_induction
            and att.status == "candidate"
            and att.evidence_level in ("heuristic", "structural")
        ):
            # Nested placeholder so multi-var goals can show outer→inner list.
            gated.induction_attempts.append(att)

    for link in profile.function_links:
        # Inject theorem_related always; missing_bridge only when goal has ≥2
        # interesting symbols (already ensured by analyzer).
        if link.kind == "theorem_related":
            if link.evidence_level not in ("explicit", "structural"):
                continue
            gated.function_links.append(link)
        elif link.kind == "missing_bridge":
            # Heuristic gap signal — keep, but only pairs fully in goal_syms.
            if not set(link.symbols) <= goal_syms:
                continue
            gated.function_links.append(link)

    # Keep formula ids for debugging / metrics; do not render SMT bodies
    # (they already appear in the lemma-generation user prompt).
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
