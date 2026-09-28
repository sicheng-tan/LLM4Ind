"""Conservative function co-occurrence links vs the current goal."""

from __future__ import annotations

from typing import List, Set, Tuple

from .types import FunctionLinkFact, ProblemProfile


def analyze_function_links(profile: ProblemProfile) -> List[FunctionLinkFact]:
    """Annotate recursion facts with link=… and return related / missing_bridge rows.

    - Recursion ``link`` / ``link_peers``: co-occurrence with other recursive /
      structural-observer symbols in non-goal axioms (peers need not be in the
      goal — e.g. ``rev`` linked via ``append`` in its defining equation).
    - ``Function links`` rows: only pairs where **both** symbols appear in the
      CURRENT goal (related vs missing_bridge).
    """
    goal_syms = _goal_symbols(profile)
    interesting = _interesting_symbols(profile)
    goal_interesting = interesting & goal_syms

    for fact in profile.recursion_structure:
        fact.link = ""
        fact.link_peers = []

    # Broad co-occurrence over all interesting symbols (for recursion annotations).
    cooccur_all = _cooccurrence_pairs(profile, interesting)
    for fact in profile.recursion_structure:
        heads = [p for p in fact.function.split("/") if p]
        if not any(h in goal_syms for h in heads):
            continue
        peers: Set[str] = set()
        for h in heads:
            if h not in interesting:
                continue
            for a, b in cooccur_all:
                if a == h:
                    peers.add(b)
                elif b == h:
                    peers.add(a)
        peers -= set(heads)
        if peers:
            fact.link = "theorem-related"
            fact.link_peers = sorted(peers)
        elif any(h in interesting for h in heads):
            fact.link = "def-only"

    links: List[FunctionLinkFact] = []
    if len(goal_interesting) < 2:
        return links

    cooccur_goal = _cooccurrence_pairs(profile, goal_interesting)
    for a, b in sorted(cooccur_goal)[:8]:
        links.append(FunctionLinkFact(
            kind="theorem_related",
            symbols=[a, b],
            evidence_level="structural",
            detail="co-occur in non-goal axioms",
        ))

    related_set = set(cooccur_goal)
    ordered = sorted(goal_interesting)
    missing: List[Tuple[str, str]] = []
    for i, a in enumerate(ordered):
        for b in ordered[i + 1 :]:
            if (a, b) not in related_set:
                missing.append((a, b))
    for a, b in missing[:6]:
        links.append(FunctionLinkFact(
            kind="missing_bridge",
            symbols=[a, b],
            evidence_level="heuristic",
            detail="both in CURRENT goal; no shared non-goal axiom",
        ))
    return links


def _goal_symbols(profile: ProblemProfile) -> Set[str]:
    gid = profile.goal_formula_id
    for rec in profile.formulas:
        if rec.formula_id == gid or rec.role == "goal":
            return set(rec.symbols)
    return set()


def _interesting_symbols(profile: ProblemProfile) -> Set[str]:
    out: Set[str] = set()
    for r in profile.recursion_structure:
        if r.kind in (
            "structural_recursion",
            "recursive_call",
            "other_decreasing_recursion",
            "mutual_recursion",
            "constructor_case_split",
        ):
            for part in r.function.split("/"):
                if part:
                    out.add(part)
    for o in profile.observer_candidates:
        if o.evidence_level in ("explicit", "structural") and o.source_formula_ids:
            out.add(o.function)
    return out


def _cooccurrence_pairs(
    profile: ProblemProfile, interesting: Set[str],
) -> Set[Tuple[str, str]]:
    pairs: Set[Tuple[str, str]] = set()
    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        hit = sorted(set(rec.symbols) & interesting)
        for i, a in enumerate(hit):
            for b in hit[i + 1 :]:
                pairs.add((a, b))
    return pairs
