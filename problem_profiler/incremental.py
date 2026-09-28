"""Incremental caches for background SMT + lemma-library formula records."""

from __future__ import annotations

import copy
import hashlib
import re
from typing import Any, Dict, List, Optional, Sequence, Tuple

from smt_patterns import normalize_lemma_formula

from .analyze import enrich_profile, refresh_goal_dependent_facts
from .parse_smt import _PROOF_GOAL_BLOCK, collect_symbols, parse_smt_profile
from .types import FormulaRecord, ProblemProfile

# Background enriched profiles keyed by hash(background_smt).
_BG_CACHE: Dict[str, ProblemProfile] = {}
# Per-namespace library cache: fingerprint -> records (incremental append).
_LIB_CACHE: Dict[str, Tuple[List[str], List[FormulaRecord]]] = {}
_STATS = {"bg_hit": 0, "bg_miss": 0, "lib_hit": 0, "lib_miss": 0, "lib_incr": 0}


def clear_profiler_caches() -> None:
    _BG_CACHE.clear()
    _LIB_CACHE.clear()
    for k in _STATS:
        _STATS[k] = 0


def profiler_cache_stats() -> Dict[str, int]:
    return dict(_STATS)


def _hash_text(text: str) -> str:
    return hashlib.sha256((text or "").encode("utf-8")).hexdigest()[:20]


def background_smt_text(smt_text: str) -> str:
    """Drop proof-goal body so sibling nodes share one background cache key."""

    def _repl(_m: re.Match) -> str:
        return "; proof goal\n; proof goal end"

    return _PROOF_GOAL_BLOCK.sub(_repl, smt_text or "")


def _library_formula_strings(items: Sequence[Any]) -> List[str]:
    out: List[str] = []
    for item in items or ():
        if isinstance(item, dict):
            raw = item.get("formula") or ""
        else:
            raw = str(item or "")
        norm = normalize_lemma_formula(raw)
        if norm:
            out.append(norm)
    return out


def get_cached_background_profile(
    smt_text: str,
    *,
    problem_id: str = "",
) -> ProblemProfile:
    """Parse+enrich background (no goal); return a deep copy for merging."""
    bg_text = background_smt_text(smt_text)
    key = _hash_text(bg_text)
    hit = _BG_CACHE.get(key)
    if hit is not None:
        _STATS["bg_hit"] += 1
        return copy.deepcopy(hit)
    _STATS["bg_miss"] += 1
    profile = parse_smt_profile(bg_text, problem_id=problem_id)
    # Background should not invent a heuristic goal from axioms.
    if profile.goal_formula_id:
        for rec in profile.formulas:
            if rec.formula_id == profile.goal_formula_id or rec.role == "goal":
                rec.role = "axiom"
                rec.role_source = "assert"
        profile.goal_formula_id = None
    enrich_profile(profile)
    _BG_CACHE[key] = profile
    return copy.deepcopy(profile)


def get_library_formula_records(
    library_items: Sequence[Any],
    *,
    cache_ns: str = "",
) -> List[FormulaRecord]:
    """Parse library formulas; reuse prior records when the list only grows."""
    formulas = _library_formula_strings(library_items)
    ns = cache_ns or "_default"
    prev = _LIB_CACHE.get(ns)
    if prev is not None:
        prev_forms, prev_recs = prev
        if prev_forms == formulas:
            _STATS["lib_hit"] += 1
            return [copy.copy(r) for r in prev_recs]
        if (
            len(formulas) > len(prev_forms)
            and formulas[: len(prev_forms)] == prev_forms
        ):
            _STATS["lib_incr"] += 1
            new_recs = list(prev_recs)
            for i, form in enumerate(formulas[len(prev_forms) :], start=len(prev_forms)):
                new_recs.append(FormulaRecord(
                    formula_id=f"L{i}",
                    raw=form,
                    role="axiom",
                    role_source="lemma_library",
                    symbols=collect_symbols(form),
                ))
            _LIB_CACHE[ns] = (list(formulas), new_recs)
            return [copy.copy(r) for r in new_recs]
    _STATS["lib_miss"] += 1
    recs = [
        FormulaRecord(
            formula_id=f"L{i}",
            raw=form,
            role="axiom",
            role_source="lemma_library",
            symbols=collect_symbols(form),
        )
        for i, form in enumerate(formulas)
    ]
    _LIB_CACHE[ns] = (list(formulas), recs)
    return [copy.copy(r) for r in recs]


def extract_goal_formula(
    smt_text: str,
    current_goal: Optional[str] = None,
) -> Optional[str]:
    if current_goal and str(current_goal).strip():
        return normalize_lemma_formula(current_goal)
    full = parse_smt_profile(smt_text, problem_id="")
    if full.goal_formula_id:
        for rec in full.formulas:
            if rec.formula_id == full.goal_formula_id:
                return rec.raw
    return None


def build_problem_profile_incremental(
    smt_text: str,
    *,
    problem_id: str = "",
    current_goal: Optional[str] = None,
    library_items: Sequence[Any] = (),
    cache_ns: str = "",
) -> ProblemProfile:
    """Background cache ⊕ library records ⊕ current goal; refresh goal-dependent facts."""
    profile = get_cached_background_profile(smt_text, problem_id=problem_id)
    # Drop any residual goal rows from a stale cache shape.
    profile.formulas = [f for f in profile.formulas if f.role != "goal"]
    profile.goal_formula_id = None

    lib_recs = get_library_formula_records(library_items, cache_ns=cache_ns or problem_id)
    # Avoid duplicating formulas already present as background axioms.
    bg_raw = {f.raw for f in profile.formulas}
    for rec in lib_recs:
        if rec.raw not in bg_raw:
            profile.formulas.append(rec)

    goal = extract_goal_formula(smt_text, current_goal)
    if goal:
        profile.formulas.append(FormulaRecord(
            formula_id="G0",
            raw=goal,
            role="goal",
            role_source="current_goal" if current_goal else "smt_goal",
            symbols=collect_symbols(goal),
        ))
        profile.goal_formula_id = "G0"

    refresh_goal_dependent_facts(profile)
    return profile
