"""Public API for the deterministic Problem Profiler."""

from __future__ import annotations

from typing import Any, List, Optional, Sequence

from .analyze import enrich_profile
from .gate import gate_profile_for_prompt
from .incremental import (
    build_problem_profile_incremental,
    clear_profiler_caches,
    profiler_cache_stats,
)
from .parse_smt import parse_smt_profile
from .render import format_profile_prompt_block
from .types import GatedProfileFacts, ProblemProfile

__all__ = [
    "ProblemProfile",
    "GatedProfileFacts",
    "build_problem_profile",
    "build_problem_profile_incremental",
    "gate_profile_for_prompt",
    "format_profile_prompt_block",
    "profile_prompt_block_for_smt",
    "attempt_lemmas_from_failed_data",
    "clear_profiler_caches",
    "profiler_cache_stats",
]


def build_problem_profile(smt_text: str, *, problem_id: str = "") -> ProblemProfile:
    """Parse SMT-LIB2 and enrich with recursion / observer / relation facts."""
    profile = parse_smt_profile(smt_text, problem_id=problem_id)
    return enrich_profile(profile)


def profile_prompt_block_for_smt(
    smt_text: str,
    *,
    problem_id: str = "",
    current_goal: Optional[str] = None,
    library_items: Sequence[Any] = (),
    attempt_lemmas: Sequence[Any] = (),
    cache_ns: str = "",
) -> str:
    """Build + gate + render; empty string when nothing relevant to inject.

    Uses an incremental cache: background SMT (goal stripped) is parsed once per
    content hash; lemma-library formulas are appended incrementally when the
    library only grows. Goal-dependent facts refresh every call.

    ``attempt_lemmas`` (useless / unproved texts from the current node) are
    merged only into induction matching, not into recursion analysis.
    """
    profile = build_problem_profile_incremental(
        smt_text,
        problem_id=problem_id,
        current_goal=current_goal,
        library_items=library_items,
        attempt_lemmas=attempt_lemmas,
        cache_ns=cache_ns or problem_id,
    )
    gated = gate_profile_for_prompt(profile, current_goal=current_goal)
    return format_profile_prompt_block(gated)


def attempt_lemmas_from_failed_data(failed_data: Optional[dict] = None) -> List[str]:
    """Collect lemma texts from useless groups + unproved list for induction matching."""
    data = failed_data if isinstance(failed_data, dict) else {}
    out: List[str] = []
    seen: set = set()

    def _add(text: str) -> None:
        from smt_patterns import normalize_lemma_formula
        norm = normalize_lemma_formula(text or "")
        if norm and norm not in seen:
            seen.add(norm)
            out.append(norm)

    for group in data.get("useless_lemma_groups") or []:
        if not isinstance(group, dict):
            continue
        for lem in group.get("lemmas") or []:
            if isinstance(lem, str):
                _add(lem)
            elif isinstance(lem, dict):
                _add(str(lem.get("lemma") or lem.get("formula") or ""))
    for rec in data.get("unproved_lemmas") or []:
        if isinstance(rec, str):
            _add(rec)
        elif isinstance(rec, dict):
            _add(str(rec.get("lemma") or rec.get("formula") or ""))
    return out
