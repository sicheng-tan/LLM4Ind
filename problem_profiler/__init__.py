"""Public API for the deterministic Problem Profiler."""

from __future__ import annotations

from typing import Any, Optional, Sequence

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
    cache_ns: str = "",
) -> str:
    """Build + gate + render; empty string when nothing relevant to inject.

    Uses an incremental cache: background SMT (goal stripped) is parsed once per
    content hash; lemma-library formulas are appended incrementally when the
    library only grows. Goal-dependent facts refresh every call.
    """
    profile = build_problem_profile_incremental(
        smt_text,
        problem_id=problem_id,
        current_goal=current_goal,
        library_items=library_items,
        cache_ns=cache_ns or problem_id,
    )
    gated = gate_profile_for_prompt(profile, current_goal=current_goal)
    return format_profile_prompt_block(gated)
