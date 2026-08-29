"""Ablation switches for features added on top of the original PaperMate loop.

Defaults are on so the current full method is unchanged. Set any value in
``off`` / ``0`` / ``false`` / ``no`` to disable that piece.

These flags are independent of ``SOLVER_ROUTING``, ``LEMMA_LIBRARY``, and
``OBLIGATION_TREE``. PaperMate (P0) is:

    SOLVER_ROUTING=off LEMMA_LIBRARY=off OBLIGATION_TREE=off
    FEEDBACK_REPAIR_HINTS=off FEEDBACK_PROGRESS=off
    PROMPT_RETARGET=off UNPROVED_NOT_INVALID=off
"""

from __future__ import annotations

import os
from typing import Sequence

_OFF_VALUES = frozenset({"0", "off", "false", "no"})


def _flag_enabled(name: str, default: str = "on") -> bool:
    return os.getenv(name, default).strip().lower() not in _OFF_VALUES


def repair_hints_enabled() -> bool:
    """Write solver-derived repair hints into failed_lemmas / the LLM prompt."""
    return _flag_enabled("FEEDBACK_REPAIR_HINTS")


def progress_feedback_enabled() -> bool:
    """Run the 3s usefulness sidecar and inject progress lemmas into the prompt."""
    return _flag_enabled("FEEDBACK_PROGRESS")


def prompt_retarget_enabled() -> bool:
    """Pick / switch generation templates from hint families and consecutive no-help."""
    return _flag_enabled("PROMPT_RETARGET")


def unproved_not_invalid_enabled() -> bool:
    """Record a failed useful subgoal as useful_but_unproved instead of invalid."""
    return _flag_enabled("UNPROVED_NOT_INVALID")


def paper_schedule_prompt(
    strategies: Sequence[str],
    attempt: int,
    max_attempts_per_prompt: int,
) -> str:
    """Paper order: first template for N attempts, then the next, and so on."""
    pool = [s for s in strategies if s]
    if not pool:
        return ""
    per = max(1, int(max_attempts_per_prompt) or 1)
    idx = min(max(0, int(attempt)) // per, len(pool) - 1)
    return pool[idx]
