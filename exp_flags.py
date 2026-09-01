"""Ablation switches for features added on top of the original PaperMate loop.

Defaults are on so the current full method is unchanged. Set any value in
``off`` / ``0`` / ``false`` / ``no`` to disable that piece.

These flags are independent of ``SOLVER_ROUTING``, ``LEMMA_LIBRARY``, and
``OBLIGATION_TREE``.
"""

from __future__ import annotations

import os
from typing import Any, Dict, Sequence

_OFF_VALUES = frozenset({"0", "off", "false", "no"})

OURS_PROMPT_STRATEGIES = (
    "prove_prompt_equational_reasoning",
    "prove_prompt_term_rewrite",
)
NAIVE_PROMPT_STRATEGIES = ("prompt_naive",)


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


def normalize_strategy_mode(strategy_mode: str) -> str:
    mode = (strategy_mode or "default").strip().lower().replace("-", "_")
    if mode in ("naive",):
        return "naive"
    if mode in ("zero_shot", "zeroshot"):
        return "zero_shot"
    if mode in ("default", "ours", ""):
        return "default"
    return "default"


def resolve_prompt_pack(
    strategy_mode: str,
    max_attempts_per_prompt: int,
) -> Dict[str, Any]:
    """Prompt folder, templates, and attempt budget for ``--strategy-mode``.

    ``MAX_ATTEMPTS_PER_PROMPT`` is N (default 3). Paper / ours uses N attempts
    on each of two templates (2N total). Naive uses the single ``prompt_naive``
    template 2N times so the LLM-call budget matches. ``zero_shot`` currently
    uses the same ours pack as ``default`` (no separate prompt folder).
    """
    n = max(1, int(max_attempts_per_prompt) or 1)
    mode = normalize_strategy_mode(strategy_mode)
    if mode == "naive":
        strategies = list(NAIVE_PROMPT_STRATEGIES)
        return {
            "mode": mode,
            "folder_path": "./prompts_naive",
            "strategies": strategies,
            "max_attempts_per_prompt": n,
            "total_attempts": n * 2,
        }
    strategies = list(OURS_PROMPT_STRATEGIES)
    return {
        "mode": mode,
        "folder_path": "./prompts_ours",
        "strategies": strategies,
        "max_attempts_per_prompt": n,
        "total_attempts": n * len(strategies),
    }


def prompt_retarget_active(n_strategies: int) -> bool:
    """Retarget needs at least two templates; naive therefore stays on paper order."""
    return prompt_retarget_enabled() and int(n_strategies) > 1


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
