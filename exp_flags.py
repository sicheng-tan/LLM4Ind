"""Ablation switches for features added on top of the original PaperMate loop.

Most flags default on. ``FEEDBACK_PROGRESS`` defaults off (no 3s sidecar).
``FEEDBACK_FORMULA_EVIDENCE`` defaults off (no ``-o lemmas`` samples).
Set a value in ``off`` / ``0`` / ``false`` / ``no`` to disable a piece.

These flags are independent of ``SOLVER_ROUTING``, ``LEMMA_LIBRARY``,
and ``LEMMA_LIBRARY_LOCAL``.

暂时弃用 (default **off**; set ``on`` to re-enable — do not turn this on
by accident):
- ``FEEDBACK_PROGRESS``: 3s usefulness sidecar, progress lemmas in the prompt,
  and sidecar-driven profile rerank (``no_progress`` / ``partial_progress``).
  Mix / HD hints still come from the failed 60s A∧C→P prove.
  Do not turn this on unless you are deliberately ablating the sidecar.

``PROMPT_ADVICE`` / ``OBLIGATION_TREE`` default on: LAST ATTEMPT advice
labels and the last well-formed split tree in the prompt / json. Independent
of ``--strategy-mode``.

``ANCESTOR_CYCLE_FILTER`` / ``ANCESTOR_PROMPT`` default on: path-local
ancestor α-cycle screening and PROOF PATH GOALS in the user prompt.
"""

from __future__ import annotations

import os
from typing import Any, Dict, Optional, Sequence

_OFF_VALUES = frozenset({"0", "off", "false", "no"})

OURS_PROMPT_STRATEGIES = (
    "prove_prompt_equational_reasoning",
    "prove_prompt_term_rewrite",
)
NAIVE_PROMPT_STRATEGIES = ("prompt_naive",)
# v2: one generic template (lemma_general). Structural repair is LAST ATTEMPT
# GENERALIZE hint directions, not a second system prompt. Budget stays 2N.
V2_PROMPT_STRATEGIES = ("lemma_general",)
V2_LEMMA_GENERAL = "lemma_general"


def _flag_enabled(name: str, default: str = "on") -> bool:
    return os.getenv(name, default).strip().lower() not in _OFF_VALUES


def repair_hints_enabled() -> bool:
    """Write solver-derived repair hints into failed_lemmas / the LLM prompt."""
    return _flag_enabled("FEEDBACK_REPAIR_HINTS")


def formula_evidence_enabled() -> bool:
    """Collect ``-o lemmas`` and show concrete solver formulas next to difficulty.

    Default **off**. Enable with ``FEEDBACK_FORMULA_EVIDENCE=on`` for the
    difficulty + instantiation-sample ablation. Does not emit new advice
    labels (TRIGGER/BRIDGE/GENERALIZE); samples stay evidence, not diagnoses.
    """
    return _flag_enabled("FEEDBACK_FORMULA_EVIDENCE", default="off")


def progress_feedback_enabled() -> bool:
    """Run the 3s usefulness sidecar and inject progress lemmas into the prompt.

    暂时弃用: default **off**. Do not enable casually — the sidecar is extra
    solver work and leftover ``progress_lemmas`` / ``no_progress`` hints can
    rerank profiles. Mix / HD still come from the failed 60s A∧C→P prove.
    ``FEEDBACK_PROGRESS=on`` restores the sidecar.
    """
    return _flag_enabled("FEEDBACK_PROGRESS", default="off")


def prompt_retarget_enabled() -> bool:
    """Pick / switch generation templates from hint families and consecutive no-help."""
    return _flag_enabled("PROMPT_RETARGET")


def prompt_advice_enabled() -> bool:
    """Emit LAST ATTEMPT advice labels (TRIGGER/BRIDGE/GENERALIZE/...).

    Independent of ``--strategy-mode``. Off keeps HD / library / INVALID
    without those labels.
    """
    return _flag_enabled("PROMPT_ADVICE")


def unproved_not_invalid_enabled() -> bool:
    """When on, a useful-but-unproved subgoal stays off invalid_lemmas (tree-only)."""
    return _flag_enabled("UNPROVED_NOT_INVALID")


def ancestor_cycle_filter_enabled() -> bool:
    """Drop candidates α/eq-equivalent to a strict ancestor (path cycle)."""
    return _flag_enabled("ANCESTOR_CYCLE_FILTER")


def ancestor_prompt_enabled() -> bool:
    """Inject PROOF PATH GOALS (CURRENT + strict ancestors) into the user prompt."""
    return _flag_enabled("ANCESTOR_PROMPT")


def cvc_patterns_enabled() -> bool:
    """CVC ``:pattern`` CLI/env flag. Default **off** (temporarily unused).

    Feedback-gated 6-way ±pattern is deprecated: ``should_add_cvc_patterns``
    stays false even if this returns true. Re-enable only with
    ``PATTERN_FEEDBACK_GATE_ENABLED`` in ``smt_patterns.py``.
    """
    return _flag_enabled("CVC_PATTERNS", default="off")


def resolve_cvc_patterns_enabled(override: Optional[bool] = None) -> bool:
    """CLI/prove_run override, else ``CVC_PATTERNS`` env (default off)."""
    if override is not None:
        return bool(override)
    return cvc_patterns_enabled()


def apply_cvc_patterns_cli(value: Optional[str]) -> None:
    """Set ``CVC_PATTERNS`` from ``--cvc-patterns on|off`` (None = leave env)."""
    if value is None:
        return
    os.environ["CVC_PATTERNS"] = "on" if str(value).strip().lower() in (
        "on", "1", "true", "yes",
    ) else "off"


# Fail-fast / child-budget switches live in lemma_gates.py (same default-on
# pattern). paper.env must set them off / CHILD_LLM_ATTEMPTS=0 / LLM_PARSE_RETRIES=0.


def normalize_strategy_mode(strategy_mode: str) -> str:
    mode = (strategy_mode or "default").strip().lower().replace("-", "_")
    if mode in ("naive",):
        return "naive"
    if mode in ("zero_shot", "zeroshot"):
        return "zero_shot"
    if mode in ("v2_simple", "v2_compact", "general_ind_simple"):
        return "v2_simple"
    if mode in ("v2", "general_ind", "general_induction"):
        return "v2"
    if mode in ("default_simple", "ours_simple", "simple"):
        return "default_simple"
    if mode in ("default", "ours", ""):
        return "default"
    return "default"


def is_v2_strategy_mode(strategy_mode: str) -> bool:
    """True for ``v2`` and ``v2_simple`` (lemma_general pack)."""
    return normalize_strategy_mode(strategy_mode) in ("v2", "v2_simple")


def resolve_prompt_pack(
    strategy_mode: str,
    max_attempts_per_prompt: int,
) -> Dict[str, Any]:
    """Prompt folder, templates, and attempt budget for ``--strategy-mode``.

    ``MAX_ATTEMPTS_PER_PROMPT`` is N (default 3). Paper / ours uses N attempts
    on each of two templates (2N total). Naive uses the single ``prompt_naive``
    template 2N times so the LLM-call budget matches. ``zero_shot`` currently
    uses the same ours pack as ``default`` (no separate prompt folder).

    ``default_simple`` uses the same two template *names* as ``default``, but
    loads shortened system prompts from ``prompts_ours_compact``.

    ``v2`` uses ``prompts_v2`` with only ``lemma_general`` (budget 2N).
    ``v2_simple`` uses the same template name and budget from
    ``prompts_v2_compact``. Retarget on/off does not change the template:
    the pool is a singleton, so ``prompt_retarget_active`` is false either way.
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
            "no_retarget_prompt": None,
        }
    if mode == "v2":
        strategies = list(V2_PROMPT_STRATEGIES)
        return {
            "mode": mode,
            "folder_path": "./prompts_v2",
            "strategies": strategies,
            "max_attempts_per_prompt": n,
            "total_attempts": n * 2,
            "no_retarget_prompt": V2_LEMMA_GENERAL,
        }
    if mode == "v2_simple":
        strategies = list(V2_PROMPT_STRATEGIES)
        return {
            "mode": mode,
            "folder_path": "./prompts_v2_compact",
            "strategies": strategies,
            "max_attempts_per_prompt": n,
            "total_attempts": n * 2,
            "no_retarget_prompt": V2_LEMMA_GENERAL,
        }
    if mode == "default_simple":
        strategies = list(OURS_PROMPT_STRATEGIES)
        return {
            "mode": mode,
            "folder_path": "./prompts_ours_compact",
            "strategies": strategies,
            "max_attempts_per_prompt": n,
            "total_attempts": n * len(strategies),
            "no_retarget_prompt": None,
        }
    strategies = list(OURS_PROMPT_STRATEGIES)
    return {
        "mode": mode,
        "folder_path": "./prompts_ours",
        "strategies": strategies,
        "max_attempts_per_prompt": n,
        "total_attempts": n * len(strategies),
        "no_retarget_prompt": None,
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
