"""Optional LLM controller for joint prompt/profile selection.

The selector is deliberately separate from solver execution.  It may choose
only identifiers supplied by the caller; it cannot invent command-line
options or establish a proof.  The deterministic router remains the default.
"""

from __future__ import annotations

import json
import logging
import os
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

from solver_routing import (
    CVC5_PROMPT_GUIDANCE,
    VAMPIRE_PROMPT_GUIDANCE,
    order_prompt_strategies,
)
from theory_features import TheoryFeatures


PROMPT_ROOT = Path(__file__).resolve().parent / "prompts_routing"

VAMPIRE_PROFILE_OPTIONS = {
    "induction_portfolio": "--mode portfolio --schedule induction",
    "struct_induction": "--mode portfolio --schedule struct_induction",
    "struct_induction_tip": "--mode portfolio --schedule struct_induction_tip",
    "integer_induction": "--mode portfolio --schedule integer_induction",
    "smtcomp": "--mode portfolio --schedule smtcomp",
    "struct_single": "--induction struct --induction_gen on --avatar off",
    "int_single": "--induction int --induction_gen on --avatar off",
    "alasca_arith": (
        "--induction both --theory_instantiation all "
        "--unification_with_abstraction interpreted_only "
        "--arithmetic_subterm_generalizations cautious"
    ),
}

CVC5_PROFILE_OPTIONS = {
    "cvc5_simple": "--full-saturate-quant",
    "cvc5_inductive": "--full-saturate-quant --quant-ind --conjecture-gen",
    "cvc5_inductive_no_ematching": (
        "--full-saturate-quant --quant-ind --conjecture-gen --no-e-matching"
    ),
    "cvc4_default": "--quant-ind --quant-cf --conjecture-gen --full-saturate-quant",
    "adt_structural": "--full-saturate-quant --quant-ind --dt-stc-ind",
    "integer_recursive": "--full-saturate-quant --quant-ind --int-wf-ind",
    "controlled_conjecture": (
        "--quant-ind --conjecture-gen "
        "--conjecture-gen-max-depth=2 --conjecture-gen-per-round=5"
    ),
}


@dataclass
class RoutingDecision:
    """Validated choice returned by the routing controller."""

    backend: str
    profile: str
    prompt_strategy: str
    confidence: float
    reason: str
    source: str = "static"
    error: Optional[str] = None

    def to_dict(self) -> dict:
        return asdict(self)


def routing_decider_mode() -> str:
    """Return ``relative`` (default), ``llm``, or a safe static fallback."""
    mode = os.getenv("SOLVER_ROUTING_DECIDER", "relative").strip().lower()
    return mode if mode in {"relative", "llm"} else "relative"


def llm_selector_enabled() -> bool:
    return routing_decider_mode() == "llm"


def choose_joint_action(
    *,
    llm: Any,
    backend: str,
    features: TheoryFeatures,
    candidate_profiles: Sequence[str],
    prompt_strategies: Sequence[str],
    hints: Sequence[dict] = (),
    history: Sequence[dict] = (),
    current_profile: Optional[str] = None,
    current_prompt: Optional[str] = None,
) -> RoutingDecision:
    """Choose a whitelisted prompt/profile pair.

    In ``relative`` mode no LLM call is made.  In ``llm`` mode the model sees
    backend-specific profile cards and returns JSON.  Any malformed or
    out-of-set response falls back to the deterministic choice.
    """
    profiles = [p for p in candidate_profiles if p]
    prompts = [p for p in prompt_strategies if p]
    if not profiles:
        profiles = ["induction_portfolio"] if backend == "vampire" else ["cvc5_inductive"]
    if not prompts:
        prompts = ["prove_prompt_equational_reasoning"]

    if routing_decider_mode() != "llm":
        profile, prompt = _select_relative_pair(
            profiles=profiles,
            prompts=prompts,
            hints=hints,
            history=history,
            current_profile=current_profile,
            current_prompt=current_prompt,
        )
        return RoutingDecision(
            backend=backend,
            profile=profile,
            prompt_strategy=prompt,
            confidence=1.0,
            reason="deterministic theory/hint routing",
            source="relative",
        )

    if llm is None:
        return _fallback_decision(
            backend,
            profiles,
            prompts,
            hints,
            error="LLM selector is unavailable",
        )

    messages = _build_selector_messages(
        backend=backend,
        features=features,
        candidate_profiles=profiles,
        prompt_strategies=prompts,
        hints=hints,
        history=history,
    )
    try:
        response = llm.invoke(messages)
        content = getattr(response, "content", response)
        data = _parse_json_object(str(content))
        profile = str(data.get("profile", "")).strip()
        prompt = str(data.get("prompt_strategy", "")).strip()
        confidence = _bounded_float(data.get("confidence", 0.0))
        reason = str(data.get("reason", "")).strip()[:500]
        if profile not in profiles:
            raise ValueError(f"profile is not an allowed candidate: {profile!r}")
        if prompt not in prompts:
            # Prompt selection is optional for compatibility with profile-only
            # selectors.  Use the deterministic feedback choice.
            prompt = order_prompt_strategies(prompts, hints)[0]
        if confidence < _minimum_confidence():
            raise ValueError(f"confidence below threshold: {confidence:.2f}")
        return RoutingDecision(
            backend=backend,
            profile=profile,
            prompt_strategy=prompt,
            confidence=confidence,
            reason=reason or "LLM selected an allowed profile",
            source="llm",
        )
    except Exception as exc:
        logging.warning("%s profile selector failed; using static route: %s", backend, exc)
        return _fallback_decision(
            backend,
            profiles,
            prompts,
            hints,
            error=str(exc),
        )


def _build_selector_messages(
    *,
    backend: str,
    features: TheoryFeatures,
    candidate_profiles: Sequence[str],
    prompt_strategies: Sequence[str],
    hints: Sequence[dict],
    history: Sequence[dict],
) -> List[dict]:
    backend_dir = "vampire" if backend == "vampire" else "cvc5"
    system_path = PROMPT_ROOT / backend_dir / "system_prompt.txt"
    user_path = PROMPT_ROOT / backend_dir / "user_prompt.txt"
    system = system_path.read_text(encoding="utf-8")
    template = user_path.read_text(encoding="utf-8")

    cards = _profile_cards(backend, candidate_profiles)
    compact_hints = []
    for hint in hints[-6:]:
        compact_hints.append({
            "kind": hint.get("kind", ""),
            "detail": str(hint.get("detail", ""))[:300],
            "signals": list(hint.get("suggested_actions", []))[:3],
        })
    compact_history = []
    for item in history[-8:]:
        compact_history.append({
            "prompt_strategy": item.get("prompt_strategy", ""),
            "profile": item.get("profile", ""),
            "winner_profile": item.get("winner_profile", ""),
            "candidate_profiles": item.get("candidate_profiles", [])[:6],
            "status": item.get("status", ""),
            "proved": item.get("proved", False),
            "signals": item.get("signals", [])[:5],
            "utility": item.get("utility"),
        })

    user = template.format(
        backend=backend,
        theory=features.summary(),
        theory_features=json.dumps(features.to_dict(), ensure_ascii=False),
        profiles=json.dumps(cards, ensure_ascii=False, indent=2),
        prompt_strategies=json.dumps(list(prompt_strategies), ensure_ascii=False),
        hints=json.dumps(compact_hints, ensure_ascii=False, indent=2),
        history=json.dumps(compact_history, ensure_ascii=False, indent=2),
    )
    return [
        {"role": "system", "content": system},
        {"role": "user", "content": user},
    ]


def _profile_cards(backend: str, profiles: Sequence[str]) -> List[dict]:
    guidance = VAMPIRE_PROMPT_GUIDANCE if backend == "vampire" else CVC5_PROMPT_GUIDANCE
    options = VAMPIRE_PROFILE_OPTIONS if backend == "vampire" else CVC5_PROFILE_OPTIONS
    cards = []
    for profile in profiles:
        cards.append({
            "id": profile,
            "configuration": options.get(profile, "configuration unavailable"),
            "expected_effect": guidance.get(profile, "Use the profile's documented theory strategy."),
        })
    return cards


def _fallback_decision(
    backend: str,
    profiles: Sequence[str],
    prompts: Sequence[str],
    hints: Sequence[dict],
    *,
    error: str,
) -> RoutingDecision:
    ordered = order_prompt_strategies(prompts, hints)
    return RoutingDecision(
        backend=backend,
        profile=profiles[0],
        prompt_strategy=ordered[0],
        confidence=0.0,
        reason="LLM selector unavailable or invalid; static whitelist fallback",
        source="static_fallback",
        error=error,
    )


def _select_relative_pair(
    *,
    profiles: Sequence[str],
    prompts: Sequence[str],
    hints: Sequence[dict],
    history: Sequence[dict],
    current_profile: Optional[str],
    current_prompt: Optional[str],
) -> tuple[str, str]:
    """Select a pair using static priors plus observed pair outcomes."""
    ordered_prompts = order_prompt_strategies(prompts, hints)
    prompt_rank = {name: len(ordered_prompts) - idx for idx, name in enumerate(ordered_prompts)}
    profile_rank = {name: len(profiles) - idx for idx, name in enumerate(profiles)}
    observations: Dict[tuple[str, str], dict] = {}
    for item in history:
        key = (item.get("prompt_strategy", ""), item.get("profile", ""))
        if key[0] and key[1]:
            observations[key] = item

    best_key = (ordered_prompts[0], profiles[0])
    best_score = float("-inf")
    for prompt in ordered_prompts:
        for profile in profiles:
            score = 0.25 * prompt_rank[prompt] + 0.25 * profile_rank[profile]
            if prompt == current_prompt:
                score += 0.1
            if profile == current_profile:
                score += 0.1
            observation = observations.get((prompt, profile))
            if observation is None:
                score += 0.05
            else:
                if observation.get("proved"):
                    score += 100.0
                elif observation.get("status") in {"error", "invalid_lemma"}:
                    score -= 2.0
                elif observation.get("status") in {"timeout", "unknown", "incomplete"}:
                    score -= 0.15
                if observation.get("fallback_used"):
                    score -= 0.05
                utility = observation.get("utility")
                if utility is not None:
                    try:
                        score += max(-2.0, min(3.0, float(utility)))
                    except (TypeError, ValueError):
                        pass
            if score > best_score:
                best_key = (prompt, profile)
                best_score = score
    return best_key[1], best_key[0]


def _parse_json_object(content: str) -> Dict[str, Any]:
    text = content.strip()
    fenced = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL | re.IGNORECASE)
    if fenced:
        text = fenced.group(1)
    else:
        match = re.search(r"\{.*\}", text, re.DOTALL)
        if match:
            text = match.group(0)
    value = json.loads(text)
    if not isinstance(value, dict):
        raise ValueError("selector response is not a JSON object")
    return value


def _bounded_float(value: Any) -> float:
    try:
        return max(0.0, min(1.0, float(value)))
    except (TypeError, ValueError):
        return 0.0


def _minimum_confidence() -> float:
    try:
        return max(0.0, min(1.0, float(os.getenv("SOLVER_ROUTING_LLM_MIN_CONFIDENCE", "0.55"))))
    except ValueError:
        return 0.55
