"""Feedback-guided solver routing shared by Vampire and CVC5 backends.

Phase 1: theory features + named profiles + persisted GoalSearchState.
Phase 2: hint-driven re-ranking, top-k selection, parent/child inheritance.
Phase 3: prompt/profile pair state, per-attempt telemetry, and an optional
backend-specific LLM selector (implemented in profile_selector.py).

This module does not invoke solvers. Runners execute the chosen profiles;
Mate persists the routing state in failed_lemmas.json.
"""

from __future__ import annotations

import logging
import os
import random
from dataclasses import asdict, dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from solver_relative_metrics import log_gain
from theory_features import TheoryFeatures


VAMPIRE_FALLBACK_PROFILE = "induction_portfolio"
CVC5_FALLBACK_PROFILES = [
    "cvc5_simple",
    "cvc5_inductive",
    "cvc5_inductive_no_ematching",
    "cvc4_default",
]

VAMPIRE_PROMPT_GUIDANCE = {
    "induction_portfolio": (
        "The backend uses Vampire's mixed induction portfolio (paper default). "
        "Both constructor rewrite lemmas and inductive generalizations are useful."
    ),
    "struct_induction": (
        "The backend is focused on datatype structural induction. "
        "Generate constructor-aware equational lemmas and inductive-step bridges."
    ),
    "struct_induction_tip": (
        "The backend uses a TIP-oriented structural induction schedule. "
        "Prefer small datatype identities close to recursive definitions."
    ),
    "integer_induction": (
        "The backend is focused on integer induction. "
        "Generate arithmetic recurrence, monotonicity, or bound lemmas, not ADT constructor facts."
    ),
    "smtcomp": (
        "The backend uses an SMT-COMP arithmetic schedule. "
        "Prefer LIA-friendly lemmas and avoid datatype-only constructor equalities."
    ),
    "struct_single": (
        "The diagnostic backend applies structural induction only. "
        "Target constructor cases and rewrite under the inductive hypothesis."
    ),
    "int_single": (
        "The diagnostic backend applies integer induction only. "
        "Generate recurrence / interval lemmas."
    ),
    "alasca_arith": (
        "The backend uses ALASCA-style arithmetic superposition "
        "(unification with abstraction + theory instantiation). "
        "Generate linear-arithmetic bridge lemmas and quantified arithmetic facts."
    ),
}

CVC5_PROMPT_GUIDANCE = {
    "cvc5_simple": (
        "The backend uses full quantifier saturation without explicit induction. "
        "Generate lemmas that instantiate or rewrite toward the goal."
    ),
    "cvc5_inductive": (
        "The backend uses cvc5 quantifier induction + conjecture generation. "
        "Generalized inductive lemmas and rewrite bridges are both useful."
    ),
    "cvc5_inductive_no_ematching": (
        "The backend disabled E-matching to limit instantiation explosion. "
        "Generate smaller, goal-directed rewrite lemmas rather than broad quantified conjectures."
    ),
    "cvc4_default": (
        "The backend may fall back to CVC4 inductive reasoning. "
        "Keep lemmas simple and close to recursive definitions."
    ),
    "adt_structural": (
        "The backend strengthens datatype structural induction. "
        "Generate constructor/selector lemmas and datatype case-split facts."
    ),
    "integer_recursive": (
        "The backend uses integer well-founded induction. "
        "Generate arithmetic recurrence and monotonicity lemmas."
    ),
    "controlled_conjecture": (
        "The backend runs conjecture-gen with a reduced enumeration budget. "
        "Avoid wide quantified conjectures; add local bridging equalities."
    ),
}

# Rewrite-family hints → term_rewrite template (matching / demodulation lemmas).
# Generalize-family hints → equational template (induction-case bridges / stronger IH).
_REWRITE_HINTS = {"need_rewrite", "induction_stuck", "need_directed_rewrite"}
_GENERALIZE_HINTS = {
    "need_induction_lemma",
    "need_stronger_lemma",
    "need_arithmetic_lemma",
    "induction_depth_limit",
}
_EXPLOSION_HINTS = {"search_explosion", "timeout"}

EQUATIONAL_PROMPT = "prove_prompt_equational_reasoning"
TERM_REWRITE_PROMPT = "prove_prompt_term_rewrite"


@dataclass
class GoalSearchState:
    """Per-goal routing state stored in failed_lemmas.json under key 'routing'."""
    backend: str = ""
    theory_features: dict = field(default_factory=dict)
    candidate_profiles: List[str] = field(default_factory=list)
    active_profile: Optional[str] = None
    active_prompt: Optional[str] = None
    decision_mode: str = "relative"
    decision_source: str = "static"
    decision_confidence: float = 0.0
    fallback_profiles: List[str] = field(default_factory=list)
    parent_profile: Optional[str] = None
    routing_reasons: List[str] = field(default_factory=list)
    profile_history: List[dict] = field(default_factory=list)
    pair_history: List[dict] = field(default_factory=list)
    prompt_guidance: str = ""

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Optional[dict]) -> "GoalSearchState":
        if not data:
            return cls()
        known = {f.name for f in cls.__dataclass_fields__.values()}  # type: ignore[attr-defined]
        return cls(**{k: v for k, v in data.items() if k in known})


def routing_enabled() -> bool:
    val = os.getenv("SOLVER_ROUTING", "on").strip().lower()
    return val not in ("0", "off", "false", "no")


def fallback_enabled() -> bool:
    val = os.getenv("SOLVER_ROUTING_FALLBACK", "on").strip().lower()
    return val not in ("0", "off", "false", "no")


def probe_timeout_s() -> int:
    try:
        return max(1, int(os.getenv("SOLVER_PROBE_TIMEOUT", "2")))
    except ValueError:
        return 2


def probes_enabled() -> bool:
    val = os.getenv("SOLVER_ROUTING_PROBES", "on").strip().lower()
    return val not in ("0", "off", "false", "no")


def top_k_profiles() -> int:
    try:
        return max(1, int(os.getenv("SOLVER_ROUTING_TOP_K", "2")))
    except ValueError:
        return 2


def probe_profile_count() -> int:
    """Number of ranked profiles to observe before final top-k selection."""
    try:
        return max(top_k_profiles(), int(os.getenv("SOLVER_ROUTING_PROBE_MAX_PROFILES", "3")))
    except ValueError:
        return max(top_k_profiles(), 3)


def fallback_fraction() -> float:
    try:
        return max(0.0, min(0.8, float(os.getenv("SOLVER_ROUTING_FALLBACK_FRACTION", "0.25"))))
    except ValueError:
        return 0.25


def fallback_min_timeout() -> int:
    try:
        return max(1, int(os.getenv("SOLVER_ROUTING_FALLBACK_MIN_SECONDS", "5")))
    except ValueError:
        return 5


def hint_kinds(hints: Sequence[dict]) -> List[str]:
    return [str(h.get("kind", "")) for h in hints if h.get("kind")]


def recommend_vampire_profiles(
    features: TheoryFeatures,
    hints: Sequence[dict] = (),
    *,
    parent_profile: Optional[str] = None,
) -> Tuple[List[str], List[str]]:
    """Return (ordered candidate profiles, reasons). Paper default is always last fallback."""
    reasons: List[str] = []
    ranked: List[str] = []

    kinds = set(hint_kinds(hints))
    if features.mixed_adt_lia:
        ranked = ["induction_portfolio", "smtcomp", "alasca_arith", "struct_induction"]
        reasons.append("static:mixed_adt_lia")
    elif features.has_int and not features.has_adt:
        ranked = ["integer_induction", "alasca_arith", "smtcomp", "induction_portfolio"]
        reasons.append("static:integer")
    elif features.has_adt:
        ranked = ["struct_induction", "induction_portfolio", "struct_induction_tip"]
        reasons.append("static:adt")
    else:
        ranked = ["induction_portfolio", "smtcomp"]
        reasons.append("static:default")

    if "need_arithmetic_lemma" in kinds:
        _boost(ranked, ["alasca_arith", "integer_induction", "smtcomp"])
        reasons.append("hint:need_arithmetic_lemma")
    if kinds & _EXPLOSION_HINTS:
        _boost(ranked, ["struct_induction", "struct_single"])
        reasons.append("hint:search_explosion_or_timeout")
    if kinds & _REWRITE_HINTS:
        _boost(ranked, ["struct_induction", "induction_portfolio"])
        reasons.append("hint:need_rewrite_or_induction_stuck")
    if "need_induction_lemma" in kinds or "induction_depth_limit" in kinds:
        _boost(ranked, ["induction_portfolio", "struct_induction"])
        if "need_induction_lemma" in kinds:
            reasons.append("hint:need_induction_lemma")
        if "induction_depth_limit" in kinds:
            reasons.append("hint:induction_depth_limit")

    if parent_profile:
        _boost(ranked, [parent_profile])
        reasons.append(f"inherit:{parent_profile}")

    ranked = _dedup_keep(ranked)
    if VAMPIRE_FALLBACK_PROFILE not in ranked:
        ranked.append(VAMPIRE_FALLBACK_PROFILE)
    return ranked, reasons


def recommend_cvc5_profiles(
    features: TheoryFeatures,
    hints: Sequence[dict] = (),
    *,
    parent_profile: Optional[str] = None,
) -> Tuple[List[str], List[str]]:
    reasons: List[str] = []
    ranked: List[str] = []
    kinds = set(hint_kinds(hints))

    if features.mixed_adt_lia:
        ranked = ["cvc5_inductive", "cvc5_inductive_no_ematching", "integer_recursive", "cvc5_simple"]
        reasons.append("static:mixed_adt_lia")
    elif features.has_int and not features.has_adt:
        ranked = ["integer_recursive", "cvc5_inductive", "cvc5_simple"]
        reasons.append("static:integer")
    elif features.has_adt:
        ranked = ["adt_structural", "cvc5_inductive", "cvc5_inductive_no_ematching", "cvc5_simple"]
        reasons.append("static:adt")
    else:
        ranked = list(CVC5_FALLBACK_PROFILES)
        reasons.append("static:default")

    if "need_rewrite" in kinds:
        _boost(ranked, ["cvc5_inductive_no_ematching", "cvc5_simple"])
        reasons.append("hint:need_rewrite")
    if "need_stronger_lemma" in kinds:
        _boost(ranked, ["cvc5_inductive", "adt_structural", "integer_recursive"])
        reasons.append("hint:need_stronger_lemma")
    if kinds & _EXPLOSION_HINTS or "search_explosion" in kinds:
        _boost(ranked, ["controlled_conjecture", "cvc5_inductive_no_ematching"])
        reasons.append("hint:search_explosion_or_timeout")
    if "high_difficulty_assertions" in kinds and features.has_adt:
        _boost(ranked, ["adt_structural", "cvc5_inductive"])
        reasons.append("hint:high_difficulty_assertions")
    if "need_arithmetic_lemma" in kinds:
        _boost(ranked, ["integer_recursive", "cvc5_inductive"])
        reasons.append("hint:need_arithmetic_lemma")

    if parent_profile:
        _boost(ranked, [parent_profile])
        reasons.append(f"inherit:{parent_profile}")

    ranked = _dedup_keep(ranked)
    for name in CVC5_FALLBACK_PROFILES:
        if name not in ranked:
            ranked.append(name)
    return ranked, reasons


def recommend_profiles(
    backend: str,
    features: TheoryFeatures,
    hints: Sequence[dict] = (),
    *,
    parent_profile: Optional[str] = None,
) -> Tuple[List[str], List[str]]:
    if backend == "vampire":
        return recommend_vampire_profiles(features, hints, parent_profile=parent_profile)
    return recommend_cvc5_profiles(features, hints, parent_profile=parent_profile)


def select_top_profiles(
    ranked: Sequence[str],
    utilities: Optional[Dict[str, float]] = None,
    *,
    k: Optional[int] = None,
) -> List[str]:
    """Keep top-k by probe utility when available, else keep static order."""
    k = k or top_k_profiles()
    if not utilities:
        return list(ranked)[:k]
    scored = sorted(
        ranked,
        key=lambda name: (-float(utilities.get(name, -1e9)), ranked.index(name)),
    )
    return scored[:k]


def signal_kind(text: str) -> str:
    """Strip '(+12%)' / '(8->2,75%)' suffixes from a progress signal."""
    return str(text).split("(", 1)[0].strip()


def collect_feedback_signal_kinds(
    hints: Sequence[dict] = (),
    progress_lemmas: Sequence[dict] = (),
    extra: Sequence[str] = (),
) -> List[str]:
    """Unique routing tokens from repair hints, 3s lemma signals, and extras."""
    out: List[str] = []
    seen = set()

    def _add(raw: object) -> None:
        kind = signal_kind(raw) if raw else ""
        if kind and kind not in seen:
            seen.add(kind)
            out.append(kind)

    for hint in hints:
        _add(hint.get("kind", ""))
        for item in hint.get("progress_signals") or []:
            _add(item)
    for record in progress_lemmas:
        for item in record.get("signals") or []:
            _add(item)
    for item in extra or []:
        _add(item)
    return out


_KEEP_SIGNAL_PREFIXES = (
    "goal_difficulty_drop",
    "axiom_difficulty_drop",
    "more_skolemize",
    "more_datatype_inference",
    "more_induction_activity",
    "more_demodulations",
    "lower_passive_ratio",
)
_LEMMA_FEEDBACK_HINTS = {"no_progress", "partial_progress"}


def _has_prefix(kinds: Sequence[str], prefixes: Sequence[str]) -> bool:
    return any(any(kind == p or kind.startswith(p) for p in prefixes) for kind in kinds)


def apply_progress_routing(
    backend: str,
    ranked: Sequence[str],
    signal_kinds: Sequence[str],
    current_profile: Optional[str] = None,
) -> Tuple[List[str], List[str]]:
    """Reorder profiles from matched 3s progress / explosion / no-signal.

    Does not compute a numeric utility. Keep / switch / try-next are discrete.
    """
    out = list(ranked)
    reasons: List[str] = []
    kinds = list(signal_kinds)
    if not kinds:
        return out, reasons

    strong_keep = _has_prefix(kinds, _KEEP_SIGNAL_PREFIXES) or "partial_progress" in kinds
    explosion = _has_prefix(kinds, ("search_explosion",))
    no_signal = (
        "no_progress" in kinds or "no_measurable_progress" in kinds
    ) and not strong_keep

    if explosion and not _has_prefix(
        kinds,
        (
            "goal_difficulty_drop",
            "axiom_difficulty_drop",
            "more_skolemize",
            "more_induction_activity",
        ),
    ):
        if backend == "vampire":
            _boost(out, ["struct_induction", "struct_single"])
        else:
            _boost(out, ["controlled_conjecture", "cvc5_inductive_no_ematching"])
        reasons.append("progress:search_explosion")
        return _dedup_keep(out), reasons

    if strong_keep:
        if _has_prefix(kinds, ("more_datatype_inference",)):
            if backend == "vampire":
                _boost(out, ["struct_induction"])
            else:
                _boost(out, ["adt_structural"])
            reasons.append("progress:more_datatype")
        if current_profile:
            _boost(out, [current_profile])
            reasons.append("progress:keep_profile")
        return _dedup_keep(out), reasons

    if no_signal and current_profile and current_profile in out:
        out = [name for name in out if name != current_profile] + [current_profile]
        reasons.append("progress:try_next_profile")
        return _dedup_keep(out), reasons

    return _dedup_keep(out), reasons


def rank_profiles_for_attempt(
    backend: str,
    features: TheoryFeatures,
    hints: Sequence[dict] = (),
    *,
    parent_profile: Optional[str] = None,
    current_profile: Optional[str] = None,
    progress_lemmas: Sequence[dict] = (),
    extra_signals: Sequence[str] = (),
    probe_utilities: Optional[Dict[str, float]] = None,
) -> Tuple[List[str], List[str], List[str]]:
    """Static + hint rank, then 3s progress rerank, then top-k.

    Probe scores apply only before any lemma-failure sidecar exists; after that
    they must not override keep / switch / try-next.
    """
    ranked, reasons = recommend_profiles(
        backend, features, hints, parent_profile=parent_profile
    )
    signals = collect_feedback_signal_kinds(hints, progress_lemmas, extra_signals)
    ranked, extra = apply_progress_routing(
        backend, ranked, signals, current_profile=current_profile
    )
    reasons = list(reasons) + extra
    lemma_feedback = bool(
        set(hint_kinds(hints)) & _LEMMA_FEEDBACK_HINTS
        or extra_signals
        or progress_lemmas
    )
    utilities = None if lemma_feedback else probe_utilities
    candidates = select_top_profiles(ranked, utilities)
    return ranked, candidates, reasons


def profile_utility_from_stats(
    *,
    backend: str,
    proved: bool,
    status: str,
    stats: dict,
    elapsed: float = 1.0,
    reference_stats: Optional[dict] = None,
    reference_elapsed: Optional[float] = None,
) -> Tuple[float, List[str]]:
    """Score a probe.

    When a matched reference is supplied, use scale-free rate gains. Without
    one, score status only — never absolute volume cutoffs such as gen>2000.
    """
    if proved:
        return 100.0, ["proved"]
    if status == "error":
        return -20.0, ["solver_error"]
    if reference_stats is not None:
        return _relative_profile_utility(
            backend=backend,
            status=status,
            stats=stats,
            elapsed=elapsed,
            reference_stats=reference_stats,
            reference_elapsed=reference_elapsed if reference_elapsed is not None else elapsed,
        )

    signals: List[str] = ["status_only"]
    score = 0.0
    if status in ("timeout", "unknown", "incomplete"):
        score -= 0.1
    return score, signals


def _relative_profile_utility(
    *,
    backend: str,
    status: str,
    stats: dict,
    elapsed: float,
    reference_stats: dict,
    reference_elapsed: float,
) -> Tuple[float, List[str]]:
    """Compare profile activity rates against a common paper-profile probe."""
    elapsed = max(float(elapsed), 0.2)
    reference_elapsed = max(float(reference_elapsed), 0.2)

    def rate(data: dict, key: str, duration: float) -> float:
        return max(float(data.get(key, 0)), 0.0) / duration

    def gain(key: str) -> float:
        return log_gain(
            rate(stats, key, elapsed),
            rate(reference_stats, key, reference_elapsed),
        )

    signals: List[str] = []
    score = 0.0
    if backend == "vampire":
        induction = sum(
            gain(key)
            for key in (
                "InductionApplications",
                "StructuralInduction",
                "GeneralizedInductionApplications",
            )
        )
        integer_induction = sum(
            gain(key)
            for key in (
                "IntegerInfiniteIntervalInduction",
                "IntegerFiniteIntervalInduction",
            )
        )
        rewrite = gain("Fw demodulations") + gain("Bw demodulations")
        generated = gain("Generated clauses")
        if induction > 0:
            score += min(induction / 0.693, 3.0)
            signals.append("relative_induction_gain")
        if integer_induction > 0:
            score += min(integer_induction / 0.693, 2.5)
            signals.append("relative_integer_induction_gain")
        if rewrite > 0:
            score += min(rewrite / 0.693, 1.5)
            signals.append("relative_rewrite_gain")
        if generated >= 0.405 and induction <= 0 and integer_induction <= 0:
            score -= 1.5
            signals.append("relative_search_explosion")
    else:
        induction = gain("QUANTIFIERS_SKOLEMIZE")
        inst = gain("INST_TOTAL")
        datatypes = gain("DT_TOTAL")
        conjecture = gain("CONJ_TOTAL")
        productive = induction > 0 or inst > 0 or datatypes > 0
        if induction > 0:
            score += min(induction / 0.693, 2.5)
            signals.append("relative_skolemize_gain")
        if inst > 0:
            score += min(inst / 0.693, 1.5)
            signals.append("relative_instantiation_gain")
        if datatypes > 0:
            score += min(datatypes / 0.693, 1.5)
            signals.append("relative_datatype_gain")
        if conjecture > 0 and not productive:
            score += min(conjecture / 0.693, 0.8)
            signals.append("relative_conjecture_gain")
        if conjecture >= 0.405 and not productive:
            score -= 1.5
            signals.append("relative_search_explosion")
    if status in ("timeout", "unknown", "incomplete"):
        score -= 0.1
    if not signals:
        signals.append("no_relative_probe_gain")
    return score, signals


def preferred_prompt_for_hints(hints: Sequence[dict]) -> Optional[str]:
    """Template that matches a single hint family, or None if mixed / empty.

    Rewrite-family kinds ask for lemmas that fire matching and demodulation;
    that is ``prove_prompt_term_rewrite``. Generalize / induction-family kinds
    ask for induction-case bridges and stronger IHs; that is
    ``prove_prompt_equational_reasoning``.
    """
    kinds = set(hint_kinds(hints))
    has_generalize = bool(kinds & _GENERALIZE_HINTS)
    has_rewrite = bool(kinds & _REWRITE_HINTS)
    if has_rewrite and not has_generalize:
        return TERM_REWRITE_PROMPT
    if has_generalize and not has_rewrite:
        return EQUATIONAL_PROMPT
    return None


def order_prompt_strategies(
    strategies: Sequence[str],
    hints: Sequence[dict],
) -> List[str]:
    """Reorder the paper prompt pool; never drop a strategy.

    One hint family: that family's template goes first. Both families: keep
    the given order — ``select_generation_prompt`` samples instead.
    """
    prefer = preferred_prompt_for_hints(hints)
    if not prefer:
        return list(strategies)
    return sorted(strategies, key=lambda s: 0 if s == prefer else 1)


# Consecutive empty / invalid / useless attempts before switching generation mode.
NO_HELP_PROMPT_SWITCH = 2
# Present-but-zero overshoot still votes, so a kind on the gate is not dropped.
_FAMILY_STRENGTH_FLOOR = 0.05
_prompt_mode_rng: Optional[random.Random] = None


def _hint_strength(hint: dict) -> float:
    raw = hint.get("strength")
    if raw is None:
        return 1.0
    try:
        return max(0.0, float(raw))
    except (TypeError, ValueError):
        return 1.0


def prompt_family_scores(hints: Sequence[dict]) -> Tuple[float, float]:
    """Return (rewrite_family, generalize_family) weights. 0 means the family is absent."""
    rewrite = 0.0
    generalize = 0.0
    rewrite_seen = False
    generalize_seen = False
    for hint in hints:
        kind = str(hint.get("kind") or "")
        if kind in _REWRITE_HINTS:
            rewrite_seen = True
            rewrite += _hint_strength(hint)
        elif kind in _GENERALIZE_HINTS:
            generalize_seen = True
            generalize += _hint_strength(hint)
    if rewrite_seen:
        rewrite = max(rewrite, _FAMILY_STRENGTH_FLOOR)
    if generalize_seen:
        generalize = max(generalize, _FAMILY_STRENGTH_FLOOR)
    return rewrite, generalize


def term_rewrite_sample_prob(hints: Sequence[dict]) -> Optional[float]:
    """P(term-rewrite template) when both families fire; otherwise None.

    Weight follows rewrite-family strength, matching
    ``preferred_prompt_for_hints`` (rewrite → term_rewrite).
    """
    rewrite, generalize = prompt_family_scores(hints)
    if rewrite <= 0 or generalize <= 0:
        return None
    return rewrite / (generalize + rewrite)


def prompt_kind_signature(hints: Sequence[dict]) -> str:
    """Coarse family set: none / rewrite / generalize / both."""
    rewrite, generalize = prompt_family_scores(hints)
    if rewrite > 0 and generalize > 0:
        return "both"
    if generalize > 0:
        return "generalize"
    if rewrite > 0:
        return "rewrite"
    return "none"


def _prompt_mode_rng_instance() -> random.Random:
    global _prompt_mode_rng
    if _prompt_mode_rng is None:
        seed = os.getenv("PROMPT_MODE_SEED", "").strip()
        if not seed:
            _prompt_mode_rng = random.Random()
        else:
            try:
                _prompt_mode_rng = random.Random(int(seed))
            except ValueError:
                _prompt_mode_rng = random.Random(seed)
    return _prompt_mode_rng


def reset_prompt_mode_rng() -> None:
    """Drop the process RNG so the next call re-reads ``PROMPT_MODE_SEED``."""
    global _prompt_mode_rng
    _prompt_mode_rng = None


def select_generation_prompt(
    strategies: Sequence[str],
    hints: Sequence[dict],
    *,
    rng: Optional[random.Random] = None,
) -> str:
    """Starting LLM template from existing repair-hint kinds.

    One family: that family's template (rewrite → term_rewrite,
    generalize → equational). Both families: sample with
    P(term_rewrite) = rewrite_strength / (generalize + rewrite), using
    mix-gate overshoot stored on each hint. Does not drop a strategy from the pool.
    """
    pool = [s for s in strategies if s]
    if not pool:
        return ""
    p_rewrite = term_rewrite_sample_prob(hints)
    if p_rewrite is None:
        return order_prompt_strategies(pool, hints)[0]
    if TERM_REWRITE_PROMPT not in pool or EQUATIONAL_PROMPT not in pool:
        return order_prompt_strategies(pool, hints)[0]
    sampler = rng if rng is not None else _prompt_mode_rng_instance()
    pick = TERM_REWRITE_PROMPT if sampler.random() < p_rewrite else EQUATIONAL_PROMPT
    rewrite_score, generalize_score = prompt_family_scores(hints)
    logging.info(
        "两类 prompt-kind 同时存在，P(term_rewrite)=%.3f (generalize=%.3f rewrite=%.3f) → %s",
        p_rewrite,
        generalize_score,
        rewrite_score,
        pick,
    )
    return pick


def advance_generation_prompt(
    strategies: Sequence[str],
    current: str,
    consecutive_no_help: int,
    *,
    switch_after: int = NO_HELP_PROMPT_SWITCH,
) -> Tuple[str, int, bool]:
    """Toggle the other paper prompt after consecutive empty/invalid/useless attempts.

    Hint kinds only pick the starting template. This helper does not read or
    rewrite repair hints; it only changes which generation template is used next.
    """
    pool = [s for s in strategies if s]
    if not pool:
        return current or "", consecutive_no_help, False
    if current not in pool:
        return pool[0], 0, bool(current) and current != pool[0]
    if consecutive_no_help < switch_after or len(pool) < 2:
        return current, consecutive_no_help, False
    nxt = pool[(pool.index(current) + 1) % len(pool)]
    return nxt, 0, True


def retarget_generation_prompt(
    strategies: Sequence[str],
    hints: Sequence[dict],
    current: str,
    consecutive_no_help: int,
    last_signature: str,
    *,
    rng: Optional[random.Random] = None,
    switch_after: int = NO_HELP_PROMPT_SWITCH,
) -> Tuple[str, int, str, str]:
    """After a no-help attempt, maybe change the generation template.

    - Kind family set changed: re-run one-family kind pick or both-family sample.
    - Same family set: only consecutive empty/invalid/useless can toggle.

    Returns (prompt, consecutive_no_help, signature, reason)
    with reason in ``kind`` / ``consecutive`` / ``keep``.
    """
    signature = prompt_kind_signature(hints)
    if signature != last_signature:
        nxt = select_generation_prompt(strategies, hints, rng=rng)
        if nxt != current:
            logging.info(
                "失败反馈 kind %s → %s，切换 prompt %s → %s",
                last_signature,
                signature,
                current,
                nxt,
            )
            return nxt, 0, signature, "kind"
        return current, consecutive_no_help, signature, "keep"
    nxt, consecutive_no_help, switched = advance_generation_prompt(
        strategies, current, consecutive_no_help, switch_after=switch_after
    )
    if switched:
        return nxt, consecutive_no_help, signature, "consecutive"
    return current, consecutive_no_help, signature, "keep"


def prompt_guidance_for(backend: str, profile: Optional[str]) -> str:
    table = VAMPIRE_PROMPT_GUIDANCE if backend == "vampire" else CVC5_PROMPT_GUIDANCE
    if profile and profile in table:
        return table[profile]
    if backend == "vampire":
        return table[VAMPIRE_FALLBACK_PROFILE]
    return table["cvc5_inductive"]


def fallback_profiles_for(backend: str) -> List[str]:
    if backend == "vampire":
        return [VAMPIRE_FALLBACK_PROFILE]
    return list(CVC5_FALLBACK_PROFILES)


def build_search_state(
    backend: str,
    features: TheoryFeatures,
    hints: Sequence[dict] = (),
    *,
    parent_profile: Optional[str] = None,
    utilities: Optional[Dict[str, float]] = None,
    history: Optional[List[dict]] = None,
) -> GoalSearchState:
    ranked, reasons = recommend_profiles(
        backend, features, hints, parent_profile=parent_profile
    )
    top = select_top_profiles(ranked, utilities)
    active = top[0] if top else None
    fallback = fallback_profiles_for(backend)
    return GoalSearchState(
        backend=backend,
        theory_features=features.to_dict(),
        candidate_profiles=top,
        active_profile=active,
        decision_mode=os.getenv("SOLVER_ROUTING_DECIDER", "relative").strip().lower(),
        fallback_profiles=fallback,
        parent_profile=parent_profile,
        routing_reasons=reasons,
        profile_history=list(history or []),
        prompt_guidance=prompt_guidance_for(backend, active),
    )


def record_profile_history(
    state: GoalSearchState,
    profile: str,
    *,
    status: str,
    utility: float,
    signals: Iterable[str] = (),
) -> GoalSearchState:
    entry = {
        "profile": profile,
        "status": status,
        "utility": round(float(utility), 3),
        "signals": list(signals)[:6],
    }
    history = [h for h in state.profile_history if h.get("profile") != profile]
    history.append(entry)
    state.profile_history = history[-8:]
    return state


def apply_routing_decision(state: GoalSearchState, decision: object) -> GoalSearchState:
    """Apply a validated selector result without accepting arbitrary options."""
    profile = getattr(decision, "profile", None)
    prompt = getattr(decision, "prompt_strategy", None)
    if profile:
        state.active_profile = str(profile)
        # An LLM-selected profile is intentionally a single primary profile.
        # The runner may still use its explicit paper fallback.
        if getattr(decision, "source", "") == "llm":
            state.candidate_profiles = [state.active_profile]
    if prompt:
        state.active_prompt = str(prompt)
    state.decision_source = str(getattr(decision, "source", "static"))
    try:
        state.decision_confidence = float(getattr(decision, "confidence", 0.0))
    except (TypeError, ValueError):
        state.decision_confidence = 0.0
    reason = getattr(decision, "reason", "")
    if reason:
        state.routing_reasons = list(state.routing_reasons) + [f"decision:{reason}"]
        state.routing_reasons = state.routing_reasons[-8:]
    state.prompt_guidance = prompt_guidance_for(state.backend, state.active_profile)
    return state


def set_routing_candidates(
    state: GoalSearchState,
    ranked_profiles: Sequence[str],
    *,
    active_profile: Optional[str] = None,
    active_prompt: Optional[str] = None,
) -> GoalSearchState:
    """Update the allowed primary profiles without changing fallback semantics."""
    state.candidate_profiles = _dedup_keep(list(ranked_profiles))
    if active_profile:
        state.active_profile = active_profile
    elif state.candidate_profiles and state.active_profile not in state.candidate_profiles:
        state.active_profile = state.candidate_profiles[0]
    if active_prompt:
        state.active_prompt = active_prompt
    state.prompt_guidance = prompt_guidance_for(state.backend, state.active_profile)
    return state


def record_pair_attempt(
    state: GoalSearchState,
    *,
    prompt_strategy: Optional[str],
    profile: Optional[str],
    status: str,
    proved: bool = False,
    elapsed: float = 0.0,
    utility: Optional[float] = None,
    signals: Iterable[str] = (),
    fallback_used: bool = False,
    decision_source: Optional[str] = None,
    winner_profile: Optional[str] = None,
) -> GoalSearchState:
    """Append compact telemetry for a prompt/profile action."""
    entry = {
        "prompt_strategy": prompt_strategy or "",
        "profile": profile or "",
        # A timed-out/failed portfolio has no winner.  Keep the selected
        # profile in ``profile`` and reserve this field for an actual winner.
        "winner_profile": winner_profile or "",
        "candidate_profiles": list(state.candidate_profiles),
        "status": status,
        "proved": bool(proved),
        "elapsed": round(float(elapsed), 3),
        "utility": None if utility is None else round(float(utility), 3),
        "signals": list(signals)[:8],
        "fallback_used": bool(fallback_used),
        "decision_source": decision_source or state.decision_source,
    }
    state.pair_history = (state.pair_history + [entry])[-20:]
    return state


def format_routing_for_prompt(state: Optional[GoalSearchState]) -> str:
    if state is None or not state.active_profile:
        return ""
    parts = [
        "\nSOLVER ROUTING (feedback-guided theory portfolio):",
        f"  backend={state.backend}, recommended_profile={state.active_profile}",
        f"  decision_mode={state.decision_mode}, source={state.decision_source}",
        f"  candidates={', '.join(state.candidate_profiles)}",
    ]
    if state.active_prompt:
        parts.append(f"  recommended_prompt={state.active_prompt}")
    feats = state.theory_features or {}
    parts.append(
        "  theory: "
        f"ADT={feats.get('has_adt')}, Int={feats.get('has_int')}, "
        f"mixed={feats.get('mixed_adt_lia')}, logic={feats.get('logic', '')}"
    )
    if state.routing_reasons:
        parts.append(f"  reasons: {', '.join(state.routing_reasons[:6])}")
    if state.prompt_guidance:
        parts.append(f"  {state.prompt_guidance}")
    if state.pair_history:
        parts.append("  recent prompt/profile outcomes:")
        for item in state.pair_history[-4:]:
            pair = f"{item.get('prompt_strategy', '?')} + {item.get('profile', '?')}"
            outcome = item.get("status", "unknown")
            if item.get("proved"):
                outcome = "proved"
            fallback = " [fallback]" if item.get("fallback_used") else ""
            winner = item.get("winner_profile")
            winner_text = (
                f", winner={winner}"
                if winner and winner != item.get("profile")
                else ""
            )
            signals = ", ".join(item.get("signals", [])[:3])
            signal_text = f", signals={signals}" if signals else ""
            parts.append(
                f"    {pair}: {outcome}{fallback}{winner_text}{signal_text}"
            )
    return "\n".join(parts)


def _boost(ranked: List[str], names: Sequence[str]) -> None:
    for name in reversed(names):
        if name in ranked:
            ranked.remove(name)
        ranked.insert(0, name)


def _dedup_keep(items: Sequence[str]) -> List[str]:
    seen = set()
    out: List[str] = []
    for x in items:
        if x and x not in seen:
            seen.add(x)
            out.append(x)
    return out
