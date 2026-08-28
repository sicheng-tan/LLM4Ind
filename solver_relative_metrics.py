"""
Scale-adaptive metrics for solver-guided lemma feedback.

All gates here are relative (log-gain, shares, in-problem percentiles).
They are meant to replace fixed absolute cutoffs such as CONJ_TOTAL > 20
so the same logic works on small Nat lemmas and large ADT/integer tasks.
"""

from __future__ import annotations

import math
from typing import Sequence


# ~20% increase in (1+x). High-volume counters (demod, inst, conj, clauses).
LOG_GAIN_MIN = math.log(1.20)
# Rare / low-count events (skolem, induction applications, eq-taut).
LOG_GAIN_MIN_RARE = math.log(1.10)
# Absolute noise floor as a fraction of the reference count (high-volume only).
NOISE_FRAC = 0.02
# Difficulty drop that counts as progress (in-problem relative).
DIFFICULTY_REL_DROP = 0.20
# Generated/instantiation volume growth treated as explosion without product.
EXPLOSION_LOG_GAIN = math.log(1.50)

# Vampire within-run mix (induction vs rewrite). One inequality per hint.
REWRITE_PER_INDUCTION_MAX = 8.0
INDUCTION_SHARE_MAX = 0.15
INTEGER_INDUCTION_SHARE_MIN = 0.70
# Superposition volume vs productive rewrite (demod + eq-taut).
SUPERPOSITION_PER_REWRITE_MIN = 8.0
# Vampire induction-depth wall (small integer, not a log-gain).
MAX_INDUCTION_DEPTH_HINT = 2
# Kept for routing docs / older call sites; mix hints no longer AND these.
INDUCTION_SHARE_MIN = 0.08
INDUCTION_PER_REWRITE_MAX = 0.02
REWRITE_SHARE_MIN = 0.85

# CVC5 within-run mix. One inequality per hint.
SKOLEM_PER_CONJ_MAX = 0.05
INST_OF_MATCHING_MAX = 0.75
CONJ_SHARE_MIN = 0.25
INST_PER_SKOLEM_MAX = 10.0
SKOLEM_SHARE_MIN = 0.01

# In-problem difficulty: keep assertions at/above this percentile of positive scores.
HARD_AXIOM_PERCENTILE = 0.50


def log_gain(candidate: float, reference: float) -> float:
    """Scale-free increment: log1p(cand) - log1p(ref)."""
    return math.log1p(max(float(candidate), 0.0)) - math.log1p(max(float(reference), 0.0))


def gate_overshoot(
    value: float,
    threshold: float,
    *,
    higher: bool = False,
) -> float:
    """How far ``value`` is past a mix gate, scaled into ``[0, 1]``.

    Lower-than-threshold gates (the usual mix hints): 0 on the line, 1 at 0.
    Higher-than-threshold gates (e.g. integer-induction share): 0 on the line,
    1 at 1.0. Used as a sampling weight when both prompt-mode families fire.
    """
    v = float(value)
    t = float(threshold)
    if higher:
        denom = max(1.0 - t, 1e-9)
        return min(1.0, max(0.0, (v - t) / denom))
    if t <= 0:
        return 1.0 if v <= 0 else 0.0
    return min(1.0, max(0.0, (t - v) / t))


def relative_increase(
    candidate: float,
    reference: float,
    *,
    kind: str = "rate",
) -> float:
    """(cand - ref) / denom.

    Counts use max(ref, 1) so a 0→1 bump is +100%. Rates use max(ref, ε)
    so 0.4/s → 0.9/s is not diluted by a count-sized floor of 1.
    """
    ref = float(reference)
    if kind == "count":
        denom = max(ref, 1.0)
    else:
        denom = max(ref, 1e-9)
    return (float(candidate) - ref) / denom


def activity_rate(count: float, elapsed_s: float, min_elapsed: float = 0.2) -> float:
    """Normalize a counter by diagnostic wall time."""
    return max(float(count), 0.0) / max(float(elapsed_s), min_elapsed)


def is_relative_gain(
    candidate: float,
    reference: float,
    *,
    rare: bool = False,
    kind: str = "rate",
) -> bool:
    """
    True if `candidate` is a meaningful increase over `reference`.

    High-volume: require ~20% log-gain and a 2%-of-reference noise floor.
    Counts also require a min-1 absolute floor (one extra event). Rates do
    not — 0.4/s → 0.9/s is a real gain.
    Rare events: skip the 2% floor so 0→1 can fire; still require ~10%
    log-gain so 100→101 does not.
    """
    cand = float(candidate)
    ref = float(reference)
    if cand <= ref:
        return False
    if not rare:
        rel_floor = NOISE_FRAC * max(ref, 0.0)
        floor = max(1.0, rel_floor) if kind == "count" else rel_floor
        if (cand - ref) <= floor:
            return False
        return log_gain(cand, ref) >= LOG_GAIN_MIN
    return log_gain(cand, ref) >= LOG_GAIN_MIN_RARE


def gain_score(candidate: float, reference: float, cap: float) -> float:
    """Map log-gain onto [0, cap]; a 2× increase contributes 1.0 before capping."""
    g = log_gain(candidate, reference)
    if g <= 0:
        return 0.0
    return min(g / math.log(2.0), cap)


def pct_label(candidate: float, reference: float, *, kind: str = "rate") -> int:
    """Integer percent for human-readable signal strings."""
    return int(round(100.0 * relative_increase(candidate, reference, kind=kind)))


def percentile(values: Sequence[float], q: float) -> float:
    """Linear-interpolated percentile; q in [0, 1]."""
    if not values:
        return 0.0
    xs = sorted(float(v) for v in values)
    if len(xs) == 1:
        return xs[0]
    q = min(1.0, max(0.0, q))
    idx = q * (len(xs) - 1)
    lo = int(math.floor(idx))
    hi = int(math.ceil(idx))
    if lo == hi:
        return xs[lo]
    w = idx - lo
    return xs[lo] * (1.0 - w) + xs[hi] * w


def in_problem_hard_cutoff(scores: Sequence[float], q: float = HARD_AXIOM_PERCENTILE) -> float:
    """
    Cutoff for 'hard' assertions *inside this problem*.

    Uses the percentile of strictly positive scores. A lone difficulty=1 axiom
    on a small task is therefore hard; a difficulty=3 axiom in the bottom
    quartile of a large task is not.
    """
    pos = [float(s) for s in scores if s > 0]
    if not pos:
        return float("inf")
    return percentile(pos, q)


def relative_drop(old: float, new: float) -> float:
    """(old - new) / old, clamped to [0, 1] when old > 0."""
    old_f = float(old)
    new_f = float(new)
    if new_f >= old_f:
        return 0.0
    if old_f <= 0:
        return 1.0
    return (old_f - new_f) / old_f


def is_relative_drop(old: float, new: float, min_rel: float = DIFFICULTY_REL_DROP) -> bool:
    return relative_drop(old, new) >= min_rel
