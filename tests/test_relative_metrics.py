#!/usr/bin/env python3
"""Unit tests for scale-adaptive solver feedback metrics.

Run from repo root:

    python3 tests/test_relative_metrics.py
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from solver_relative_metrics import (
    activity_rate,
    in_problem_hard_cutoff,
    is_relative_drop,
    is_relative_gain,
    log_gain,
    percentile,
)
from cvc5_runner import CvcResult, compute_progress_score, derive_repair_hints
from vampire_runner import VampireResult, compute_progress_score as vampire_score
from vampire_runner import derive_repair_hints as vampire_hints


def _ok(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def test_log_gain_scale_free() -> None:
    # Same relative jump → same log-gain, regardless of scale.
    g_small = log_gain(12, 10)
    g_large = log_gain(12000, 10000)
    _ok(abs(g_small - math.log(13 / 11)) < 1e-9, "small log-gain")
    _ok(abs(g_large - math.log(12001 / 10001)) < 1e-9, "large log-gain")
    # 20% increase on a tiny counter is a gain; +40 on 10000 is not (~0.4%).
    _ok(is_relative_gain(15, 10), "small problem 10→15 should fire")
    _ok(not is_relative_gain(10040, 10000), "large problem +40 should not fire")


def test_rare_vs_volume() -> None:
    _ok(is_relative_gain(1, 0, rare=True), "0→1 skolem is meaningful")
    _ok(not is_relative_gain(101, 100, rare=True), "100→101 skolem is noise")
    _ok(
        not is_relative_gain(1.0, 0.0, rare=False, kind="count"),
        "high-volume count still wants a floor",
    )
    _ok(is_relative_gain(0.9, 0.4, kind="rate"), "rate 0.4→0.9 is a gain")
    _ok(
        not is_relative_gain(101, 100, kind="count"),
        "count 100→101 non-rare is not a gain",
    )


def test_difficulty_in_problem() -> None:
    _ok(in_problem_hard_cutoff([1]) == 1.0, "lone difficulty=1 is hard in-problem")
    _ok(in_problem_hard_cutoff([10, 10, 10, 2]) >= 2.0, "cutoff tracks this problem")
    # Bottom score of a high-range problem is not automatically hard.
    cut = in_problem_hard_cutoff([10, 9, 8, 2], q=0.5)
    _ok(cut > 2, f"median should exceed the bottom score, got {cut}")
    _ok(is_relative_drop(10, 4), "10→4 is a 60% drop")
    _ok(not is_relative_drop(10, 9), "10→9 is only 10%")
    _ok(is_relative_drop(3, 2), "3→2 is 33% and should count")


def test_percentile() -> None:
    _ok(percentile([1, 2, 3, 4], 0.5) == 2.5, "median of even list")
    _ok(percentile([4], 0.9) == 4.0, "single value")


def test_cvc_small_vs_large_progress() -> None:
    elapsed = 3.0
    small_base = CvcResult(
        status="timeout", elapsed=elapsed,
        stats={"CONJ_TOTAL": 8, "INST_TOTAL": 12, "QUANTIFIERS_SKOLEMIZE": 0, "DT_TOTAL": 4},
    )
    small_cand = CvcResult(
        status="timeout", elapsed=elapsed,
        stats={"CONJ_TOTAL": 8, "INST_TOTAL": 30, "QUANTIFIERS_SKOLEMIZE": 0, "DT_TOTAL": 4},
    )
    small_ctrl = CvcResult(
        status="timeout", elapsed=elapsed,
        stats={"CONJ_TOTAL": 8, "INST_TOTAL": 13, "QUANTIFIERS_SKOLEMIZE": 0, "DT_TOTAL": 4},
    )
    score, signals = compute_progress_score(small_base, small_cand, control=small_ctrl)
    _ok(any(s.startswith("more_instantiations") for s in signals), f"small inst gain: {signals}")
    _ok(score > 0, f"small inst score should be positive, got {score}")

    large_base = CvcResult(
        status="timeout", elapsed=elapsed,
        stats={"CONJ_TOTAL": 8000, "INST_TOTAL": 10000, "QUANTIFIERS_SKOLEMIZE": 40, "DT_TOTAL": 500},
    )
    large_cand = CvcResult(
        status="timeout", elapsed=elapsed,
        stats={"CONJ_TOTAL": 8040, "INST_TOTAL": 10040, "QUANTIFIERS_SKOLEMIZE": 41, "DT_TOTAL": 508},
    )
    large_ctrl = CvcResult(
        status="timeout", elapsed=elapsed,
        stats={"CONJ_TOTAL": 8010, "INST_TOTAL": 10020, "QUANTIFIERS_SKOLEMIZE": 40, "DT_TOTAL": 502},
    )
    score_l, signals_l = compute_progress_score(large_base, large_cand, control=large_ctrl)
    _ok(
        "more_instantiations" not in "".join(signals_l),
        f"large +40 inst should not fire, got {signals_l}",
    )
    _ok(score_l < 0.5, f"large tiny deltas should stay below progress threshold, got {score_l} {signals_l}")


def test_cvc_difficulty_relative() -> None:
    base = CvcResult(
        status="timeout", elapsed=3.0,
        stats={},
        difficulty=[("(forall ((n Nat)) (= (plus zero n) n))", 3)],
    )
    cand = CvcResult(
        status="timeout", elapsed=3.0,
        stats={},
        difficulty=[("(forall ((n Nat)) (= (plus zero n) n))", 2)],
    )
    score, signals = compute_progress_score(base, cand)
    _ok(any("axiom_difficulty_drop" in s for s in signals), f"relative 3→2 drop: {signals}")
    _ok(score > 0, f"difficulty drop score {score}")

    hints = derive_repair_hints(CvcResult(
        status="timeout", elapsed=3.0,
        difficulty=[
            ("(forall ((n Nat)) (= (plus (succ n) m) (succ (plus n m))))", 2),
            ("(forall ((n Nat)) (= (plus zero n) n))", 1),
        ],
    ))
    kinds = [h["kind"] for h in hints]
    _ok("high_difficulty_assertions" in kinds, f"difficulty=2 should be in-problem hard: {hints}")
    hard = hints[0].get("hard_axioms") or []
    _ok(any("succ" in ax for ax in hard), f"top axiom should be kept: {hard}")


def test_cvc_mix_hints_small_problem() -> None:
    # Original conj>=50 would miss this; relative mix should fire.
    hints = derive_repair_hints(CvcResult(
        status="timeout", elapsed=3.0,
        stats={"CONJ_TOTAL": 8, "QUANTIFIERS_SKOLEMIZE": 0, "INST_TOTAL": 2},
    ))
    _ok(
        any(h["kind"] == "need_stronger_lemma" for h in hints),
        f"small conj-heavy mix: {hints}",
    )

    hints_rw = derive_repair_hints(CvcResult(
        status="timeout", elapsed=3.0,
        stats={"CONJ_TOTAL": 2, "QUANTIFIERS_SKOLEMIZE": 4, "INST_TOTAL": 8},
    ))
    _ok(
        any(h["kind"] == "need_rewrite" for h in hints_rw),
        f"skolem with sparse inst: {hints_rw}",
    )


def test_vampire_small_vs_large() -> None:
    elapsed = 3.0
    small_b = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Fw demodulations": 20, "Bw demodulations": 0, "Fw demodulations to eq. taut.": 2,
               "InductionApplications": 1, "Generated clauses": 80, "Final passive clauses": 20},
    )
    small_c = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Fw demodulations": 45, "Bw demodulations": 0, "Fw demodulations to eq. taut.": 6,
               "InductionApplications": 1, "Generated clauses": 90, "Final passive clauses": 10},
    )
    small_k = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Fw demodulations": 22, "Bw demodulations": 0, "Fw demodulations to eq. taut.": 2,
               "InductionApplications": 1, "Generated clauses": 82, "Final passive clauses": 19},
    )
    score, signals = vampire_score(small_b, small_c, control=small_k)
    _ok(any(s.startswith("more_demodulations") for s in signals), f"small demod: {signals}")
    _ok("lower_passive_ratio" in signals, f"small gen=90 should still get focus signal: {signals}")

    large_b = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Fw demodulations": 10000, "Bw demodulations": 20, "Fw demodulations to eq. taut.": 80,
               "InductionApplications": 50, "Generated clauses": 40000, "Final passive clauses": 5000},
    )
    large_c = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Fw demodulations": 10080, "Bw demodulations": 20, "Fw demodulations to eq. taut.": 82,
               "InductionApplications": 52, "Generated clauses": 40100, "Final passive clauses": 4980},
    )
    score_l, signals_l = vampire_score(large_b, large_c, control=large_b)
    _ok(
        "more_demodulations" not in "".join(signals_l),
        f"large +80 demod should not fire: {signals_l}",
    )
    _ok(score_l < 0.5, f"large tiny deltas: {score_l} {signals_l}")


def test_vampire_explosion_and_mix() -> None:
    elapsed = 3.0
    base = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Generated clauses": 1000, "Final passive clauses": 200,
               "Fw demodulations": 50, "InductionApplications": 1},
    )
    boom = VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"Generated clauses": 8000, "Final passive clauses": 4000,
               "Fw demodulations": 55, "InductionApplications": 1},
    )
    score, signals = vampire_score(base, boom, control=base)
    _ok(any(s.startswith("search_explosion") for s in signals), f"explosion: {signals}")
    _ok(score <= 0, f"explosion should not look like progress: {score}")

    hints = vampire_hints(VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"InductionApplications": 4, "StructuralInduction": 2, "Fw demodulations": 8},
    ))
    _ok(
        any(h["kind"] == "need_rewrite" for h in hints),
        f"small induction-without-rewrite: {hints}",
    )

    hints_ind = vampire_hints(VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"InductionApplications": 1, "Fw demodulations": 400},
    ))
    _ok(
        any(h["kind"] == "need_induction_lemma" for h in hints_ind),
        f"rewrite-dominated mix: {hints_ind}",
    )

    hints_int = vampire_hints(VampireResult(
        status="timeout", elapsed=elapsed,
        stats={"IntegerInfiniteIntervalInduction": 80, "StructuralInduction": 2,
               "Fw demodulations": 30},
    ))
    _ok(
        any(h["kind"] == "need_arithmetic_lemma" for h in hints_int),
        f"integer-induction share: {hints_int}",
    )


def test_activity_rate() -> None:
    _ok(abs(activity_rate(90, 3.0) - 30.0) < 1e-9, "per-second")
    _ok(activity_rate(10, 0.0) > 0, "zero elapsed uses min window")


def main() -> int:
    tests = [
        test_log_gain_scale_free,
        test_rare_vs_volume,
        test_difficulty_in_problem,
        test_percentile,
        test_cvc_small_vs_large_progress,
        test_cvc_difficulty_relative,
        test_cvc_mix_hints_small_problem,
        test_vampire_small_vs_large,
        test_vampire_explosion_and_mix,
        test_activity_rate,
    ]
    failed = 0
    for fn in tests:
        try:
            fn()
            print(f"ok  {fn.__name__}")
        except Exception as e:
            failed += 1
            print(f"FAIL {fn.__name__}: {e}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
