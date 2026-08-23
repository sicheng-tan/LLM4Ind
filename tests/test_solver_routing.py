#!/usr/bin/env python3
"""Tests for theory features and feedback-guided solver routing.

Run from repo root:

    python3 tests/test_solver_routing.py
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from solver_routing import (
    GoalSearchState,
    build_search_state,
    format_routing_for_prompt,
    order_prompt_strategies,
    profile_utility_from_stats,
    record_pair_attempt,
    recommend_cvc5_profiles,
    recommend_vampire_profiles,
    select_top_profiles,
)
from theory_features import analyze_smt


def _ok(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def test_analyze_adt_nat() -> None:
    path = ROOT / "benchmarks/preprocessed/ind-ben/nat/crafted_mul_comm/0/template.smt2"
    feats = analyze_smt(path)
    _ok(feats.has_adt, "mul_comm should be ADT")
    _ok(not feats.has_int, "mul_comm Nat is not SMT Int")
    _ok(feats.has_quantifiers, "mul_comm is quantified")
    _ok("UFDT" in feats.logic, f"logic={feats.logic}")


def test_analyze_mixed_lia() -> None:
    path = ROOT / "benchmarks/preprocessed/dtt/dtt-isa/goal1/template.smt2"
    feats = analyze_smt(path)
    _ok(feats.has_adt, "DTLIA still has datatypes")
    _ok(feats.has_int, "DTLIA uses Int")
    _ok(feats.mixed_adt_lia, "should be mixed ADT+LIA")


def test_vampire_static_routing() -> None:
    adt = analyze_smt("(set-logic UFDT)\n(declare-datatypes ((nat 0)) (((zero) (s (s0 nat)))))")
    ranked, reasons = recommend_vampire_profiles(adt)
    _ok(ranked[0] == "struct_induction", f"ADT first profile: {ranked}")
    _ok("induction_portfolio" in ranked, "paper fallback must remain")
    _ok(any("static:adt" in r for r in reasons), reasons)

    mixed = analyze_smt("(set-logic UFDTLIA)\n(declare-datatypes ((Lst 0)) (((nil))))\n(declare-fun f (Int) Int)")
    ranked_m, _ = recommend_vampire_profiles(mixed)
    _ok(ranked_m[0] in ("induction_portfolio", "smtcomp", "alasca_arith"), ranked_m)

    ranked_h, reasons_h = recommend_vampire_profiles(
        mixed, [{"kind": "need_arithmetic_lemma"}]
    )
    _ok(ranked_h[0] in ("alasca_arith", "integer_induction", "smtcomp"), ranked_h)
    _ok(any("need_arithmetic" in r for r in reasons_h), reasons_h)


def test_cvc5_static_and_hint_routing() -> None:
    adt = analyze_smt("(set-logic UFDT)\n(declare-datatypes ((nat 0)) (((zero))))")
    ranked, _ = recommend_cvc5_profiles(adt)
    _ok(ranked[0] == "adt_structural", ranked)

    ranked_e, reasons = recommend_cvc5_profiles(
        adt, [{"kind": "search_explosion"}]
    )
    _ok(ranked_e[0] in ("controlled_conjecture", "cvc5_inductive_no_ematching"), ranked_e)
    _ok(any("explosion" in r for r in reasons), reasons)

    for name in (
        "cvc5_simple",
        "cvc5_inductive",
        "cvc5_inductive_no_ematching",
        "cvc4_default",
    ):
        _ok(name in ranked_e, f"paper fallback missing {name}")


def test_prompt_reorder_keeps_all() -> None:
    strats = ["prove_prompt_equational_reasoning", "prove_prompt_term_rewrite"]
    out = order_prompt_strategies(strats, [{"kind": "need_stronger_lemma"}])
    _ok(out[0] == "prove_prompt_term_rewrite", out)
    _ok(set(out) == set(strats), "must not drop prompts")
    out2 = order_prompt_strategies(strats, [{"kind": "need_rewrite"}])
    _ok(out2[0] == "prove_prompt_equational_reasoning", out2)


def test_select_top_by_utility() -> None:
    ranked = ["struct_induction", "induction_portfolio", "alasca_arith"]
    top = select_top_profiles(ranked, {"induction_portfolio": 4.0, "struct_induction": 1.0, "alasca_arith": 0.2}, k=2)
    _ok(top[0] == "induction_portfolio", top)
    _ok(len(top) == 2, top)


def test_utility_explosion_penalty() -> None:
    score, signals = profile_utility_from_stats(
        backend="vampire",
        proved=False,
        status="timeout",
        stats={"Generated clauses": 8000, "InductionApplications": 0, "StructuralInduction": 0},
        elapsed=2.0,
    )
    _ok(any("explosion" in s for s in signals), signals)
    _ok(score < 0, score)

    proved, sig = profile_utility_from_stats(
        backend="cvc5", proved=True, status="unsat", stats={}, elapsed=0.4
    )
    _ok(proved == 100.0, proved)
    _ok("proved" in sig, sig)
    relative, relative_signals = profile_utility_from_stats(
        backend="vampire",
        proved=False,
        status="timeout",
        stats={"InductionApplications": 12, "Generated clauses": 20},
        elapsed=1.0,
        reference_stats={"InductionApplications": 2, "Generated clauses": 20},
        reference_elapsed=1.0,
    )
    _ok(relative > 0, relative)
    _ok(any("relative_induction" in s for s in relative_signals), relative_signals)


def test_search_state_prompt() -> None:
    feats = analyze_smt("(set-logic UFDT)\n(declare-datatypes ((nat 0)) (((zero))))")
    state = build_search_state("vampire", feats)
    txt = format_routing_for_prompt(state)
    _ok("recommended_profile=" in txt, txt)
    _ok("struct_induction" in txt, txt)
    _ok("constructor-aware" in txt.lower() or "structural" in txt.lower(), txt)


def test_pair_history_round_trip() -> None:
    state = GoalSearchState(
        backend="vampire",
        candidate_profiles=["struct_induction"],
        active_profile="struct_induction",
        active_prompt="prove_prompt_equational_reasoning",
    )
    record_pair_attempt(
        state,
        prompt_strategy="prove_prompt_equational_reasoning",
        profile="struct_induction",
        status="timeout",
        elapsed=1.2,
        signals=["induction_stuck"],
        fallback_used=False,
        winner_profile="induction_portfolio",
    )
    restored = GoalSearchState.from_dict(state.to_dict())
    _ok(len(restored.pair_history) == 1, restored)
    _ok(restored.pair_history[0]["profile"] == "struct_induction", restored)
    _ok(restored.pair_history[0]["winner_profile"] == "induction_portfolio", restored)


def test_failed_pair_has_no_winner() -> None:
    state = GoalSearchState(
        backend="cvc5",
        candidate_profiles=["cvc5_inductive"],
        active_profile="cvc5_inductive",
    )
    record_pair_attempt(
        state,
        prompt_strategy="prove_prompt_term_rewrite",
        profile="cvc5_inductive",
        status="timeout",
    )
    _ok(state.pair_history[0]["winner_profile"] == "", state)


def main() -> int:
    tests = [
        test_analyze_adt_nat,
        test_analyze_mixed_lia,
        test_vampire_static_routing,
        test_cvc5_static_and_hint_routing,
        test_prompt_reorder_keeps_all,
        test_select_top_by_utility,
        test_utility_explosion_penalty,
        test_search_state_prompt,
        test_pair_history_round_trip,
        test_failed_pair_has_no_winner,
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
