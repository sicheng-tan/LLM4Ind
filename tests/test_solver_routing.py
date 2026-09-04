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
    apply_progress_routing,
    build_search_state,
    collect_feedback_signal_kinds,
    format_routing_for_prompt,
    order_prompt_strategies,
    select_generation_prompt,
    advance_generation_prompt,
    term_rewrite_sample_prob,
    retarget_generation_prompt,
    prompt_kind_signature,
    prompt_family_scores,
    reset_prompt_mode_rng,
    EQUATIONAL_PROMPT,
    TERM_REWRITE_PROMPT,
    NO_HELP_PROMPT_SWITCH,
    profile_utility_from_stats,
    rank_profiles_for_attempt,
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
    _ok(out[0] == "prove_prompt_equational_reasoning", out)
    _ok(set(out) == set(strats), "must not drop prompts")
    out2 = order_prompt_strategies(strats, [{"kind": "need_rewrite"}])
    _ok(out2[0] == "prove_prompt_term_rewrite", out2)
    both = order_prompt_strategies(
        strats,
        [{"kind": "need_stronger_lemma"}, {"kind": "need_rewrite"}],
    )
    _ok(both == strats, f"both families keep paper order for sampling: {both}")


def test_generation_prompt_start_and_switch() -> None:
    strats = ["prove_prompt_equational_reasoning", "prove_prompt_term_rewrite"]
    _ok(
        select_generation_prompt(strats, []) == "prove_prompt_equational_reasoning",
        "no hints keep paper order",
    )
    _ok(
        select_generation_prompt(strats, [{"kind": "need_stronger_lemma"}])
        == "prove_prompt_equational_reasoning",
        "stronger/generalize hints start on equational",
    )
    _ok(
        select_generation_prompt(strats, [{"kind": "need_rewrite"}])
        == "prove_prompt_term_rewrite",
        "rewrite hints start on term rewrite",
    )

    cur, n, switched = advance_generation_prompt(
        strats, "prove_prompt_equational_reasoning", 1
    )
    _ok(cur == "prove_prompt_equational_reasoning" and n == 1 and not switched, (cur, n, switched))
    cur, n, switched = advance_generation_prompt(
        strats, "prove_prompt_equational_reasoning", NO_HELP_PROMPT_SWITCH
    )
    _ok(switched and n == 0 and cur == "prove_prompt_term_rewrite", (cur, n, switched))
    cur, n, switched = advance_generation_prompt(
        strats, "prove_prompt_term_rewrite", NO_HELP_PROMPT_SWITCH
    )
    _ok(switched and n == 0 and cur == "prove_prompt_equational_reasoning", (cur, n, switched))

    cur, n, switched = advance_generation_prompt(["prompt_naive"], "prompt_naive", 2)
    _ok(not switched and cur == "prompt_naive", (cur, n, switched))


def test_both_kind_families_sample_by_overshoot() -> None:
    strats = ["prove_prompt_equational_reasoning", "prove_prompt_term_rewrite"]
    _ok(term_rewrite_sample_prob([{"kind": "need_rewrite", "strength": 0.4}]) is None, "one family")
    hints = [
        {"kind": "need_stronger_lemma", "strength": 0.9},
        {"kind": "need_rewrite", "strength": 0.1},
    ]
    p = term_rewrite_sample_prob(hints)
    _ok(p is not None and abs(p - 0.1) < 1e-9, p)

    class _Fixed:
        def __init__(self, x: float) -> None:
            self.x = x

        def random(self) -> float:
            return self.x

    _ok(
        select_generation_prompt(strats, hints, rng=_Fixed(0.05))
        == "prove_prompt_term_rewrite",
        "u < p picks rewrite template (term_rewrite)",
    )
    _ok(
        select_generation_prompt(strats, hints, rng=_Fixed(0.95))
        == "prove_prompt_equational_reasoning",
        "u >= p picks generalize template (equational)",
    )
    _ok(
        select_generation_prompt(
            strats, [{"kind": "need_rewrite", "strength": 0.1}], rng=_Fixed(0.0)
        )
        == "prove_prompt_term_rewrite",
        "single family stays deterministic",
    )


def test_family_scores_floor_legacy_and_sum() -> None:
    rewrite, generalize = prompt_family_scores(
        [{"kind": "need_rewrite", "strength": 0.0}]
    )
    _ok(abs(rewrite - 0.05) < 1e-9 and generalize == 0.0, (rewrite, generalize))

    rewrite, generalize = prompt_family_scores(
        [{"kind": "need_rewrite"}, {"kind": "need_stronger_lemma"}]
    )
    _ok(abs(rewrite - 1.0) < 1e-9 and abs(generalize - 1.0) < 1e-9, (rewrite, generalize))
    p = term_rewrite_sample_prob(
        [{"kind": "need_rewrite"}, {"kind": "need_stronger_lemma"}]
    )
    _ok(p is not None and abs(p - 0.5) < 1e-9, p)

    rewrite, generalize = prompt_family_scores([
        {"kind": "need_rewrite", "strength": 0.4},
        {"kind": "induction_stuck", "strength": 0.5},
        {"kind": "need_induction_lemma", "strength": 0.2},
    ])
    _ok(abs(rewrite - 0.9) < 1e-9, rewrite)
    _ok(abs(generalize - 0.2) < 1e-9, generalize)
    p = term_rewrite_sample_prob([
        {"kind": "need_rewrite", "strength": 0.4},
        {"kind": "induction_stuck", "strength": 0.5},
        {"kind": "need_induction_lemma", "strength": 0.2},
    ])
    _ok(p is not None and abs(p - 0.9 / 1.1) < 1e-9, p)

    rewrite, generalize = prompt_family_scores([
        {"kind": "need_directed_rewrite", "strength": 0.3},
        {"kind": "induction_depth_limit", "strength": 0.5},
    ])
    _ok(abs(rewrite - 0.3) < 1e-9 and abs(generalize - 0.5) < 1e-9, (rewrite, generalize))


def test_kind_signature_change_retargets_before_streak() -> None:
    strats = [EQUATIONAL_PROMPT, TERM_REWRITE_PROMPT]
    _ok(prompt_kind_signature([]) == "none", "empty")
    nxt, n, sig, why = retarget_generation_prompt(
        strats,
        [{"kind": "need_stronger_lemma"}],
        EQUATIONAL_PROMPT,
        1,
        "none",
    )
    _ok(why == "keep" and nxt == EQUATIONAL_PROMPT and n == 1 and sig == "generalize", (nxt, n, sig, why))

    nxt, n, sig, why = retarget_generation_prompt(
        strats,
        [{"kind": "need_rewrite"}],
        EQUATIONAL_PROMPT,
        1,
        "none",
    )
    _ok(why == "kind" and nxt == TERM_REWRITE_PROMPT and n == 0 and sig == "rewrite", (nxt, n, sig, why))

    nxt, n, sig, why = retarget_generation_prompt(
        strats,
        [{"kind": "need_stronger_lemma"}],
        EQUATIONAL_PROMPT,
        1,
        "generalize",
    )
    _ok(why == "keep" and n == 1 and nxt == EQUATIONAL_PROMPT, (nxt, n, why))

    nxt, n, sig, why = retarget_generation_prompt(
        strats,
        [{"kind": "need_stronger_lemma"}],
        EQUATIONAL_PROMPT,
        2,
        "generalize",
    )
    _ok(why == "consecutive" and nxt == TERM_REWRITE_PROMPT and n == 0, (nxt, n, why))


def test_prompt_mode_seed_replays_first_draw() -> None:
    import os

    strats = [EQUATIONAL_PROMPT, TERM_REWRITE_PROMPT]
    hints = [
        {"kind": "need_stronger_lemma", "strength": 0.6},
        {"kind": "need_rewrite", "strength": 0.4},
    ]
    reset_prompt_mode_rng()
    os.environ["PROMPT_MODE_SEED"] = "17"
    try:
        first = select_generation_prompt(strats, hints)
        second = select_generation_prompt(strats, hints)
        reset_prompt_mode_rng()
        replay = select_generation_prompt(strats, hints)
        _ok(first == replay, (first, replay))
        _ok(first in strats and second in strats, (first, second))
    finally:
        os.environ.pop("PROMPT_MODE_SEED", None)
        reset_prompt_mode_rng()


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
    _ok("search_explosion" not in "".join(signals), signals)
    _ok("status_only" in signals, signals)
    _ok(abs(score + 0.1) < 1e-9, score)

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

    boom, boom_sig = profile_utility_from_stats(
        backend="vampire",
        proved=False,
        status="timeout",
        stats={"Generated clauses": 8000, "InductionApplications": 0},
        elapsed=2.0,
        reference_stats={"Generated clauses": 100, "InductionApplications": 0},
        reference_elapsed=2.0,
    )
    _ok(any("explosion" in s for s in boom_sig), boom_sig)
    _ok(boom < 0, boom)


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


def test_progress_routing_keep_switch_next() -> None:
    adt = analyze_smt("(set-logic UFDT)\n(declare-datatypes ((nat 0)) (((zero))))")
    ranked, _ = recommend_cvc5_profiles(adt)
    kept, reasons = apply_progress_routing(
        "cvc5",
        ranked,
        ["goal_difficulty_drop", "partial_progress"],
        current_profile="cvc5_inductive",
    )
    _ok(kept[0] == "cvc5_inductive", kept)
    _ok("progress:keep_profile" in reasons, reasons)

    rotated, reasons_n = apply_progress_routing(
        "cvc5",
        ranked,
        ["no_progress", "no_measurable_progress"],
        current_profile="adt_structural",
    )
    _ok(rotated[0] != "adt_structural", rotated)
    _ok(rotated[-1] == "adt_structural", rotated)
    _ok("progress:try_next_profile" in reasons_n, reasons_n)

    exploded, reasons_e = apply_progress_routing(
        "cvc5",
        ranked,
        ["search_explosion"],
        current_profile="adt_structural",
    )
    _ok(exploded[0] == "controlled_conjecture", exploded)
    _ok("progress:search_explosion" in reasons_e, reasons_e)

    v_ranked, _ = recommend_vampire_profiles(adt)
    v_keep, v_reasons = apply_progress_routing(
        "vampire",
        v_ranked,
        ["more_induction_activity"],
        current_profile="induction_portfolio",
    )
    _ok(v_keep[0] == "induction_portfolio", v_keep)
    _ok("progress:keep_profile" in v_reasons, v_reasons)

    kinds = collect_feedback_signal_kinds(
        extra=["search_explosion(+80%)", "goal_difficulty_drop(8->2,75%)"]
    )
    _ok(kinds == ["search_explosion", "goal_difficulty_drop"], kinds)


def test_lemma_feedback_overrides_probe_utility() -> None:
    adt = analyze_smt("(set-logic UFDT)\n(declare-datatypes ((nat 0)) (((zero))))")
    _ranked, candidates, reasons = rank_profiles_for_attempt(
        "cvc5",
        adt,
        [{"kind": "no_progress"}],
        current_profile="adt_structural",
        extra_signals=["no_measurable_progress"],
        probe_utilities={"adt_structural": 9.0, "cvc5_inductive": 0.1},
    )
    _ok(candidates[0] != "adt_structural", candidates)
    _ok("progress:try_next_profile" in reasons, reasons)


def main() -> int:
    tests = [
        test_analyze_adt_nat,
        test_analyze_mixed_lia,
        test_vampire_static_routing,
        test_cvc5_static_and_hint_routing,
        test_prompt_reorder_keeps_all,
        test_generation_prompt_start_and_switch,
        test_both_kind_families_sample_by_overshoot,
        test_family_scores_floor_legacy_and_sum,
        test_kind_signature_change_retargets_before_streak,
        test_prompt_mode_seed_replays_first_draw,
        test_select_top_by_utility,
        test_utility_explosion_penalty,
        test_search_state_prompt,
        test_pair_history_round_trip,
        test_failed_pair_has_no_winner,
        test_progress_routing_keep_switch_next,
        test_lemma_feedback_overrides_probe_utility,
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
