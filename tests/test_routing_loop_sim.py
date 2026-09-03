#!/usr/bin/env python3
"""Fast simulation of the post-fix routing loop. No real solver, no LLM API.

Run from repo root:

    python3 tests/test_routing_loop_sim.py
"""

from __future__ import annotations

import os
import sys
import tempfile
import time
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")
os.environ.setdefault("SOLVER_ROUTING", "on")
os.environ.setdefault("SOLVER_ROUTING_DECIDER", "relative")
os.environ.setdefault("SOLVER_ROUTING_PROBES", "on")

from cvc5_runner import CvcResult, cvc_probeable_profiles
from solver_routing import recommend_cvc5_profiles
from theory_features import analyze_smt


FAKE_LLM = """
Here are candidate lemmas.
; Output begin
(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m))))
; Output end
"""

ADT_SMT = """(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun plus (Nat Nat) Nat)
(assert (forall ((n Nat)) (= (plus zero n) n)))
; proof goal
(assert (not (forall ((n Nat)) (= (plus n zero) n))))
; proof goal end
(check-sat)
"""

PROMPTS = [
    "prove_prompt_equational_reasoning",
    "prove_prompt_term_rewrite",
]


def _timeout(strategy: str = "adt_structural", **stats) -> CvcResult:
    return CvcResult(
        status="timeout",
        elapsed=0.01,
        strategy=strategy,
        stats=dict(stats) if stats else {"CONJ_TOTAL": 3},
    )


def _ok(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def test_parse_simulated_llm() -> None:
    import Mate_new as mate

    lemmas = mate.parse_llm_response(FAKE_LLM)
    _ok(len(lemmas) == 1, lemmas)
    _ok("succ" in lemmas[0] and "plus" in lemmas[0], lemmas[0])


def test_cvc4_not_in_probe_list() -> None:
    adt = analyze_smt(ADT_SMT)
    ranked, _ = recommend_cvc5_profiles(adt)
    names = cvc_probeable_profiles(ranked)[:3]
    _ok("cvc4_default" not in names, names)
    _ok("adt_structural" in names, names)


def _seeded_adt_node(tmp: str):
    import Mate_new as mate

    smt = Path(tmp) / "template.smt2"
    smt.write_text(ADT_SMT, encoding="utf-8")
    with patch.dict(
        os.environ, {"SOLVER_ROUTING_PROBES": "off"}, clear=False
    ):
        mate.seed_baseline_repair_hints(tmp, "template", smt)
    return mate


def test_select_try_next_after_no_progress() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        _seeded_adt_node(tmp)
        state = mate.load_routing_state(tmp, "template")
        current = state.active_profile
        _ok(current == "adt_structural", current)
        data = mate.load_failed_lemmas(tmp, "template")
        data["repair_hints"] = [{"kind": "no_progress", "detail": "sim"}]
        data["progress_routing_signals"] = ["no_measurable_progress"]
        mate.save_failed_lemmas(tmp, "template", data)
        state, decision = mate.select_attempt_action(tmp, "template", PROMPTS)
        _ok(decision.profile != current, decision)
        _ok("progress:try_next_profile" in state.routing_reasons, state.routing_reasons)


def test_select_keep_after_difficulty_drop() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        _seeded_adt_node(tmp)
        current = mate.load_routing_state(tmp, "template").active_profile
        data = mate.load_failed_lemmas(tmp, "template")
        data["repair_hints"] = [{"kind": "partial_progress", "detail": "sim"}]
        data["progress_routing_signals"] = ["goal_difficulty_drop"]
        data["progress_lemmas"] = [{
            "lemma": "(L)",
            "score": 1.2,
            "signals": ["goal_difficulty_drop(9->3,67%)"],
        }]
        mate.save_failed_lemmas(tmp, "template", data)
        state, decision = mate.select_attempt_action(tmp, "template", PROMPTS)
        _ok(decision.profile == current, decision)
        _ok("progress:keep_profile" in state.routing_reasons, state.routing_reasons)


def test_select_explosion_switches_profile() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        _seeded_adt_node(tmp)
        data = mate.load_failed_lemmas(tmp, "template")
        data["repair_hints"] = [{"kind": "no_progress", "detail": "sim"}]
        data["progress_routing_signals"] = ["search_explosion"]
        mate.save_failed_lemmas(tmp, "template", data)
        state, decision = mate.select_attempt_action(tmp, "template", PROMPTS)
        _ok(decision.profile == "controlled_conjecture", decision)
        _ok("progress:search_explosion" in state.routing_reasons, state.routing_reasons)


def test_quick_run_simulated_llm_and_3s_feedback() -> None:
    """One usefulness-failure attempt: canned LLM, mocked 1s/60s/3s solvers."""
    import Mate_new as mate

    lemmas = mate.parse_llm_response(FAKE_LLM)
    boom = _timeout(
        "adt_structural",
        CONJ_TOTAL=80,
        INST_TOTAL=2,
        QUANTIFIERS_SKOLEMIZE=0,
        DT_TOTAL=0,
    )
    quiet = _timeout(
        "adt_structural",
        CONJ_TOTAL=4,
        INST_TOTAL=1,
        QUANTIFIERS_SKOLEMIZE=0,
        DT_TOTAL=0,
    )

    def fake_diag(path, timeout=3, **kwargs):
        name = str(path)
        if "lemma" in name:
            return boom
        return quiet

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(ADT_SMT, encoding="utf-8")
        with patch.dict(
            os.environ,
            {"SOLVER_ROUTING": "on", "SOLVER_ROUTING_PROBES": "off", "FEEDBACK_PROGRESS": "on"},
            clear=False,
        ), patch(
            "Mate_new.generate_lemmas_with_llm", return_value=lemmas
        ), patch(
            "Mate_new.run_cvc", return_value=_timeout("cvc5_simple")
        ), patch(
            "Mate_new.run_cvc_routed", return_value=_timeout("adt_structural")
        ), patch(
            "Mate_new.run_cvc_diagnostic", side_effect=fake_diag
        ), patch("Mate_new.seed_baseline_repair_hints"):
            mate.save_routing_state(
                tmp,
                "template",
                mate.GoalSearchState(
                    backend="cvc5",
                    candidate_profiles=["adt_structural", "cvc5_inductive"],
                    active_profile="adt_structural",
                    fallback_profiles=[
                        "cvc5_simple",
                        "cvc5_inductive",
                        "cvc5_inductive_no_ematching",
                        "cvc4_default",
                    ],
                ),
            )
            proved, subgoals, extracted = mate.quick_run(
                tmp, "template", PROMPTS[0], "./prompts_ours",
                solver_profile="adt_structural",
            )
        _ok(proved is False, proved)
        _ok(subgoals == [], subgoals)
        _ok(extracted == lemmas, extracted)
        data = mate.load_failed_lemmas(tmp, "template")
        kinds = [h.get("kind") for h in data.get("repair_hints") or []]
        _ok("no_progress" in kinds or "partial_progress" in kinds, kinds)
        signals = data.get("progress_routing_signals") or []
        _ok("search_explosion" in signals, signals)
        pair = mate.load_routing_state(tmp, "template").pair_history[-1]
        _ok(pair["utility"] is None, pair)
        _ok(pair["proved"] is False, pair)
        state, decision = mate.select_attempt_action(tmp, "template", PROMPTS)
        _ok(decision.profile == "controlled_conjecture", decision)
        _ok("progress:search_explosion" in state.routing_reasons, state.routing_reasons)


def test_pair_history_skips_last_failed_without_utility() -> None:
    """History is only a repeat-avoidance list; utility is ignored."""
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        _seeded_adt_node(tmp)
        state = mate.load_routing_state(tmp, "template")
        mate.save_routing_state(
            tmp,
            "template",
            mate.record_pair_attempt(
                state,
                prompt_strategy=PROMPTS[0],
                profile=state.active_profile,
                status="timeout",
                proved=False,
                utility=None,
            ),
        )
        _state, decision = mate.select_attempt_action(tmp, "template", PROMPTS)
        _ok(
            (decision.prompt_strategy, decision.profile)
            != (PROMPTS[0], state.active_profile),
            decision,
        )


def test_real_cvc5_trivial_unsat_under_2s() -> None:
    """Live cvc5 smoke: timeout 2s, trivial unsat. Skips if the binary is missing."""
    from cvc5_runner import _cvc5_binary, run_cvc

    binary = Path(_cvc5_binary())
    if not binary.is_file():
        print("skip test_real_cvc5_trivial_unsat_under_2s: no cvc5 binary")
        return
    if not os.access(binary, os.X_OK):
        os.chmod(binary, 0o755)
    smt = """(set-logic ALL)
(assert false)
(check-sat)
"""
    t0 = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "false.smt2"
        path.write_text(smt, encoding="utf-8")
        result = run_cvc(path, timeout=2, profiles=["cvc5_simple"])
    elapsed = time.time() - t0
    _ok(elapsed <= 2.0, f"real cvc5 exceeded 2s: {elapsed:.2f}s")
    _ok(result.proved and result.status == "unsat", result)
    _ok(result.strategy == "cvc5_simple", result.strategy)


def main() -> int:
    tests = [
        test_parse_simulated_llm,
        test_cvc4_not_in_probe_list,
        test_select_try_next_after_no_progress,
        test_select_keep_after_difficulty_drop,
        test_select_explosion_switches_profile,
        test_quick_run_simulated_llm_and_3s_feedback,
        test_pair_history_skips_last_failed_without_utility,
        test_real_cvc5_trivial_unsat_under_2s,
    ]
    failed = 0
    t0 = time.time()
    for fn in tests:
        try:
            fn()
            print(f"ok  {fn.__name__}")
        except Exception as exc:
            failed += 1
            print(f"FAIL {fn.__name__}: {exc}")
    elapsed = time.time() - t0
    print(f"{len(tests) - failed}/{len(tests)} passed in {elapsed:.2f}s")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
