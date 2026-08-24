#!/usr/bin/env python3
"""Tests for first-prove diagnostics and subgoal cache reuse."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from cvc5_runner import (
    CvcResult,
    _cvc_prove_cmd,
    _inject_difficulty_script,
    parse_cvc_difficulty,
)
from vampire_runner import VampireResult, _vampire_command


TINY_SMT = """(set-logic ALL)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 0)))
(check-sat)
"""


def test_inject_difficulty_script() -> None:
    script = _inject_difficulty_script(TINY_SMT)
    assert "(set-option :produce-difficulty true)" in script
    assert "(get-difficulty)" in script
    assert script.count("(check-sat)") == 1


def test_inject_difficulty_without_set_logic() -> None:
    smt = """(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 0)))
(check-sat)
"""
    script = _inject_difficulty_script(smt)
    assert script.splitlines()[0] == "(set-option :produce-difficulty true)"
    assert "(get-difficulty)" in script
    assert "(set-logic" not in script


def test_parse_cvc_difficulty_simple() -> None:
    text = "unsat\n(\n((P x) 10)\n((Q y) 3)\n)\n"
    items = parse_cvc_difficulty(text)
    scores = {term: score for term, score in items}
    assert scores.get("(P x)") == 10
    assert scores.get("(Q y)") == 3


def test_cvc_prove_cmd_adds_stats_and_tlimit() -> None:
    cfg = {"binary": "cvc5", "options": ["--lang", "smt2"], "type": "CVC5"}
    cmd = _cvc_prove_cmd(
        cfg,
        Path("goal.smt2"),
        60,
        collect_stats=True,
        collect_difficulty=True,
    )
    assert "--stats" in cmd
    assert "--tlimit-per=60000" in cmd
    assert cmd[-1] == "goal.smt2"

    cvc4 = {"binary": "cvc4", "options": [], "type": "CVC4"}
    cmd4 = _cvc_prove_cmd(
        cvc4, Path("goal.smt2"), 60, collect_stats=True, collect_difficulty=True
    )
    assert "--stats" not in cmd4


def test_vampire_command_show_induction() -> None:
    cmd = _vampire_command(
        "vampire",
        "induction_portfolio",
        60,
        collect_stats=True,
        collect_ucore=False,
        proof_file=None,
        show_induction=True,
    )
    assert cmd[cmd.index("--show_induction") + 1] == "on"

    ucore = _vampire_command(
        "vampire",
        "induction_portfolio",
        60,
        collect_stats=True,
        collect_ucore=True,
        proof_file=None,
        show_induction=True,
    )
    assert "--show_induction" not in ucore


def test_cvc_compact_roundtrip() -> None:
    import Mate_new as mate

    original = CvcResult(
        proved=False,
        status="timeout",
        elapsed=12.5,
        strategy="cvc5_inductive",
        stats={"CONJ_TOTAL": 8, "INST_TOTAL": 3},
        difficulty=[("(forall ((x Int)) (P x))", 11)],
    )
    restored = mate._cvc_diag_from_compact(mate._compact_cvc_diag(original))
    assert restored is not None
    assert restored.status == "timeout"
    assert restored.stats["CONJ_TOTAL"] == 8
    assert restored.difficulty[0][1] == 11


def test_initial_verify_caches_baseline_without_diagnostic() -> None:
    import Mate_new as mate

    failed = CvcResult(
        status="timeout",
        strategy="cvc5_inductive",
        stats={"CONJ_TOTAL": 5},
        difficulty=[("(P x)", 9)],
    )
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"SOLVER_ROUTING": "off"}, clear=False), patch(
            "Mate_new.run_cvc_routed", return_value=failed
        ) as routed, patch("Mate_new.run_cvc_diagnostic") as diag:
            ok = mate.perform_initial_verification(
                smt, base_path=tmp, goal_name="template"
            )
        assert ok is False
        routed.assert_called_once()
        kwargs = routed.call_args.kwargs
        assert kwargs.get("collect_stats") is True
        assert kwargs.get("collect_difficulty") is True
        diag.assert_not_called()
        cached = mate._load_cached_diag(tmp, "template", "baseline_diag")
        assert cached is not None
        assert cached.stats["CONJ_TOTAL"] == 5
        assert cached.difficulty[0][1] == 9


def test_seed_does_not_run_diagnostic() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(
            os.environ,
            {"SOLVER_ROUTING": "off", "SOLVER_ROUTING_PROBES": "off"},
            clear=False,
        ), patch("Mate_new.run_cvc_diagnostic") as diag:
            mate.seed_baseline_repair_hints(tmp, "template", smt)
        diag.assert_not_called()
        assert mate._load_cached_diag(tmp, "template", "baseline_diag") is None


def test_failed_prove_does_not_overwrite_baseline() -> None:
    import Mate_new as mate

    first = CvcResult(status="timeout", stats={"CONJ_TOTAL": 1}, strategy="a")
    second = CvcResult(status="unknown", stats={"CONJ_TOTAL": 99}, strategy="b")
    with tempfile.TemporaryDirectory() as tmp:
        mate._record_failed_prove_diagnostics(tmp, "template", first)
        mate._record_failed_prove_diagnostics(tmp, "template", second)
        cached = mate._load_cached_diag(tmp, "template", "baseline_diag")
        assert cached is not None
        assert cached.stats["CONJ_TOTAL"] == 1
        assert cached.strategy == "a"


def test_subgoal_reuses_child_cache() -> None:
    import Mate_new as mate

    child = CvcResult(
        status="timeout",
        stats={"INST_TOTAL": 2},
        difficulty=[("(hard)", 7)],
        strategy="cvc5_inductive",
    )
    with tempfile.TemporaryDirectory() as tmp:
        mate._store_cached_diag(tmp, "template_1", "baseline_diag", child)
        with patch("Mate_new.run_cvc_diagnostic") as diag:
            mate._record_subgoal_failure_feedback(
                tmp, "template", "template_1", ["(assert true)", "(assert false)"]
            )
        diag.assert_not_called()
        parent = mate.load_failed_lemmas(tmp, "template")
        kinds = [h.get("kind") for h in parent.get("repair_hints") or []]
        assert "subgoal_failed" in kinds
        assert parent["unproved_lemmas"][0]["lemma"] == "(assert true)"
        assert [r["lemma"] for r in parent["unproved_lemmas"]] == ["(assert true)"]


def test_subgoal_falls_back_when_cache_missing() -> None:
    import Mate_new as mate

    fallback = CvcResult(status="timeout", difficulty=[("(ax)", 4)])
    with tempfile.TemporaryDirectory() as tmp:
        child = Path(tmp) / "template_1.smt2"
        child.write_text(TINY_SMT, encoding="utf-8")
        with patch("Mate_new.run_cvc_diagnostic", return_value=fallback) as diag:
            mate._record_subgoal_failure_feedback(
                tmp, "template", "template_1", ["(assert false)"]
            )
        diag.assert_called_once()
        cached = mate._load_cached_diag(tmp, "template_1", "baseline_diag")
        assert cached is not None
        assert cached.difficulty[0][1] == 4


def test_vampire_compact_and_subgoal_cache() -> None:
    import Mate_new_vampire as mv

    original = VampireResult(
        status="timeout",
        stats={"InductionApplications": 6},
        induction_focus=["(P (succ x))"],
        strategy="induction_portfolio",
    )
    restored = mv._vampire_diag_from_compact(mv._compact_vampire_diag(original))
    assert restored is not None
    assert restored.induction_focus == ["(P (succ x))"]

    with tempfile.TemporaryDirectory() as tmp:
        mv._store_cached_diag(tmp, "template_1", "baseline_diag", original)
        with patch("Mate_new_vampire.run_vampire_diagnostic") as diag:
            mv._record_subgoal_failure_feedback(
                tmp, "template", "template_1", ["(assert true)", "(assert false)"]
            )
        diag.assert_not_called()
        parent = mv.load_failed_lemmas(tmp, "template")
        assert any(h.get("kind") == "subgoal_failed" for h in parent["repair_hints"])
        assert [r["lemma"] for r in parent["unproved_lemmas"]] == ["(assert true)"]


def test_empty_stats_skip_hint_and_utility() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        mate.record_solver_attempt(
            tmp,
            "template",
            prompt_strategy="prove_prompt",
            selected_profile="cvc5_inductive",
            result=CvcResult(status="timeout", elapsed=60.0, stats={}),
        )
        state = mate.load_routing_state(tmp, "template")
        assert state.pair_history
        last = state.pair_history[-1]
        assert last["utility"] is None
        assert last["signals"] == []


def test_progress_uses_3s_short_baseline() -> None:
    import Mate_new as mate

    long = CvcResult(
        status="timeout", elapsed=60.0,
        stats={"CONJ_TOTAL": 8000},
        difficulty=[("(ax)", 9)],
    )
    short = CvcResult(status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 8})
    control = CvcResult(status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 7})
    with tempfile.TemporaryDirectory() as tmp:
        mate._store_cached_diag(tmp, "template", "baseline_diag", long)

        def fake_diag(path, timeout=3, **kwargs):
            name = str(path)
            if "control" in name:
                return control
            return short

        with patch("Mate_new.run_cvc_diagnostic", side_effect=fake_diag):
            _ordered, hint_b = mate.analyze_lemma_progress(
                [], TINY_SMT, Path(tmp), "template", tmp
            )
        assert hint_b.stats["CONJ_TOTAL"] == 8000
        cached_short = mate._load_cached_diag(tmp, "template", "baseline_diag_short")
        assert cached_short is not None
        assert cached_short.stats["CONJ_TOTAL"] == 8
        still_long = mate._load_cached_diag(tmp, "template", "baseline_diag")
        assert still_long is not None
        assert still_long.stats["CONJ_TOTAL"] == 8000


def test_cvc_diagnostic_single_process() -> None:
    fake = CvcResult(status="timeout", stdout="unknown\n(\n)\n", stderr="")
    with patch("cvc5_runner.run_cvc_difficulty") as second, patch(
        "cvc5_runner._execute_single", return_value=fake
    ):
        with tempfile.TemporaryDirectory() as tmp:
            smt = Path(tmp) / "g.smt2"
            smt.write_text(TINY_SMT, encoding="utf-8")
            from cvc5_runner import run_cvc_diagnostic

            run_cvc_diagnostic(smt, timeout=1, collect_difficulty=True)
        second.assert_not_called()


def test_repair_hint_quota_keeps_structure() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        mate.add_repair_hints(tmp, "template", [
            {"kind": "high_difficulty_assertions", "detail": "hard"},
            {"kind": "need_rewrite", "detail": "mix"},
            {"kind": "need_induction_lemma", "detail": "ind"},
        ])
        mate.add_repair_hints(tmp, "template", [
            {"kind": "timeout", "detail": "t1", "context": "attempt"},
            {"kind": "no_progress", "detail": "np"},
            {"kind": "timeout", "detail": "t2", "context": "usefulness"},
        ])
        data = mate.load_failed_lemmas(tmp, "template")
        kinds = [h["kind"] for h in data["repair_hints"]]
        assert kinds.count("timeout") == 1
        assert "no_progress" in kinds
        assert "need_rewrite" in kinds
        assert "need_induction_lemma" in kinds
        assert "high_difficulty_assertions" not in kinds


def test_blocking_lemma_only_and_unmatched_skips_unproved() -> None:
    import Mate_new as mate

    child = CvcResult(status="timeout", difficulty=[("(hard)", 3)])
    with tempfile.TemporaryDirectory() as tmp:
        mate._store_cached_diag(tmp, "template_2", "baseline_diag", child)
        mate._record_subgoal_failure_feedback(
            tmp, "template", "template_2", ["lemma-a", "lemma-b"]
        )
        parent = mate.load_failed_lemmas(tmp, "template")
        assert [r["lemma"] for r in parent["unproved_lemmas"]] == ["lemma-b"]

        mate._store_cached_diag(tmp, "template_1_2", "baseline_diag", child)
        mate._record_subgoal_failure_feedback(
            tmp, "template", "template_1_2", ["lemma-a", "lemma-b"]
        )
        parent = mate.load_failed_lemmas(tmp, "template")
        assert [r["lemma"] for r in parent["unproved_lemmas"]] == ["lemma-b"]


def test_trivial_implication_and_control_shape() -> None:
    import Mate_new as mate

    assert mate._is_trivial_equational_lemma("(= x x)")
    assert mate._is_trivial_equational_lemma("(=> P P)")
    assert mate._is_trivial_equational_lemma("(forall ((x Nat)) (= x x))")
    assert not mate._is_trivial_equational_lemma(
        "(forall ((x Nat)) (= (plus x zero) x))"
    )
    kept = mate._progress_singleton_lemmas([
        "(=> P P)",
        "(forall ((n Nat)) (= (plus n zero) n))",
    ])
    assert kept == ["(forall ((n Nat)) (= (plus n zero) n))"]


def test_progress_prompt_does_not_fight_useless_group() -> None:
    import Mate_new as mate

    txt = mate.format_solver_feedback_for_prompt({
        "useless_lemma_groups": [{"lemmas": ["(L1)", "(L2)"], "status": "timeout"}],
        "progress_lemmas": [{"lemma": "(L1)", "score": 1.2, "signals": ["more_demodulations"]}],
        "repair_hints": [],
        "invalid_lemmas": [],
        "unproved_lemmas": [],
        "routing": {},
    })
    assert "GROUPS (combinations)" in txt
    assert "in_failed_group" in txt
    assert "NOT proof of usefulness" in txt


def test_empty_llm_does_not_retry_immediately() -> None:
    import Mate_new as mate

    goal_smt = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(goal_smt, encoding="utf-8")
        with patch("Mate_new.generate_lemmas_with_llm", return_value=[]), patch(
            "Mate_new.run_cvc_routed"
        ) as routed, patch("Mate_new.seed_baseline_repair_hints"):
            proved, _, _ = mate.quick_run(tmp, "template", "p", "./prompts_ours")
        assert proved is False
        routed.assert_not_called()


def test_stats_without_reference_skip_utility() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        mate.record_solver_attempt(
            tmp,
            "template",
            prompt_strategy="prove_prompt",
            selected_profile="cvc5_inductive",
            result=CvcResult(status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 99}),
        )
        last = mate.load_routing_state(tmp, "template").pair_history[-1]
        assert last["utility"] is None


def main() -> int:
    test_inject_difficulty_script()
    test_inject_difficulty_without_set_logic()
    test_parse_cvc_difficulty_simple()
    test_cvc_prove_cmd_adds_stats_and_tlimit()
    test_vampire_command_show_induction()
    test_cvc_compact_roundtrip()
    test_initial_verify_caches_baseline_without_diagnostic()
    test_seed_does_not_run_diagnostic()
    test_failed_prove_does_not_overwrite_baseline()
    test_subgoal_reuses_child_cache()
    test_subgoal_falls_back_when_cache_missing()
    test_vampire_compact_and_subgoal_cache()
    test_empty_stats_skip_hint_and_utility()
    test_progress_uses_3s_short_baseline()
    test_cvc_diagnostic_single_process()
    test_repair_hint_quota_keeps_structure()
    test_blocking_lemma_only_and_unmatched_skips_unproved()
    test_trivial_implication_and_control_shape()
    test_progress_prompt_does_not_fight_useless_group()
    test_empty_llm_does_not_retry_immediately()
    test_stats_without_reference_skip_utility()
    print("prove diagnostics tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
