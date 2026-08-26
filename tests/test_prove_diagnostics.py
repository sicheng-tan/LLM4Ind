#!/usr/bin/env python3
"""Tests for first-prove diagnostics and subgoal cache reuse."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch
from contextlib import ExitStack


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from cvc5_runner import (
    CvcResult,
    _cvc_prove_cmd,
    _inject_difficulty_script,
    parse_cvc_difficulty,
    run_cvc_probe,
    cvc_probeable_profiles,
    cvc_profile_specs,
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


def test_progress_cache_reused_for_same_profile() -> None:
    import Mate_new as mate

    short = CvcResult(
        status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 8}, strategy="cvc5_inductive",
    )
    control = CvcResult(
        status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 7}, strategy="cvc5_inductive",
    )
    with tempfile.TemporaryDirectory() as tmp:
        state = mate.load_routing_state(tmp, "template")
        state.active_profile = "cvc5_inductive"
        mate.save_routing_state(tmp, "template", state)
        mate._store_cached_diag(tmp, "template", "baseline_diag_short", short)
        mate._store_cached_diag(tmp, "template", "control_diag", control)
        with patch("Mate_new.run_cvc_diagnostic") as diag:
            mate.analyze_lemma_progress([], TINY_SMT, Path(tmp), "template", tmp)
        diag.assert_not_called()


def test_progress_cache_invalidated_on_profile_change() -> None:
    import Mate_new as mate

    old = CvcResult(
        status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 8}, strategy="cvc5_inductive",
    )
    old_ctrl = CvcResult(
        status="timeout", elapsed=3.0, stats={"CONJ_TOTAL": 7}, strategy="cvc5_inductive",
    )
    long = CvcResult(status="timeout", elapsed=60.0, stats={"CONJ_TOTAL": 8000})
    with tempfile.TemporaryDirectory() as tmp:
        state = mate.load_routing_state(tmp, "template")
        state.active_profile = "adt_structural"
        mate.save_routing_state(tmp, "template", state)
        mate._store_cached_diag(tmp, "template", "baseline_diag", long)
        mate._store_cached_diag(tmp, "template", "baseline_diag_short", old)
        mate._store_cached_diag(tmp, "template", "control_diag", old_ctrl)

        def fake_diag(path, timeout=3, profile=None, **kwargs):
            name = profile or "adt_structural"
            stats = {"CONJ_TOTAL": 1 if "control" in str(path) else 2}
            return CvcResult(status="timeout", elapsed=3.0, stats=stats, strategy=name)

        with patch("Mate_new.run_cvc_diagnostic", side_effect=fake_diag) as diag:
            _ordered, hint_b = mate.analyze_lemma_progress(
                [], TINY_SMT, Path(tmp), "template", tmp
            )
        assert diag.call_count >= 2
        cached = mate._load_cached_diag(tmp, "template", "baseline_diag_short")
        assert cached is not None
        assert cached.strategy == "adt_structural"
        assert cached.stats["CONJ_TOTAL"] == 2
        assert hint_b.stats["CONJ_TOTAL"] == 8000
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


def _execute_strategy(call) -> str:
    if "strategy" in call.kwargs:
        return call.kwargs["strategy"]
    return call.args[2]


def test_cvc_probe_skips_cvc4() -> None:
    fake = CvcResult(status="timeout")
    with patch("cvc5_runner._execute_single", return_value=fake) as exe:
        with tempfile.TemporaryDirectory() as tmp:
            smt = Path(tmp) / "g.smt2"
            smt.write_text(TINY_SMT, encoding="utf-8")
            out = run_cvc_probe(smt, ["cvc4_default", "cvc5_inductive"], timeout=1)
    assert set(out) == {"cvc5_inductive"}
    assert exe.call_count == 1
    assert _execute_strategy(exe.call_args) == "cvc5_inductive"
    cmd = exe.call_args.args[0]
    assert "--stats" in cmd
    assert cmd[0] == cvc_profile_specs()["cvc5_inductive"]["binary"]


def test_cvc_probeable_fills_next_cvc5() -> None:
    ranked = [
        "adt_structural",
        "cvc4_default",
        "cvc5_inductive",
        "cvc5_inductive_no_ematching",
    ]
    assert cvc_probeable_profiles(ranked)[:3] == [
        "adt_structural",
        "cvc5_inductive",
        "cvc5_inductive_no_ematching",
    ]


def test_cvc_diagnostic_still_remaps_cvc4() -> None:
    fake = CvcResult(status="timeout")
    with patch("cvc5_runner._execute_single", return_value=fake) as exe:
        with tempfile.TemporaryDirectory() as tmp:
            smt = Path(tmp) / "g.smt2"
            smt.write_text(TINY_SMT, encoding="utf-8")
            from cvc5_runner import run_cvc_diagnostic

            run_cvc_diagnostic(
                smt, timeout=1, collect_difficulty=False, profile="cvc4_default"
            )
    assert exe.call_count == 1
    assert _execute_strategy(exe.call_args) == "cvc5_inductive"
    cmd = exe.call_args.args[0]
    assert cmd[0] == cvc_profile_specs()["cvc5_inductive"]["binary"]


def test_subgoal_hard_axioms_skip_proof_goal() -> None:
    import Mate_new as mate

    goal = "(not (forall ((x Int)) (P x)))"
    axiom = "(forall ((x Int)) (P x))"
    child = CvcResult(
        status="timeout",
        difficulty=[(goal, 20), (axiom, 10)],
        goal_term=goal,
        strategy="cvc5_inductive",
    )
    with tempfile.TemporaryDirectory() as tmp:
        mate._store_cached_diag(tmp, "template_1", "baseline_diag", child)
        mate._record_subgoal_failure_feedback(
            tmp, "template", "template_1", ["lemma-a"]
        )
        parent = mate.load_failed_lemmas(tmp, "template")
        failed = next(h for h in parent["repair_hints"] if h.get("kind") == "subgoal_failed")
        hard = failed.get("hard_axioms") or []
        assert axiom in hard
        assert goal not in hard


def test_repair_hints_keep_all_kinds() -> None:
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
        timeout = next(h for h in data["repair_hints"] if h["kind"] == "timeout")
        assert timeout["detail"] == "t2"
        assert "no_progress" in kinds
        assert "need_rewrite" in kinds
        assert "need_induction_lemma" in kinds
        assert "high_difficulty_assertions" in kinds


def test_subgoal_failed_keeps_latest_two() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        for name in ("template_1", "template_2", "template_3"):
            mate.add_repair_hints(tmp, "template", [{
                "kind": "subgoal_failed",
                "context": f"subgoal:{name}",
                "detail": name,
            }])
        data = mate.load_failed_lemmas(tmp, "template")
        failed = [h for h in data["repair_hints"] if h["kind"] == "subgoal_failed"]
        assert [h["detail"] for h in failed] == ["template_2", "template_3"]


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


def test_prove_run_does_not_retry_after_llm_exhausted() -> None:
    import Mate_new as mate
    import Mate_new_vampire as mate_v

    goal_smt = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(goal_smt, encoding="utf-8")
        with patch("Mate_new.routing_enabled", return_value=False), patch(
            "Mate_new.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new.quick_run", return_value=(False, [], [])
        ), patch("Mate_new.run_cvc_routed") as routed:
            assert mate.prove_run(tmp, "template") is False
            routed.assert_not_called()

        with patch("Mate_new_vampire.routing_enabled", return_value=False), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new_vampire.quick_run", return_value=(False, [], [])
        ), patch("Mate_new_vampire.run_vampire_routed") as routed_v:
            assert mate_v.prove_run(tmp, "template") is False
            routed_v.assert_not_called()


def test_two_no_help_switches_generation_prompt() -> None:
    import Mate_new as mate

    goal_smt = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""
    calls: list[str] = []

    def fake_quick_run(_base, _name, prompt_strategy, *_args, **_kwargs):
        n = len(calls)
        calls.append(prompt_strategy)
        if n == 0:
            return False, [], []
        if n == 1:
            return False, [], ["(forall ((x Int)) (P x))"]
        return False, [], []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(goal_smt, encoding="utf-8")
        with patch("Mate_new.routing_enabled", return_value=False), patch(
            "Mate_new.perform_initial_verification", return_value=False
        ), patch("Mate_new.quick_run", side_effect=fake_quick_run), patch.dict(
            mate.config, {"MAX_ATTEMPTS_PER_PROMPT": 3}
        ):
            assert mate.prove_run(tmp, "template") is False

    assert len(calls) == 6, calls
    assert calls[:2] == [
        "prove_prompt_equational_reasoning",
        "prove_prompt_equational_reasoning",
    ], calls
    assert calls[2:4] == [
        "prove_prompt_term_rewrite",
        "prove_prompt_term_rewrite",
    ], calls
    assert calls[4:] == [
        "prove_prompt_equational_reasoning",
        "prove_prompt_equational_reasoning",
    ], calls

    calls.clear()
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(goal_smt, encoding="utf-8")
        mate.add_repair_hints(
            tmp,
            "template",
            [{"kind": "need_stronger_lemma", "detail": "strengthen", "context": "goal"}],
        )
        with patch("Mate_new.routing_enabled", return_value=False), patch(
            "Mate_new.perform_initial_verification", return_value=False
        ), patch("Mate_new.quick_run", side_effect=fake_quick_run), patch.dict(
            mate.config, {"MAX_ATTEMPTS_PER_PROMPT": 3}
        ):
            assert mate.prove_run(tmp, "template") is False
    assert calls[0] == "prove_prompt_term_rewrite", calls
    assert calls[2] == "prove_prompt_equational_reasoning", calls


class _FixedRng:
    def __init__(self, x: float) -> None:
        self.x = x

    def random(self) -> float:
        return self.x


_PROMPT_GOAL_SMT = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""


def _collect_prove_prompts(
    module_name: str,
    quick_fn,
    *,
    hints=None,
    routing: bool = False,
    decision=None,
    select_rng=None,
    extra_patches=(),
) -> list[str]:
    import importlib
    from types import SimpleNamespace

    from solver_routing import select_generation_prompt as real_select

    mate = importlib.import_module(module_name)
    calls: list[str] = []

    def wrapped_quick(base_path, base_name, prompt_strategy, *args, **kwargs):
        calls.append(prompt_strategy)
        return quick_fn(
            len(calls) - 1, prompt_strategy, base_path=base_path, mate=mate
        )

    def wrapped_select(strategies, hint_list, *, rng=None):
        return real_select(strategies, hint_list, rng=select_rng)

    decision = decision or SimpleNamespace(
        prompt_strategy="prove_prompt_term_rewrite",
        profile="cvc5_inductive",
        source="relative",
    )
    patches = [
        patch(f"{module_name}.routing_enabled", return_value=routing),
        patch(f"{module_name}.perform_initial_verification", return_value=False),
        patch(f"{module_name}.seed_baseline_repair_hints"),
        patch(f"{module_name}.quick_run", side_effect=wrapped_quick),
        patch.dict(mate.config, {"MAX_ATTEMPTS_PER_PROMPT": 3}),
    ]
    if routing:
        patches.append(
            patch(
                f"{module_name}.select_attempt_action",
                return_value=(SimpleNamespace(), decision),
            )
        )
    if select_rng is not None:
        patches.append(patch(f"{module_name}.select_generation_prompt", wrapped_select))
    patches.extend(extra_patches)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_PROMPT_GOAL_SMT, encoding="utf-8")
        if hints:
            mate.add_repair_hints(tmp, "template", hints)
        with ExitStack() as stack:
            for p in patches:
                stack.enter_context(p)
            mate.prove_run(tmp, "template")
    return calls


def test_two_no_help_switches_on_vampire_loop() -> None:
    def quick(n, _prompt, **_kwargs):
        return False, [], []

    for module_name in ("Mate_new", "Mate_new_vampire"):
        calls = _collect_prove_prompts(module_name, quick)
        assert calls[:2] == [
            "prove_prompt_equational_reasoning",
            "prove_prompt_equational_reasoning",
        ], (module_name, calls)
        assert calls[2:4] == [
            "prove_prompt_term_rewrite",
            "prove_prompt_term_rewrite",
        ], (module_name, calls)


def test_routing_does_not_override_generation_prompt() -> None:
    from types import SimpleNamespace

    def quick(_n, _prompt, **_kwargs):
        return False, [], []

    hijack = SimpleNamespace(
        prompt_strategy="prove_prompt_term_rewrite",
        profile="cvc5_inductive",
        source="relative",
    )
    calls = _collect_prove_prompts(
        "Mate_new", quick, routing=True, decision=hijack
    )
    assert calls[0] == "prove_prompt_equational_reasoning", calls
    assert "prove_prompt_term_rewrite" not in calls[:2], calls


def test_prove_run_samples_when_both_kind_families() -> None:
    def quick(_n, _prompt, **_kwargs):
        return False, [], []

    hints = [
        {"kind": "need_stronger_lemma", "strength": 0.9, "detail": "g", "context": "goal"},
        {"kind": "need_rewrite", "strength": 0.1, "detail": "r", "context": "goal"},
    ]
    rewrite = _collect_prove_prompts(
        "Mate_new",
        quick,
        hints=hints,
        select_rng=_FixedRng(0.05),
    )
    assert rewrite[0] == "prove_prompt_term_rewrite", rewrite
    assert rewrite[1] == "prove_prompt_term_rewrite", rewrite
    equational = _collect_prove_prompts(
        "Mate_new",
        quick,
        hints=hints,
        select_rng=_FixedRng(0.95),
    )
    assert equational[0] == "prove_prompt_equational_reasoning", equational


def test_useful_subgoal_failure_resets_no_help_streak() -> None:
    def quick(n, _prompt, **_kwargs):
        if n == 0:
            return True, ["template_1"], ["(forall ((x Int)) (P x))"]
        return False, [], []

    calls = _collect_prove_prompts(
        "Mate_new",
        quick,
        extra_patches=(
            patch("Mate_new.prove_subgoals_parallel", return_value=False),
        ),
    )
    assert calls[0] == "prove_prompt_equational_reasoning", calls
    assert calls[1] == "prove_prompt_equational_reasoning", calls
    assert calls[2] == "prove_prompt_equational_reasoning", calls
    assert calls[3] == "prove_prompt_term_rewrite", calls


def test_timeout_breaks_no_help_streak() -> None:
    def quick(n, _prompt, **_kwargs):
        if n == 1:
            raise TimeoutError("attempt timeout")
        return False, [], []

    calls = _collect_prove_prompts("Mate_new", quick)
    assert calls[:4] == [
        "prove_prompt_equational_reasoning",
        "prove_prompt_equational_reasoning",
        "prove_prompt_equational_reasoning",
        "prove_prompt_equational_reasoning",
    ], calls
    assert calls[4] == "prove_prompt_term_rewrite", calls


def test_kind_feedback_switches_after_one_no_help() -> None:
    def quick(n, _prompt, **kwargs):
        if n == 0:
            kwargs["mate"].add_repair_hints(
                kwargs["base_path"],
                "template",
                [{"kind": "need_stronger_lemma", "detail": "g", "context": "goal"}],
            )
        return False, [], []

    calls = _collect_prove_prompts("Mate_new", quick)
    assert calls[0] == "prove_prompt_equational_reasoning", calls
    assert calls[1] == "prove_prompt_term_rewrite", calls


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


def test_proved_attempt_still_has_no_pair_utility() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        mate.record_solver_attempt(
            tmp,
            "template",
            prompt_strategy="prove_prompt",
            selected_profile="cvc5_inductive",
            result=CvcResult(
                status="unsat",
                proved=True,
                elapsed=0.2,
                strategy="cvc5_inductive",
                stats={"CONJ_TOTAL": 3},
            ),
        )
        last = mate.load_routing_state(tmp, "template").pair_history[-1]
        assert last["utility"] is None
        assert last["proved"] is True
        assert last["winner_profile"] == "cvc5_inductive"


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
    test_stats_without_reference_skip_utility()
    test_proved_attempt_still_has_no_pair_utility()
    test_progress_uses_3s_short_baseline()
    test_progress_cache_reused_for_same_profile()
    test_progress_cache_invalidated_on_profile_change()
    test_cvc_diagnostic_single_process()
    test_cvc_probe_skips_cvc4()
    test_cvc_probeable_fills_next_cvc5()
    test_cvc_diagnostic_still_remaps_cvc4()
    test_subgoal_hard_axioms_skip_proof_goal()
    test_repair_hints_keep_all_kinds()
    test_subgoal_failed_keeps_latest_two()
    test_blocking_lemma_only_and_unmatched_skips_unproved()
    test_trivial_implication_and_control_shape()
    test_progress_prompt_does_not_fight_useless_group()
    test_empty_llm_does_not_retry_immediately()
    test_prove_run_does_not_retry_after_llm_exhausted()
    test_two_no_help_switches_generation_prompt()
    test_two_no_help_switches_on_vampire_loop()
    test_routing_does_not_override_generation_prompt()
    test_prove_run_samples_when_both_kind_families()
    test_useful_subgoal_failure_resets_no_help_streak()
    test_timeout_breaks_no_help_streak()
    test_kind_feedback_switches_after_one_no_help()
    print("prove diagnostics tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
