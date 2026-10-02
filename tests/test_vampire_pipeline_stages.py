"""Vampire pipeline stage unit tests (excluding counterexample/model paths).

Covers gaps vs CVC twins: preprocess glue, initial baseline + library
materialize, profiler create_prompt, root finish, harvest skip_initial
forwarding, scheme glue on quick_run, parse_vampire_stats, fast-unsat harvest.
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from induction_scheme.constants import VAMPIRE_PROVE_PROFILES
from obligation_tree import HARVEST_VAMPIRE_PROFILES, add_proved_lemma, save_lemma_library
from vampire_runner import (
    VampireResult,
    parse_vampire_stats,
    prepare_vampire_smt_input,
)


TINY_SMT = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""

_SAMPLE_SMT = """(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Nat) (tail Lst)))))
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Nat) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (xs Lst)) (= (len (cons x xs)) (succ (len xs)))))
; proof goal
(assert (not (forall ((xs Lst)) (= (len (append xs nil)) (len xs)))))
; proof goal end
(check-sat)
"""

_GOAL = "(forall ((xs Lst)) (= (len (append xs nil)) (len xs)))"
_LEMMA = "(forall ((y Int)) (=> (P y) (P y)))"


def test_prepare_vampire_smt_input_rewrites_and_flag_off() -> None:
    snip = "(assert (is-Cons x))\n(check-sat)\n"
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "g.smt2"
        src.write_text(snip, encoding="utf-8")
        with patch.dict(os.environ, {"VAMPIRE_REWRITE_TESTERS": "on"}):
            run_path, tmp_path = prepare_vampire_smt_input(src)
        assert tmp_path is not None
        assert run_path != src
        text = run_path.read_text(encoding="utf-8")
        assert "((_ is Cons) x)" in text
        assert "(is-Cons x)" not in text
        tmp_path.unlink(missing_ok=True)

        with patch.dict(os.environ, {"VAMPIRE_REWRITE_TESTERS": "off"}):
            run_path2, tmp_path2 = prepare_vampire_smt_input(src)
        assert run_path2 == src
        assert tmp_path2 is None


def test_parse_vampire_stats_common_keys() -> None:
    text = """
% ------------------------------
Generated clauses: 42
Final active clauses: 3
StructuralInduction: 2
InductionApplications: 5
IntegerInfiniteIntervalInduction: 1
MaxInductionDepth: 4
Fw demodulations: 9
% ------------------------------
Generated clauses: 100
StructuralInduction: 7
"""
    stats = parse_vampire_stats(text)
    assert stats["Generated clauses"] == 100
    assert stats["StructuralInduction"] == 7
    assert stats["InductionApplications"] == 5
    assert stats["IntegerInfiniteIntervalInduction"] == 1
    assert stats["MaxInductionDepth"] == 4
    assert stats["Fw demodulations"] == 9
    assert parse_vampire_stats("") == {}
    assert parse_vampire_stats("no stats here") == {}


def test_vampire_perform_initial_caches_baseline() -> None:
    import Mate_new_vampire as mate

    failed = VampireResult(
        status="timeout",
        strategy="struct_induction",
        stats={"Generated clauses": 5},
        induction_focus=["(P x)"],
        elapsed=60.0,
    )
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"SOLVER_ROUTING": "off"}, clear=False), patch(
            "Mate_new_vampire.run_vampire_routed", return_value=failed
        ) as routed, patch("Mate_new_vampire.run_vampire_diagnostic") as diag:
            ok = mate.perform_initial_verification(
                smt, base_path=tmp, goal_name="template"
            )
        assert ok is False
        routed.assert_called_once()
        kwargs = routed.call_args.kwargs
        assert kwargs.get("collect_stats") is True
        assert kwargs.get("show_induction") is True
        diag.assert_not_called()
        cached = mate._load_cached_diag(tmp, "template", "baseline_diag")
        assert cached is not None
        assert cached.stats["Generated clauses"] == 5
        assert cached.induction_focus == ["(P x)"]


def test_vampire_perform_initial_skips_artifacts_when_feedback_off() -> None:
    import Mate_new_vampire as mate

    failed = VampireResult(status="timeout", proved=False, elapsed=1.0)
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "FEEDBACK_REPAIR_HINTS": "off",
            "FEEDBACK_PROGRESS": "off",
        }, clear=False), patch(
            "Mate_new_vampire.run_vampire_routed", return_value=failed
        ) as routed:
            ok = mate.perform_initial_verification(
                smt, base_path=tmp, goal_name="template"
            )
        assert ok is False
        kwargs = routed.call_args.kwargs
        assert kwargs.get("collect_stats") is False
        assert kwargs.get("show_induction") is False


def test_vampire_perform_initial_materializes_library() -> None:
    import Mate_new_vampire as mate

    failed = VampireResult(status="timeout", proved=False, elapsed=0.1)
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text(TINY_SMT, encoding="utf-8")
        add_proved_lemma(tmp, "(forall ((x Int)) true)", origin="lib", role="pin")
        mat = Path(tmp) / "template.__lib.smt2"
        mat.write_text(TINY_SMT + "\n; lib\n", encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY": "on",
        }), patch(
            "Mate_new_vampire.materialize_smt_with_library", return_value=mat
        ) as materialize, patch(
            "Mate_new_vampire.run_vampire_routed", return_value=failed
        ) as routed:
            mate.perform_initial_verification(
                smt, base_path=tmp, goal_name="template"
            )
        materialize.assert_called_once()
        assert routed.call_args[0][0] == mat


def test_vampire_failed_prove_does_not_overwrite_baseline() -> None:
    import Mate_new_vampire as mate

    first = VampireResult(status="timeout", stats={"Generated clauses": 1}, strategy="a")
    second = VampireResult(status="unknown", stats={"Generated clauses": 99}, strategy="b")
    with tempfile.TemporaryDirectory() as tmp:
        mate._set_goal_only_baseline(
            tmp, "template", first, context="initial_goal", replace=False
        )
        mate._set_goal_only_baseline(
            tmp, "template", second, context="initial_goal", replace=False
        )
        cached = mate._load_cached_diag(tmp, "template", "baseline_diag")
        assert cached is not None
        assert cached.stats["Generated clauses"] == 1
        assert cached.strategy == "a"


def test_vampire_create_prompt_injects_profiler() -> None:
    import Mate_new_vampire as mate

    prompts = ROOT / "prompts_ours" / "prove_prompt_equational_reasoning"
    if not prompts.exists():
        return
    with tempfile.TemporaryDirectory() as tmp:
        save_lemma_library(
            tmp,
            [{"id": "lib_1", "formula": "(= (len nil) zero)"}],
        )
        with patch.dict(os.environ, {
            "PROBLEM_PROFILER": "on",
            "PROBLEM_PROFILER_MIN_ATTEMPT": "1",
            "PROBLEM_PROFILER_TRIGGER": "always",
            "ANCESTOR_PROMPT": "off",
            "LEMMA_LIBRARY": "on",
            "INDUCTION_SCHEME": "off",
        }):
            messages, failed = mate.create_prompt(
                _SAMPLE_SMT,
                "prove_prompt_equational_reasoning",
                tmp,
                "template",
                str(prompts.parent),
                depth=0,
                current_formula=_GOAL,
            )
        assert "PROBLEM STRUCTURE" in failed
        assert "PROBLEM STRUCTURE" in messages[1]["content"]
    with patch.dict(os.environ, {
        "PROBLEM_PROFILER": "off",
        "ANCESTOR_PROMPT": "off",
        "INDUCTION_SCHEME": "off",
    }):
        with tempfile.TemporaryDirectory() as tmp:
            _messages, failed = mate.create_prompt(
                _SAMPLE_SMT,
                "prove_prompt_equational_reasoning",
                tmp,
                "template",
                str(prompts.parent),
                depth=0,
            )
        assert "PROBLEM STRUCTURE" not in failed


def test_vampire_maybe_root_finish_skips_depth_and_disabled() -> None:
    import Mate_new_vampire as mate

    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "120"}), patch.object(
            mate, "perform_initial_verification",
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=1) is False
            verify.assert_not_called()

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "off"}), patch.object(
            mate, "perform_initial_verification",
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=0) is False
            verify.assert_not_called()


def test_vampire_maybe_root_finish_runs_and_caps_budget() -> None:
    import Mate_new_vampire as mate

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "120"}), patch(
            "Mate_new_vampire.remaining_task_s", return_value=500.0,
        ), patch.object(
            mate, "perform_initial_verification", return_value=True,
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=0) is True
            assert verify.call_args.kwargs["log_event"] == "root_finish_prove"
            assert verify.call_args.kwargs["timeout"] == 120

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "120"}), patch(
            "Mate_new_vampire.remaining_task_s", return_value=45.0,
        ), patch.object(
            mate, "perform_initial_verification", return_value=False,
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=0) is False
            assert verify.call_args.kwargs["timeout"] == 45


def test_vampire_prove_subgoals_forwards_skip_initial_diag() -> None:
    import Mate_new_vampire as mate

    calls = []

    def fake_prove_run(*args, **kwargs):
        calls.append({"args": args, "kwargs": kwargs})
        return True

    diag = {"status": "timeout", "proved": False, "stats": {"Generated clauses": 3}}
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "child.smt2").write_text(TINY_SMT, encoding="utf-8")
        with patch("Mate_new_vampire.prove_run", side_effect=fake_prove_run):
            ok, _nodes = mate.prove_subgoals_parallel(
                tmp,
                ["child"],
                depth=0,
                skip_initial_for={"child"},
                skip_initial_diag={"child": diag},
            )
        assert ok is True
        assert len(calls) == 1
        assert calls[0]["kwargs"].get("skip_initial") is True
        assert calls[0]["kwargs"].get("skip_initial_diag") == diag


def test_vampire_fast_unsat_does_not_start_harvest() -> None:
    import Mate_new_vampire as mate

    harvest = MagicMock(
        return_value=VampireResult(proved=False, status="timeout", elapsed=0.2)
    )

    def usefulness(*_a, **_k):
        return True, [_LEMMA], VampireResult(
            proved=True, status="unsat", elapsed=0.01
        )

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "LEMMA_LIBRARY": "on",
            "LEMMA_LIBRARY_LOCAL": "on",
            "SOLVER_ROUTING": "off",
            "LEMMA_DEFINED_SYMBOLS": "off",
            "USEFULNESS_HARVEST_DELAY_S": "2",
            "INDUCTION_SCHEME": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", return_value=[_LEMMA]
        ), patch(
            "Mate_new_vampire.validate_lemmas_parallel",
            side_effect=lambda _p, lemmas, *_a, **_k: list(lemmas),
        ), patch(
            "Mate_new_vampire.verify_combined_lemmas", side_effect=usefulness
        ), patch(
            "Mate_new_vampire.run_vampire_routed", harvest
        ):
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is True
        assert lemmas == [_LEMMA]
        harvest.assert_not_called()
        dispatch = mate.load_failed_lemmas(tmp, "template").get("harvest_dispatch") or {}
        assert dispatch.get("skip_initial") == []


def test_vampire_quick_run_starts_scheme_with_vampire_profiles() -> None:
    import Mate_new_vampire as mate
    from induction_scheme.prove import default_vampire_prove

    session = MagicMock()
    captured = {}

    def fake_start(**kwargs):
        captured.update(kwargs)
        return session

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(TINY_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "INDUCTION_SCHEME": "on",
            "INDUCTION_SCHEME_TRIGGER": "always",
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY": "off",
            "LEMMA_LIBRARY_LOCAL": "off",
        }), patch(
            "induction_scheme.mate_glue.maybe_start_scheme_session",
            side_effect=fake_start,
        ), patch(
            "induction_scheme.mate_glue.barrier_and_finalize",
        ), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", return_value=[]
        ), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ):
            mate.quick_run(tmp, "template", "p", "./prompts_ours")

    assert captured.get("profiles") == list(VAMPIRE_PROVE_PROFILES)
    assert captured.get("prove_fn") is default_vampire_prove
    assert tuple(HARVEST_VAMPIRE_PROFILES) == tuple(VAMPIRE_PROVE_PROFILES)
