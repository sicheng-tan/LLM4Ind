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
                tmp, "template", "template_1", ["(assert true)"]
            )
        diag.assert_not_called()
        parent = mate.load_failed_lemmas(tmp, "template")
        kinds = [h.get("kind") for h in parent.get("repair_hints") or []]
        assert "subgoal_failed" in kinds
        assert parent["unproved_lemmas"][0]["lemma"] == "(assert true)"


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
                tmp, "template", "template_1", ["(assert true)"]
            )
        diag.assert_not_called()
        parent = mv.load_failed_lemmas(tmp, "template")
        assert any(h.get("kind") == "subgoal_failed" for h in parent["repair_hints"])


def main() -> int:
    test_inject_difficulty_script()
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
    print("prove diagnostics tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
