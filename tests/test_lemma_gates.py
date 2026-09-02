#!/usr/bin/env python3
"""Defined-symbol gate, child attempt cap, sat abort, empty+reason diagnosis."""

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

from exp_flags import resolve_prompt_pack
from lemma_gates import (
    DIAGNOSIS_PROMPT_SUFFIX,
    node_attempt_plan,
    parse_llm_reason,
    should_append_diagnosis_suffix,
    undefined_symbols_in_lemma,
    tree_status_from_child_data,
)

P2_SMT = (ROOT / "experiments" / "cases" / "p2_len_rev" / "template.smt2").read_text(
    encoding="utf-8"
)
PLUS_LEMMA = (
    "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
)
SNOC_LEMMA = (
    "(forall ((x Lst) (y Nat)) (= (len (append x (cons y nil))) (succ (len x))))"
)
_GOAL = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""


def test_undefined_plus_and_defined_snoc() -> None:
    assert undefined_symbols_in_lemma(PLUS_LEMMA, P2_SMT) == ["plus"]
    assert undefined_symbols_in_lemma(SNOC_LEMMA, P2_SMT) == []


def test_parse_llm_reason() -> None:
    raw = "; Output begin\n\n; Output end\n; reason: plus has no axioms\n"
    assert parse_llm_reason(raw) == "plus has no axioms"
    assert parse_llm_reason("; Output begin\n(forall ((x Int)) true)\n; Output end") is None


def test_node_attempt_plan_child_cap() -> None:
    pack = resolve_prompt_pack("default", 3)
    with patch.dict(os.environ, {"CHILD_LLM_ATTEMPTS": "2"}):
        assert node_attempt_plan(1, pack) == (2, 1)
    with patch.dict(os.environ, {"CHILD_LLM_ATTEMPTS": "0"}):
        assert node_attempt_plan(1, pack) == (6, 3)
    with patch.dict(os.environ, {"CHILD_LLM_ATTEMPTS": "2"}):
        assert node_attempt_plan(0, pack) == (6, 3)


def test_tree_status_sat_is_invalid() -> None:
    status, reason = tree_status_from_child_data({
        "baseline_diag": {"status": "sat"},
        "node_outcome": {},
    })
    assert status == "invalid"
    assert "sat" in reason
    status, reason = tree_status_from_child_data({
        "node_outcome": {"kind": "invalid", "reason": "undefined_symbol:plus"},
        "baseline_diag": {"status": "incomplete"},
    })
    assert status == "invalid"
    assert reason == "undefined_symbol:plus"
    status, _reason = tree_status_from_child_data({
        "baseline_diag": {"status": "timeout"},
    })
    assert status == "failed"


def test_quick_run_rejects_undefined_plus() -> None:
    import Mate_new_vampire as mate

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "LEMMA_DEFINED_SYMBOLS": "on",
            "SOLVER_ROUTING": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", return_value=[PLUS_LEMMA]
        ), patch("Mate_new_vampire.run_vampire") as vampire:
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is False
        assert subgoals == []
        assert lemmas == [PLUS_LEMMA]
        vampire.assert_not_called()
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert any("undefined_symbol:plus" in str(item.get("reason")) for item in invalid)


def test_sat_aborts_child_without_llm() -> None:
    import Mate_new_vampire as mate
    from vampire_runner import VampireResult

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        sat = VampireResult(status="sat", proved=False, elapsed=0.05)
        with patch.dict(os.environ, {
            "SUBGOAL_SAT_ABORT": "on",
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY": "off",
        }), patch(
            "Mate_new_vampire.run_vampire_routed", return_value=sat
        ), patch("Mate_new_vampire.generate_lemmas_with_llm") as gen:
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        gen.assert_not_called()
        outcome = mate.load_failed_lemmas(tmp, "template")["node_outcome"]
        assert outcome.get("kind") == "invalid"
        assert outcome.get("reason") == "solver:sat"


def test_diagnosis_suffix_flag() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on"}):
            root, _ = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=0,
            )
            child, _ = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1,
            )
        assert "reason: <short explanation>" not in root[1]["content"]
        assert DIAGNOSIS_PROMPT_SUFFIX.strip() in child[1]["content"]
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "off"}):
            child_off, _ = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1,
            )
        assert "reason: <short explanation>" not in child_off[1]["content"]


def test_should_append_diagnosis_by_depth() -> None:
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on"}):
        assert should_append_diagnosis_suffix(0) is False
        assert should_append_diagnosis_suffix(1) is True
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "off"}):
        assert should_append_diagnosis_suffix(1) is False


def test_child_empty_reason_stops_attempts() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    def fake_llm(_smt, _strat, _path, base_path, goal_name, _folder, depth=0):
        mate._store_last_llm_reason(base_path, goal_name, "plus has no axioms")
        return []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        timeout = CvcResult(status="timeout", proved=False, elapsed=0.05)
        with patch.dict(os.environ, {
            "LLM_LEMMA_DIAGNOSIS": "on",
            "SUBGOAL_SAT_ABORT": "off",
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY": "off",
            "CHILD_LLM_ATTEMPTS": "2",
        }), patch("Mate_new.run_cvc_routed", return_value=timeout), patch(
            "Mate_new.generate_lemmas_with_llm", side_effect=fake_llm
        ) as gen:
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        assert gen.call_count == 1
        outcome = mate.load_failed_lemmas(tmp, "template")["node_outcome"]
        assert outcome.get("kind") == "invalid"
        assert "plus" in outcome.get("reason", "")


def main() -> int:
    test_undefined_plus_and_defined_snoc()
    test_parse_llm_reason()
    test_node_attempt_plan_child_cap()
    test_tree_status_sat_is_invalid()
    test_quick_run_rejects_undefined_plus()
    test_sat_aborts_child_without_llm()
    test_diagnosis_suffix_flag()
    test_should_append_diagnosis_by_depth()
    test_child_empty_reason_stops_attempts()
    print("lemma gate tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
