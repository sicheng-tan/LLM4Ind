#!/usr/bin/env python3
"""Defined-symbol gate, child attempt cap, sat abort, empty+reason and final diagnosis."""

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
    FINAL_DIAGNOSIS_PROMPT_SUFFIX,
    attach_source_lemmas,
    format_repair_header,
    is_invalid_diagnosis_reason,
    node_attempt_plan,
    parse_final_diagnosis,
    parse_llm_reason,
    repair_hint_for_prompt,
    should_append_diagnosis_suffix,
    should_run_final_diagnosis,
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
    assert parse_final_diagnosis("invalid\n; reason: plus has no axioms") == (
        "invalid", "plus has no axioms",
    )
    assert parse_final_diagnosis("; Output begin\ninvalid\n; Output end\n; reason: plus")[0] == "invalid"
    assert parse_final_diagnosis("failed") == ("failed", None)
    assert parse_final_diagnosis("still_open") == ("failed", None)
    assert parse_final_diagnosis("; reason: still_open") == ("failed", None)
    assert parse_final_diagnosis("; reason: plus has no axioms") == (
        "invalid", "plus has no axioms",
    )
    assert parse_final_diagnosis("") == ("failed", None)
    assert is_invalid_diagnosis_reason("plus has no axioms")
    assert is_invalid_diagnosis_reason("invalid")
    assert not is_invalid_diagnosis_reason("still_open")
    assert not is_invalid_diagnosis_reason("failed")
    assert not is_invalid_diagnosis_reason(None)
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on"}):
        assert should_run_final_diagnosis(1) is True
        assert should_run_final_diagnosis(0) is False
        assert should_run_final_diagnosis(1, has_tree=False) is False
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "off"}):
        assert should_run_final_diagnosis(1) is False


def test_repair_header_lists_usefulness_lemmas() -> None:
    lemma = "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
    initial = format_repair_header("Vampire", [{
        "kind": "need_rewrite",
        "context": "initial_goal",
        "detail": "rewriting scarce",
    }])
    assert len(initial) == 1
    assert "Use these hints to choose the NEXT lemmas:" in initial[0]
    assert "C1:" not in "\n".join(initial)
    assert "Failed to prove the goal using the above lemmas" not in "\n".join(initial)

    hints = attach_source_lemmas(
        [{"kind": "need_rewrite", "detail": "rewriting scarce"}],
        [lemma],
        context="usefulness_check",
    )
    header = "\n".join(format_repair_header("Vampire", hints))
    assert header.startswith("\n; SOLVER-GUIDED REPAIR (from Vampire failure analysis).")
    assert "C1:" in header
    assert "plus" in header
    bridge = (
        "Failed to prove the goal using the above lemmas and produced hints. "
        "Use these hints to choose the NEXT lemmas:"
    )
    assert bridge in header
    assert header.index("SOLVER-GUIDED REPAIR") < header.index("C1:")
    assert header.index("C1:") < header.index(bridge)


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


def test_tree_status_nested_invalid_does_not_mark_parent() -> None:
    from obligation_tree import append_attempt, make_child_node, make_goal_tree

    tree = make_goal_tree(
        "template_1",
        [
            make_child_node(
                node_id="template_1_1",
                formula="(forall ((m Nat)) (= (plus zero m) m))",
                status="failed",
            ),
            make_child_node(
                node_id="template_1_2",
                formula="(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m))))",
                status="invalid",
                reason="plus has no defining axioms",
            ),
        ],
        proved=False,
    )
    status, reason = tree_status_from_child_data({
        "node_outcome": {},
        "baseline_diag": {"status": "incomplete"},
        "obligation": append_attempt({}, "obligation_tree", tree),
    })
    assert status == "failed"
    assert reason == ""


def test_repair_hint_for_prompt_drops_subgoal_atp() -> None:
    assert repair_hint_for_prompt({"kind": "need_rewrite", "context": "initial_goal"})
    assert repair_hint_for_prompt({"kind": "no_progress", "context": "usefulness_check"})
    assert not repair_hint_for_prompt({"kind": "subgoal_failed", "context": "subgoal:template_1"})
    assert not repair_hint_for_prompt({
        "kind": "need_rewrite", "context": "subgoal:template_1",
    })
    assert not repair_hint_for_prompt({
        "kind": "induction_stuck", "context": "subgoal:template_1",
    })


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
        assert "previously proposed child lemma is marked invalid" in child[1]["content"]
        final, _ = mate.create_prompt(
            _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
            "./prompts_ours", depth=1, diagnosis_only=True,
        )
        assert FINAL_DIAGNOSIS_PROMPT_SUFFIX.strip() in final[1]["content"]
        assert "FINAL CHECK" in final[1]["content"]
        assert "propose different lemmas" not in final[1]["content"]
        assert "Using the obligation tree" in final[1]["content"]
        assert "output invalid" in final[1]["content"]
        assert "output failed." in final[1]["content"]
        assert "still_open" not in final[1]["content"]
        assert "prior attempts" not in final[1]["content"]
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

    def fake_llm(_smt, _strat, _path, base_path, goal_name, _folder, depth=0, **_kwargs):
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


def test_invalid_child_records_invalid_not_unproved() -> None:
    import Mate_new_vampire as mate

    with tempfile.TemporaryDirectory() as tmp:
        mate._set_node_outcome(
            tmp, "template_1",
            kind="invalid", reason="plus has no axioms", source="llm",
        )
        with patch("Mate_new_vampire.run_vampire_diagnostic") as diag:
            mate._record_subgoal_failure_feedback(
                tmp, "template", "template_1", [PLUS_LEMMA],
            )
        diag.assert_not_called()
        parent = mate.load_failed_lemmas(tmp, "template")
        assert parent["unproved_lemmas"] == []
        assert parent["invalid_lemmas"][0]["lemma"] == PLUS_LEMMA
        assert "plus" in parent["invalid_lemmas"][0]["reason"]
        assert not any(
            h.get("kind") == "subgoal_failed" for h in parent.get("repair_hints") or []
        )


def test_cancelled_invalid_child_keeps_reason() -> None:
    import Mate_new_vampire as mate

    formula = (
        "(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m))))"
    )
    with tempfile.TemporaryDirectory() as tmp:
        mate._set_node_outcome(
            tmp, "template_1_2",
            kind="invalid", reason="plus has no axioms", source="llm",
        )
        node = mate._child_obligation_node(tmp, "template_1_2", formula, "cancelled")
        assert node["status"] == "invalid"
        assert "plus" in (node.get("reason") or "")


def test_prompt_invalid_not_unproved_and_drops_child_atp() -> None:
    import Mate_new_vampire as mate

    txt = mate.format_solver_feedback_for_prompt({
        "invalid_lemmas": [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}],
        "unproved_lemmas": [],
        "useless_lemma_groups": [],
        "progress_lemmas": [],
        "repair_hints": [
            {
                "kind": "need_rewrite",
                "context": "initial_goal",
                "detail": "root rewrite",
                "suggested_actions": [],
            },
            {
                "kind": "induction_stuck",
                "context": "subgoal:template_1",
                "detail": "child stuck",
                "suggested_actions": ["weaken"],
            },
            {
                "kind": "need_induction_lemma",
                "context": "subgoal:template_1",
                "detail": "child induction",
                "suggested_actions": [],
            },
        ],
        "routing": {},
    })
    assert "do not weaken" in txt
    assert "plus has no axioms" in txt
    assert "USEFUL BUT UNPROVED" not in txt
    assert "root rewrite" in txt
    assert "child stuck" not in txt
    assert "child induction" not in txt


def test_invalid_child_does_not_stop_parent_attempts() -> None:
    import Mate_new_vampire as mate
    from obligation_tree import make_child_node

    child = make_child_node(
        node_id="template_1",
        formula=PLUS_LEMMA,
        status="invalid",
        reason="plus has no axioms",
    )
    calls = {"n": 0}
    diagnoses = {"n": 0}

    def fake_quick(*_args, **_kwargs):
        calls["n"] += 1
        return True, ["template_1"], [PLUS_LEMMA]

    def fake_parallel(*_args, **_kwargs):
        return False, [child]

    def fake_gen(*_args, diagnosis_only=False, **_kwargs):
        if diagnosis_only:
            diagnoses["n"] += 1
            mate._store_last_llm_reason(_args[3], _args[4], "failed")
            return []
        return []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "CHILD_LLM_ATTEMPTS": "2",
            "SUBGOAL_SAT_ABORT": "off",
            "LEMMA_LIBRARY": "off",
            "LLM_LEMMA_DIAGNOSIS": "on",
        }), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new_vampire.quick_run", side_effect=fake_quick
        ), patch(
            "Mate_new_vampire.prove_subgoals_parallel", side_effect=fake_parallel
        ), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", side_effect=fake_gen
        ):
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        assert calls["n"] == 2
        assert diagnoses["n"] == 1
        outcome = mate.load_failed_lemmas(tmp, "template").get("node_outcome") or {}
        assert outcome.get("kind") != "invalid"


def test_final_diagnosis_prompt_is_tree_only() -> None:
    import Mate_new as mate
    from obligation_tree import append_attempt, make_child_node, make_goal_tree

    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula=PLUS_LEMMA,
                status="invalid",
                reason="plus has no axioms",
            ),
        ],
        proved=False,
    )
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        data = mate._empty_failed_data()
        data["invalid_lemmas"] = [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]
        data["unproved_lemmas"] = [{"lemma": SNOC_LEMMA, "status": "timeout"}]
        data["repair_hints"] = [{
            "kind": "need_rewrite",
            "context": "initial_goal",
            "detail": "root rewrite",
            "suggested_actions": [],
        }]
        data["last_llm_reason"] = "previous empty"
        data["obligation"] = append_attempt({}, "obligation_tree", tree)
        mate.save_failed_lemmas(tmp, "template", data)
        with patch.dict(os.environ, {
            "LLM_LEMMA_DIAGNOSIS": "on",
            "OBLIGATION_TREE": "on",
            "LEMMA_LIBRARY": "on",
            "FEEDBACK_REPAIR_HINTS": "on",
            "UNPROVED_NOT_INVALID": "on",
        }):
            messages, extra = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1, diagnosis_only=True,
            )
            gen, gen_extra = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1, diagnosis_only=False,
            )
        text = messages[1]["content"]
        assert "FINAL CHECK" in text
        assert "Last obligation tree" in extra
        assert "L1  invalid [plus has no axioms]" in extra
        assert "IMPORTANT: The following lemmas are INVALID" not in text
        assert "USEFUL BUT UNPROVED" not in text
        assert "SOLVER-GUIDED REPAIR" not in extra
        assert "Previous empty output reason" not in text
        assert "Previous empty output reason" not in gen_extra
        assert "generate lemmas for the CURRENT goal only" not in extra
        assert "IMPORTANT: The following lemmas are INVALID" in gen_extra
        assert "Last obligation tree" in gen_extra


def test_final_diagnosis_marks_goal_invalid() -> None:
    import Mate_new_vampire as mate
    from obligation_tree import make_child_node

    child = make_child_node(
        node_id="template_1",
        formula=PLUS_LEMMA,
        status="invalid",
        reason="plus has no defining axioms",
    )

    def fake_quick(*_args, **_kwargs):
        return True, ["template_1"], [PLUS_LEMMA]

    def fake_gen(*_args, diagnosis_only=False, **_kwargs):
        if diagnosis_only:
            mate._store_last_llm_reason(
                _args[3], _args[4], "plus has no defining axioms",
            )
            return []
        return []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "CHILD_LLM_ATTEMPTS": "2",
            "SUBGOAL_SAT_ABORT": "off",
            "LEMMA_LIBRARY": "off",
            "LLM_LEMMA_DIAGNOSIS": "on",
        }), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new_vampire.quick_run", side_effect=fake_quick
        ), patch(
            "Mate_new_vampire.prove_subgoals_parallel",
            return_value=(False, [child]),
        ), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", side_effect=fake_gen
        ):
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        outcome = mate.load_failed_lemmas(tmp, "template")["node_outcome"]
        assert outcome.get("kind") == "invalid"
        assert "plus" in outcome.get("reason", "")
        assert outcome.get("source") == "llm_final"


def test_final_diagnosis_skipped_without_tree() -> None:
    import Mate_new_vampire as mate
    from obligation_tree import last_normal_tree

    diag = {"n": 0}

    def fake_quick(*_args, **_kwargs):
        return False, [], [
            "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
        ]

    def fake_gen(*_args, diagnosis_only=False, **_kwargs):
        if diagnosis_only:
            diag["n"] += 1
        return []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "CHILD_LLM_ATTEMPTS": "2",
            "SUBGOAL_SAT_ABORT": "off",
            "LEMMA_LIBRARY": "off",
            "LLM_LEMMA_DIAGNOSIS": "on",
            "OBLIGATION_TREE": "on",
        }), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new_vampire.quick_run", side_effect=fake_quick
        ), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", side_effect=fake_gen
        ):
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        assert diag["n"] == 0
        obligation = mate.load_failed_lemmas(tmp, "template").get("obligation") or {}
        assert last_normal_tree(obligation) is None
        outcome = mate.load_failed_lemmas(tmp, "template").get("node_outcome") or {}
        assert outcome.get("kind") != "invalid"


def test_final_diagnosis_skipped_at_root() -> None:
    import Mate_new_vampire as mate

    gen = {"n": 0}

    def fake_quick(*_args, **_kwargs):
        return False, [], []

    def fake_gen(*_args, diagnosis_only=False, **_kwargs):
        gen["n"] += 1
        return []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "LLM_LEMMA_DIAGNOSIS": "on",
        }), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new_vampire.quick_run", side_effect=fake_quick
        ), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", side_effect=fake_gen
        ), patch.dict(mate.config, {"MAX_ATTEMPTS_PER_PROMPT": 1}):
            ok = mate.prove_run(tmp, "template", depth=0)
        assert ok is False
        assert gen["n"] == 0


def main() -> int:
    test_undefined_plus_and_defined_snoc()
    test_parse_llm_reason()
    test_repair_header_lists_usefulness_lemmas()
    test_node_attempt_plan_child_cap()
    test_tree_status_sat_is_invalid()
    test_tree_status_nested_invalid_does_not_mark_parent()
    test_repair_hint_for_prompt_drops_subgoal_atp()
    test_quick_run_rejects_undefined_plus()
    test_sat_aborts_child_without_llm()
    test_diagnosis_suffix_flag()
    test_should_append_diagnosis_by_depth()
    test_child_empty_reason_stops_attempts()
    test_invalid_child_records_invalid_not_unproved()
    test_cancelled_invalid_child_keeps_reason()
    test_prompt_invalid_not_unproved_and_drops_child_atp()
    test_invalid_child_does_not_stop_parent_attempts()
    test_final_diagnosis_prompt_is_tree_only()
    test_final_diagnosis_marks_goal_invalid()
    test_final_diagnosis_skipped_without_tree()
    test_final_diagnosis_skipped_at_root()
    print("lemma gate tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
