#!/usr/bin/env python3
"""Defined-symbol gate, child attempt cap, sat abort, empty+reason and final diagnosis."""

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

from exp_flags import resolve_prompt_pack
from lemma_gates import (
    DIAGNOSIS_PROMPT_SUFFIX,
    FINAL_DIAGNOSIS_PROMPT_SUFFIX,
    HD_AXIOM_GOAL_HINT,
    HD_DIFFICULTY_EXPLAIN,
    PARSE_ERR_EMPTY,
    PARSE_ERR_UNMATCHED,
    allow_unmarked_lemma_output,
    apply_static_lemma_screen,
    attach_source_lemmas,
    drop_failing_members,
    format_attempt_feedback_for_prompt,
    format_diagnosis_invalid_prompt,
    format_repair_header,
    drop_equivalent_unproved,
    is_invalid_diagnosis_reason,
    lemma_known_invalid,
    lemma_known_unproved,
    lemma_same_as_goal,
    lemmas_known_invalid,
    should_promote_child_pending,
    promote_child_pending_lemmas,
    REVIVAL_ORIGIN_CHILD_PENDING,
    REVIVAL_ORIGIN_SITUATION_A,
    llm_parse_retries,
    node_attempt_plan,
    parse_final_diagnosis,
    parse_llm_lemmas,
    parse_llm_reason,
    repair_hint_for_prompt,
    should_append_diagnosis_suffix,
    should_run_final_diagnosis,
    undefined_symbols_in_lemma,
    tree_status_from_child_data,
    with_parse_retry_hint,
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


def test_lemma_same_as_goal_alpha() -> None:
    goal = "(forall ((x Int)) (P x))"
    renamed = "(forall ((y Int)) (P y))"
    other = "(forall ((x Int)) (P (s x)))"
    assert lemma_same_as_goal(goal, goal)
    assert lemma_same_as_goal(renamed, goal)
    assert not lemma_same_as_goal(other, goal)


def test_drop_failing_members_keeps_rest() -> None:
    lemmas = [PLUS_LEMMA, SNOC_LEMMA]
    with patch.dict(os.environ, {"LEMMA_FILTER_DROP": "on"}):
        kept, dropped = drop_failing_members(
            lemmas, lambda lemma: "bad" if lemma == PLUS_LEMMA else None
        )
    assert kept == [SNOC_LEMMA]
    assert dropped == [(PLUS_LEMMA, "bad")]
    with patch.dict(os.environ, {"LEMMA_FILTER_DROP": "off"}):
        kept, dropped = drop_failing_members(
            lemmas, lambda lemma: "bad" if lemma == PLUS_LEMMA else None
        )
    assert kept == []
    assert dropped == [(PLUS_LEMMA, "bad")]


def test_static_screen_drops_undefined_keeps_defined() -> None:
    with patch.dict(os.environ, {
        "LEMMA_FILTER_DROP": "on",
        "LEMMA_DEFINED_SYMBOLS": "on",
    }):
        kept, dropped = apply_static_lemma_screen(
            [PLUS_LEMMA, SNOC_LEMMA],
            original_forall="(forall ((x Lst)) (= (len (rev x)) (len x)))",
            smt=P2_SMT,
            invalid_records=[],
            same_as_goal=lambda _lemma, _goal: False,
        )
    assert kept == [SNOC_LEMMA]
    assert len(dropped) == 1
    assert dropped[0][2] == "undefined_symbol"
    assert "plus" in dropped[0][1]


def test_static_screen_drops_library_alpha_keeps_rest() -> None:
    snoc_alpha = (
        "(forall ((xs Lst) (n Nat)) (= (len (append xs (cons n nil))) (succ (len xs))))"
    )
    with patch.dict(os.environ, {
        "LEMMA_FILTER_DROP": "off",
        "LEMMA_DEFINED_SYMBOLS": "off",
    }):
        kept, dropped = apply_static_lemma_screen(
            [snoc_alpha, PLUS_LEMMA],
            original_forall="(forall ((x Lst)) (= (len (rev x)) (len x)))",
            smt=P2_SMT,
            invalid_records=[],
            same_as_goal=lemma_same_as_goal,
            library_items=[{"id": "lib_1", "formula": SNOC_LEMMA}],
        )
    assert kept == [PLUS_LEMMA]
    assert len(dropped) == 1
    assert dropped[0][2] == "same_as_library"
    assert dropped[0][1] == "already_in_library:lib_1"


def test_known_invalid_match_whitespace_not_substring() -> None:
    records = [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]
    spaced = "  " + PLUS_LEMMA.replace(" ", "  ") + "\n"
    assert lemma_known_invalid(spaced, records)
    assert lemmas_known_invalid([spaced, SNOC_LEMMA], records) == [spaced]
    overlapping = PLUS_LEMMA + " (P a)"
    assert PLUS_LEMMA in overlapping
    assert not lemma_known_invalid(overlapping, records)
    assert not lemma_known_invalid(SNOC_LEMMA, records)
    assert lemmas_known_invalid([SNOC_LEMMA], records) == []
    assert lemmas_known_invalid([PLUS_LEMMA], []) == []


def test_unproved_dedup_whitespace_and_alpha() -> None:
    formula = "(forall ((x Int)) (P x))"
    alpha = "(forall ((y Int)) (P y))"
    spaced = "  " + formula.replace(" ", "  ") + "\n"
    other = "(forall ((x Int)) (P (s x)))"
    records = [{"lemma": formula, "status": "timeout"}]
    assert lemma_known_unproved(formula, records)
    assert lemma_known_unproved(spaced, records)
    assert lemma_known_unproved(alpha, records)
    assert not lemma_known_unproved(other, records)
    assert not lemma_known_unproved("", records)
    kept, n_removed = drop_equivalent_unproved(
        records + [{"lemma": other, "status": "unknown"}], alpha
    )
    assert n_removed == 1
    assert kept == [{"lemma": other, "status": "unknown"}]


def test_add_unproved_lemma_dedups_equivalent() -> None:
    import Mate_new as mate

    formula = "(forall ((x Int)) (P x))"
    alpha = "(forall ((y Int)) (P y))"
    other = "(forall ((x Int)) (Q x))"
    with tempfile.TemporaryDirectory() as tmp:
        mate.add_unproved_lemma(tmp, "template", formula, {"status": "timeout"})
        mate.add_unproved_lemma(
            tmp, "template", "  " + formula + "\n", {"status": "unknown"}
        )
        mate.add_unproved_lemma(tmp, "template", alpha, {"status": "timeout"})
        mate.add_unproved_lemma(tmp, "template", other, {"status": "timeout"})
        mate.add_unproved_lemma(tmp, "template_1", formula, {"status": "timeout"})
        records = mate.load_failed_lemmas(tmp, "template")["unproved_lemmas"]
        assert [item["lemma"] for item in records] == [formula, other]
        child = mate.load_failed_lemmas(tmp, "template_1")["unproved_lemmas"]
        assert [item["lemma"] for item in child] == [formula]


def test_situation_a_dual_writes_revival_not_into_child_pending() -> None:
    import Mate_new as mate

    lemma = "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
    with tempfile.TemporaryDirectory() as tmp:
        mate._record_blocking_lemma(
            tmp, "template", lemma,
            {"status": "useful_but_unproved", "blocking_subgoal": "template_1"},
        )
        data = mate.load_failed_lemmas(tmp, "template")
        assert [item["lemma"] for item in data["unproved_lemmas"]] == [lemma]
        assert len(data["revival_lemmas"]) == 1
        rec = data["revival_lemmas"][0]
        assert rec["lemma"] == lemma
        assert rec["origin"] == REVIVAL_ORIGIN_SITUATION_A
        assert rec["blocking_subgoal"] == "template_1"
        prompt = mate.format_solver_feedback_for_prompt(data, tmp)
        assert "USEFUL BUT UNPROVED" in prompt
        assert lemma in prompt
        assert REVIVAL_ORIGIN_CHILD_PENDING not in prompt


def test_promote_child_pending_skips_library_blocking_timeout() -> None:
    import Mate_new as mate

    goal_len = "(forall ((x Lst)) (= (len (rev x)) (len x)))"
    homo = (
        "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
    )
    plus_zero = "(forall ((n Nat)) (= (plus n zero) n))"
    timeout_c = "(forall ((x Lst)) (= (rev (rev x)) x))"
    assert should_promote_child_pending(
        plus_zero, current_goal=goal_len, library=[], blocking_lemma=homo,
    )
    assert not should_promote_child_pending(
        plus_zero, current_goal=goal_len, library=[{"formula": plus_zero}],
        blocking_lemma=homo,
    )
    assert not should_promote_child_pending(
        homo, current_goal=goal_len, library=[], blocking_lemma=homo,
    )
    assert not should_promote_child_pending(
        goal_len, current_goal=goal_len, library=[], blocking_lemma=homo,
    )

    with tempfile.TemporaryDirectory() as tmp:
        mate._record_blocking_lemma(
            tmp, "template_1", plus_zero,
            {"status": "useful_but_unproved"},
        )
        mate.save_failed_lemmas(tmp, "template", {
            **mate._empty_failed_data(),
            "useless_lemma_groups": [{"lemmas": [timeout_c], "status": "timeout"}],
        })
        n = promote_child_pending_lemmas(
            tmp, "template", "template_1",
            blocking_lemma=homo,
            current_goal=goal_len,
            library=[],
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        assert n == 1
        parent = mate.load_failed_lemmas(tmp, "template")
        assert parent["unproved_lemmas"] == []
        assert timeout_c not in [
            item["lemma"] for item in parent["revival_lemmas"]
        ]
        rec = parent["revival_lemmas"][0]
        assert rec["lemma"] == plus_zero
        assert rec["origin"] == REVIVAL_ORIGIN_CHILD_PENDING
        assert rec["source_goal"] == "template_1"
        prompt = mate.format_solver_feedback_for_prompt(parent, tmp)
        assert "USEFUL BUT UNPROVED" not in prompt
        assert plus_zero not in prompt

        n_dup = promote_child_pending_lemmas(
            tmp, "template", "template_1",
            blocking_lemma=homo,
            current_goal=goal_len,
            library=[],
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        assert n_dup == 0


def test_promote_inherits_child_revival_not_deeper_files() -> None:
    """Parent copies the child's revival pool; deeper files stay put until promoted."""
    import Mate_new as mate

    goal_len = "(forall ((x Lst)) (= (len (rev x)) (len x)))"
    homo = (
        "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
    )
    plus_zero = "(forall ((n Nat)) (= (plus n zero) n))"
    len_ge = "(forall ((x Lst)) (>= (len x) 0))"
    great = "(forall ((x Lst)) (= (rev (rev (rev x))) (rev x)))"

    with tempfile.TemporaryDirectory() as tmp:
        mate._record_blocking_lemma(
            tmp, "template_1_1", len_ge,
            {"status": "useful_but_unproved", "blocking_subgoal": "template_1_1_1"},
        )
        n_mid = promote_child_pending_lemmas(
            tmp, "template_1", "template_1_1",
            blocking_lemma=plus_zero,
            current_goal=homo,
            library=[],
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        assert n_mid == 1
        mate._record_blocking_lemma(
            tmp, "template_1", plus_zero,
            {"status": "useful_but_unproved", "blocking_subgoal": "template_1_1"},
        )
        great_data = mate._empty_failed_data()
        great_data["unproved_lemmas"] = [
            {"lemma": great, "status": "useful_but_unproved"},
        ]
        great_data["revival_lemmas"] = [{
            "lemma": great,
            "status": "unproved",
            "origin": REVIVAL_ORIGIN_SITUATION_A,
            "source_goal": "template_1_1_1",
        }]
        mate.save_failed_lemmas(tmp, "template_1_1_1", great_data)

        n = promote_child_pending_lemmas(
            tmp, "template", "template_1",
            blocking_lemma=homo,
            current_goal=goal_len,
            library=[],
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        assert n == 2
        parent = mate.load_failed_lemmas(tmp, "template")
        assert parent["unproved_lemmas"] == []
        by_lemma = {item["lemma"]: item for item in parent["revival_lemmas"]}
        assert set(by_lemma) == {plus_zero, len_ge}
        assert by_lemma[plus_zero]["origin"] == REVIVAL_ORIGIN_CHILD_PENDING
        assert by_lemma[plus_zero]["source_goal"] == "template_1"
        assert by_lemma[len_ge]["origin"] == REVIVAL_ORIGIN_CHILD_PENDING
        assert by_lemma[len_ge]["source_goal"] == "template_1_1"
        prompt = mate.format_solver_feedback_for_prompt(parent, tmp)
        assert "USEFUL BUT UNPROVED" not in prompt
        assert plus_zero not in prompt
        assert len_ge not in prompt


def test_parse_llm_reason() -> None:
    raw = "; Output begin\n\n; Output end\n; INVALID_GOAL: plus has no axioms\n"
    assert parse_llm_reason(raw) == "plus has no axioms"
    assert parse_llm_reason("INVALID_GOAL: plus has no axioms") == "plus has no axioms"
    assert parse_llm_reason("; Output begin\n(forall ((x Int)) true)\n; Output end") is None
    assert parse_llm_reason("reason: the IH does not match") is None
    assert parse_llm_reason("; reason: plus has no axioms") is None
    assert parse_final_diagnosis("invalid\n; INVALID_GOAL: plus has no axioms") == (
        "invalid", "plus has no axioms",
    )
    assert parse_final_diagnosis("; Output begin\ninvalid\n; Output end\n; INVALID_GOAL: plus")[0] == "invalid"
    assert parse_final_diagnosis("failed") == ("failed", None)
    assert parse_final_diagnosis("still_open") == ("failed", None)
    assert parse_final_diagnosis("; INVALID_GOAL: still_open") == ("failed", None)
    assert parse_final_diagnosis("; INVALID_GOAL: plus has no axioms") == (
        "invalid", "plus has no axioms",
    )
    assert parse_final_diagnosis("; reason: plus has no axioms") == ("failed", None)
    assert parse_final_diagnosis("") == ("failed", None)
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on"}):
        assert allow_unmarked_lemma_output(
            "thinking\n; INVALID_GOAL: plus has no axioms\n",
            diagnosis_only=False,
            depth=1,
        )
        assert not allow_unmarked_lemma_output(
            "thinking\n; INVALID_GOAL: plus has no axioms\n",
            diagnosis_only=False,
            depth=0,
        )
        assert not allow_unmarked_lemma_output(
            "thinking with no diagnosis line", diagnosis_only=False, depth=1,
        )
        assert not allow_unmarked_lemma_output(
            "thinking\nreason: the IH does not match\n",
            diagnosis_only=False,
            depth=1,
        )
        assert not allow_unmarked_lemma_output(
            "; reason: plus has no axioms", diagnosis_only=False, depth=1,
        )
        assert allow_unmarked_lemma_output(
            "thinking with no diagnosis line", diagnosis_only=True,
        )
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "off"}):
        assert not allow_unmarked_lemma_output(
            "; INVALID_GOAL: plus has no axioms", diagnosis_only=False, depth=1,
        )
    assert is_invalid_diagnosis_reason("plus has no axioms")
    assert is_invalid_diagnosis_reason("invalid")
    assert not is_invalid_diagnosis_reason("still_open")
    assert not is_invalid_diagnosis_reason("failed")
    assert not is_invalid_diagnosis_reason(None)
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on"}):
        assert should_run_final_diagnosis(1) is True
        assert should_run_final_diagnosis(0) is False
        assert should_run_final_diagnosis(1, has_invalid=False) is False
    with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "off"}):
        assert should_run_final_diagnosis(1) is False
    assert "CURRENT goal is also invalid" in format_diagnosis_invalid_prompt({
        "invalid_lemmas": [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}],
    })
    assert format_diagnosis_invalid_prompt({"invalid_lemmas": []}) == ""
    assert format_diagnosis_invalid_prompt({}) == ""


def test_parse_llm_lemmas_xml_and_legacy() -> None:
    snoc = "(forall ((x Nat) (y Lst)) (= (len (append y (cons x nil))) (succ (len y))))"
    plus = "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
    xml = (
        "<output>\n"
        f"<lemma>{snoc}</lemma>\n"
        f"<lemma>{plus}</lemma>\n"
        "</output>"
    )
    assert parse_llm_lemmas(xml) == [snoc, plus]
    assert parse_llm_lemmas(
        f"thinking\n<lemma>\n{snoc}\n</lemma>\n"
    ) == [snoc]
    multiline = (
        "<output>\n<lemma>\n"
        "(forall ((x Nat))\n"
        "  (= (plus x zero) x))\n"
        "</lemma>\n</output>"
    )
    assert parse_llm_lemmas(multiline) == [
        "(forall ((x Nat))\n  (= (plus x zero) x))",
    ]
    empty_raised = False
    try:
        parse_llm_lemmas("<output>\n</output>")
    except ValueError as exc:
        empty_raised = True
        assert str(exc) == PARSE_ERR_EMPTY
    assert empty_raised
    assert parse_llm_lemmas(
        "<output></output>\n; INVALID_GOAL: plus has no axioms\n",
        depth=1,
    ) == []
    root_invalid_raised = False
    try:
        parse_llm_lemmas(
            "<output></output>\n; INVALID_GOAL: plus has no axioms\n",
            depth=0,
        )
    except ValueError as exc:
        root_invalid_raised = True
        assert str(exc) == PARSE_ERR_EMPTY
    assert root_invalid_raised
    assert parse_llm_lemmas("<output>\n</output>", diagnosis_only=True) == []
    assert parse_llm_lemmas(
        f"<lemmas>\n<lemma>{snoc}</lemma>\n</lemmas>"
    ) == [snoc]
    assert parse_llm_lemmas(
        f"<output>\n<lemma>(assert {snoc})</lemma>\n</output>"
    ) == [snoc]
    legacy = f"; Output begin\n{snoc}\n; Output end"
    assert parse_llm_lemmas(legacy) == [snoc]
    wrapped = f"; Output begin\n(assert {snoc})\n; Output end"
    assert parse_llm_lemmas(wrapped) == [snoc]
    raised = False
    try:
        parse_llm_lemmas("no tags here")
    except ValueError as exc:
        raised = True
        assert "输出标记" in str(exc)
    assert raised


def test_parse_llm_lemmas_salvage_and_paren_repair() -> None:
    plus = "(forall ((n Nat) (m Nat)) (= (plus m n) (plus n m)))"
    salvaged = (
        "thinking\n; Need unknown lemma :\n"
        f"{plus}\n"
        "<output></output>\n"
    )
    assert parse_llm_lemmas(salvaged) == [plus]
    missing_one = "<output>\n<lemma>(forall ((x Nat)) (= (plus x zero) x)</lemma>\n</output>"
    assert parse_llm_lemmas(missing_one) == [
        "(forall ((x Nat)) (= (plus x zero) x))",
    ]
    missing_two = "<output>\n<lemma>(forall ((x Nat)) (= (plus x zero) x</lemma>\n</output>"
    assert parse_llm_lemmas(missing_two) == [
        "(forall ((x Nat)) (= (plus x zero) x))",
    ]
    too_open = "<output>\n<lemma>(forall ((x Nat)) (= (plus x zero</lemma>\n</output>"
    unmatched_raised = False
    try:
        parse_llm_lemmas(too_open)
    except ValueError as exc:
        unmatched_raised = True
        assert str(exc) == PARSE_ERR_UNMATCHED
    assert unmatched_raised


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
    assert header.startswith("\nSOLVER-GUIDED REPAIR (from Vampire failure analysis).")
    assert "C1:" in header
    assert "plus" in header
    bridge = (
        "Failed to prove the goal using the above lemmas and produced hints. "
        "Use these hints to choose the NEXT lemmas:"
    )
    assert bridge in header
    assert header.index("SOLVER-GUIDED REPAIR") < header.index("C1:")
    assert header.index("C1:") < header.index(bridge)


def test_last_attempt_omits_lemma_difficulty_tags() -> None:
    used = "(forall ((x Nat)) (= (plus x zero) x))"
    unused = "(forall ((x Nat)) true)"
    axiom = "(forall ((n Nat)) (= (plus zero n) n))"
    txt = format_attempt_feedback_for_prompt(
        {
            "useless_lemma_groups": [{
                "lemmas": [used, unused],
                "status": "timeout",
                "repair_hints": [{
                    "kind": "high_difficulty_assertions",
                    "hard_axioms": [axiom, used],
                    "source_lemmas": [used, unused],
                }],
            }],
        },
        backend="cvc5",
    )
    assert "[used" not in txt
    assert "[unused]" not in txt
    assert "[attributed" not in txt
    assert "high-difficulty axiom:" in txt
    assert "plus zero n" in txt or "plus zero" in txt
    assert used not in "\n".join(
        line for line in txt.splitlines() if "high-difficulty axiom:" in line
    )
    assert HD_DIFFICULTY_EXPLAIN in txt
    assert HD_AXIOM_GOAL_HINT in txt
    assert "Prefer a constructor/rewrite lemma" not in txt
    assert "Do not restate the goal" not in txt
    assert "inductive generalization" not in txt


def test_stale_lemma_usage_json_is_not_prompted() -> None:
    c1 = "(forall ((n Nat)) (= (plus n zero) n))"
    txt = format_attempt_feedback_for_prompt(
        {
            "useless_lemma_groups": [{
                "lemmas": [c1],
                "status": "timeout",
                "lemma_usage": [
                    {"lemma": c1, "score": 9, "used": True},
                ],
                "repair_hints": [{
                    "kind": "high_difficulty_assertions",
                    "hard_axioms": [c1],
                }],
            }],
        },
        backend="cvc5",
    )
    assert "1. " + c1 in txt
    assert "[used" not in txt
    assert "[unused]" not in txt
    assert "[attributed" not in txt


def test_last_attempt_prompt_keeps_latest_group_and_drops() -> None:
    kept = "(forall ((x Nat)) (= (plus x zero) x))"
    older = "(forall ((x Nat)) true)"
    lib_dup = "(forall ((y Nat)) (= (plus y zero) y))"
    axiom = "(forall ((n Nat)) (= (plus n zero) n))"
    txt = format_attempt_feedback_for_prompt(
        {
            "useless_lemma_groups": [
                {"lemmas": [older], "status": "timeout"},
                {
                    "lemmas": [kept],
                    "status": "timeout",
                    "repair_hints": [{
                        "kind": "high_difficulty_assertions",
                        "hard_axioms": [axiom],
                        "rarely_instantiated": [axiom],
                    }, {
                        "kind": "need_rewrite",
                        "detail": "should become matching_weak",
                    }],
                },
            ],
            "last_screen": [
                {"lemma": lib_dup, "reason": "already_in_library:L3", "gate": "same_as_library"},
                {"lemma": "(bad)", "reason": "known", "gate": "known_invalid"},
            ],
            "repair_hints": [{"kind": "need_rewrite", "detail": "stale global"}],
        },
        backend="cvc5",
    )
    assert "LAST ATTEMPT" in txt
    assert "status=timeout" in txt
    assert kept in txt
    assert older not in txt
    assert "Combination 2" not in txt
    assert "Do not emit the exact same set" not in txt
    assert "already in lemma library L3" in txt
    assert "known_invalid" not in txt
    assert "(bad)" not in txt
    assert "repair hints:" in txt
    assert "high-difficulty axiom:" in txt
    assert HD_DIFFICULTY_EXPLAIN in txt
    assert "advice: TRIGGER" in txt
    assert HD_AXIOM_GOAL_HINT not in txt
    assert "rarely instantiated:" in txt
    assert "matching_weak:" not in txt
    assert "need_rewrite" not in txt
    assert "should become matching_weak" not in txt
    assert "stale global" not in txt
    assert "You may refine kept lemmas or propose a different set." in txt

    initial = format_attempt_feedback_for_prompt(
        {
            "repair_hints": [{
                "kind": "high_difficulty_assertions",
                "hard_axioms": [axiom],
            }],
        },
        backend="cvc5",
    )
    assert "INITIAL SOLVE" in initial
    assert "high-difficulty axiom:" in initial
    assert HD_DIFFICULTY_EXPLAIN in initial
    assert HD_AXIOM_GOAL_HINT in initial
    hidden = format_attempt_feedback_for_prompt(
        {
            "useless_lemma_groups": [{"lemmas": [kept], "status": "timeout"}],
            "repair_hints": [{"kind": "need_rewrite", "detail": "hidden"}],
        },
        backend="cvc5",
        include_stuck=False,
    )
    assert "LAST ATTEMPT" in hidden
    assert "matching_weak" not in hidden
    assert "hidden" not in hidden


def test_node_attempt_plan_child_cap() -> None:
    pack = resolve_prompt_pack("default", 3)
    with patch.dict(os.environ, {"CHILD_LLM_ATTEMPTS": "2"}):
        assert node_attempt_plan(1, pack) == (2, 1)
    with patch.dict(os.environ, {"CHILD_LLM_ATTEMPTS": "0"}):
        assert node_attempt_plan(1, pack) == (6, 3)
    with patch.dict(os.environ, {"CHILD_LLM_ATTEMPTS": "2"}):
        assert node_attempt_plan(0, pack) == (6, 3)


def test_llm_parse_retries_env() -> None:
    with patch.dict(os.environ, {"LLM_PARSE_RETRIES": "2"}):
        assert llm_parse_retries() == 2
    with patch.dict(os.environ, {"LLM_PARSE_RETRIES": "0"}):
        assert llm_parse_retries() == 0
    with patch.dict(os.environ, {"LLM_PARSE_RETRIES": ""}):
        assert llm_parse_retries() == 2
    with patch.dict(os.environ, {"LLM_PARSE_RETRIES": "nope"}):
        assert llm_parse_retries() == 2
    msgs = [
        {"role": "system", "content": "s"},
        {"role": "user", "content": "u"},
    ]
    hinted = with_parse_retry_hint(msgs, "forgot the tags")
    assert hinted[-2]["role"] == "assistant"
    assert "forgot the tags" in hinted[-2]["content"]
    assert hinted[-1]["role"] == "user"
    assert "<output>" in hinted[-1]["content"]
    assert hinted[0] is not msgs[0]


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
    assert not repair_hint_for_prompt({"kind": "need_rewrite", "context": "initial_goal"})
    assert not repair_hint_for_prompt({"kind": "no_progress", "context": "usefulness_check"})
    assert not repair_hint_for_prompt({"kind": "partial_progress", "context": "usefulness_check"})
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
            "LEMMA_FILTER_DROP": "on",
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


def test_quick_run_drops_undefined_keeps_snoc() -> None:
    import Mate_new_vampire as mate
    from vampire_runner import VampireResult

    timeout = VampireResult(status="timeout", proved=False, elapsed=0.01)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "LEMMA_DEFINED_SYMBOLS": "on",
            "LEMMA_FILTER_DROP": "on",
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY_LOCAL": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm",
            return_value=[PLUS_LEMMA, SNOC_LEMMA],
        ), patch("Mate_new_vampire.run_vampire", return_value=timeout), patch(
            "Mate_new_vampire.verify_combined_lemmas",
            return_value=(False, [], timeout),
        ) as useful:
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is False
        assert subgoals == []
        assert lemmas == [SNOC_LEMMA]
        useful.assert_called()
        useful_lemmas = useful.call_args.args[1]
        assert useful_lemmas == [SNOC_LEMMA]
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert any("undefined_symbol:plus" in str(item.get("reason")) for item in invalid)
        assert all("snoc" not in str(item.get("lemma") or "").lower() for item in invalid)


def test_quick_run_library_duplicate_retries_goal_not_invalid() -> None:
    import Mate_new_vampire as mate
    from obligation_tree import add_proved_lemma

    snoc_alpha = (
        "(forall ((xs Lst) (n Nat)) (= (len (append xs (cons n nil))) (succ (len xs))))"
    )
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "LEMMA_LIBRARY": "on",
            "LEMMA_LIBRARY_LOCAL": "off",
            "LEMMA_DEFINED_SYMBOLS": "on",
            "LEMMA_FILTER_DROP": "on",
            "SOLVER_ROUTING": "off",
        }):
            add_proved_lemma(tmp, SNOC_LEMMA, origin="seed")
            with patch(
                "Mate_new_vampire.generate_lemmas_with_llm",
                return_value=[snoc_alpha],
            ), patch(
                "Mate_new_vampire.perform_initial_verification", return_value=False
            ) as retry, patch(
                "Mate_new_vampire.verify_combined_lemmas"
            ) as useful, patch("Mate_new_vampire.run_vampire") as vampire:
                proved, subgoals, lemmas = mate.quick_run(
                    tmp, "template", "p", "./prompts_ours"
                )
        assert proved is False
        assert subgoals == []
        assert lemmas == [snoc_alpha]
        useful.assert_not_called()
        vampire.assert_not_called()
        retry.assert_called()
        assert retry.call_args.kwargs.get("log_event") == "library_retry"
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert invalid == []


def test_quick_run_filter_drop_off_aborts_whole_group() -> None:
    import Mate_new_vampire as mate

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        with patch.dict(os.environ, {
            "LEMMA_DEFINED_SYMBOLS": "on",
            "LEMMA_FILTER_DROP": "off",
            "SOLVER_ROUTING": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm",
            return_value=[PLUS_LEMMA, SNOC_LEMMA],
        ), patch("Mate_new_vampire.run_vampire") as vampire, patch(
            "Mate_new_vampire.verify_combined_lemmas"
        ) as useful:
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is False
        assert subgoals == []
        assert lemmas == [PLUS_LEMMA, SNOC_LEMMA]
        vampire.assert_not_called()
        useful.assert_not_called()
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert any("undefined_symbol:plus" in str(item.get("reason")) for item in invalid)


def test_quick_run_skips_known_invalid_without_solver() -> None:
    import Mate_new_vampire as mate

    spaced = "  " + PLUS_LEMMA.replace(" ", "  ") + "\n"
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        data = mate.load_failed_lemmas(tmp, "template")
        data["invalid_lemmas"] = [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]
        mate.save_failed_lemmas(tmp, "template", data)
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "LEMMA_FILTER_DROP": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm",
            return_value=[spaced, SNOC_LEMMA],
        ), patch("Mate_new_vampire.run_vampire") as vampire:
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is False
        assert subgoals == []
        assert lemmas == [spaced, SNOC_LEMMA]
        vampire.assert_not_called()
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert invalid == [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]


def test_quick_run_drops_known_invalid_keeps_other() -> None:
    import Mate_new_vampire as mate
    from vampire_runner import VampireResult

    timeout = VampireResult(status="timeout", proved=False, elapsed=0.01)
    spaced = "  " + PLUS_LEMMA.replace(" ", "  ") + "\n"
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        data = mate.load_failed_lemmas(tmp, "template")
        data["invalid_lemmas"] = [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]
        mate.save_failed_lemmas(tmp, "template", data)
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "LEMMA_DEFINED_SYMBOLS": "on",
            "LEMMA_FILTER_DROP": "on",
            "LEMMA_LIBRARY_LOCAL": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm",
            return_value=[spaced, SNOC_LEMMA],
        ), patch("Mate_new_vampire.run_vampire", return_value=timeout), patch(
            "Mate_new_vampire.verify_combined_lemmas",
            return_value=(False, [], timeout),
        ) as useful:
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is False
        assert lemmas == [SNOC_LEMMA]
        useful.assert_called()
        assert useful.call_args.args[1] == [SNOC_LEMMA]
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert invalid[0]["reason"] == "plus has no axioms"


def test_quick_run_does_not_skip_unrelated_lemma() -> None:
    import Mate_new_vampire as mate
    from vampire_runner import VampireResult

    timeout = VampireResult(status="timeout", proved=False, elapsed=0.01)
    overlapping = PLUS_LEMMA + " (P a)"
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(P2_SMT, encoding="utf-8")
        data = mate.load_failed_lemmas(tmp, "template")
        data["invalid_lemmas"] = [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]
        mate.save_failed_lemmas(tmp, "template", data)
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "LEMMA_DEFINED_SYMBOLS": "off",
        }), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", return_value=[overlapping]
        ), patch("Mate_new_vampire.run_vampire", return_value=timeout) as vampire:
            mate.quick_run(tmp, "template", "p", "./prompts_ours")
        vampire.assert_called()
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert invalid[0]["reason"] == "plus has no axioms"


def test_add_invalid_lemma_keeps_original_reason() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        mate.add_invalid_lemma(tmp, "template", PLUS_LEMMA, "plus has no axioms")
        mate.add_invalid_lemma(
            tmp, "template", "  " + PLUS_LEMMA + "\n", "undefined_symbol:plus"
        )
        invalid = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert invalid == [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]


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
        assert "INVALID_GOAL: <short explanation>" not in root[1]["content"]
        assert DIAGNOSIS_PROMPT_SUFFIX.strip() in child[1]["content"]
        assert "emit <output></output>" in child[1]["content"]
        assert "previously proposed child lemma is marked invalid" in child[1]["content"]
        final, _ = mate.create_prompt(
            _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
            "./prompts_ours", depth=1, diagnosis_only=True,
        )
        assert FINAL_DIAGNOSIS_PROMPT_SUFFIX.strip() in final[1]["content"]
        assert "do not use <lemma> tags" in final[1]["content"]
        assert "FINAL CHECK" in final[1]["content"]
        assert "propose different lemmas" not in final[1]["content"]
        assert "Using INVALID child lemmas" in final[1]["content"]
        assert "output invalid" in final[1]["content"]
        assert "output failed." in final[1]["content"]
        assert "obligation tree" not in final[1]["content"]
        assert "still_open" not in final[1]["content"]
        assert "prior attempts" not in final[1]["content"]
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "off"}):
            child_off, _ = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1,
            )
        assert "INVALID_GOAL: <short explanation>" not in child_off[1]["content"]


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


class _InvalidGoalOnlyReply:
    content = (
        "The CURRENT goal uses plus, which is only declared.\n"
        "; INVALID_GOAL: plus has no axioms\n"
    )


class _CotReasonOnlyReply:
    content = (
        "The inductive case fails.\n"
        "reason: the IH does not match the conclusion.\n"
    )


def _run_generate_lemmas(
    fake_llm,
    *,
    retries: str = "2",
    diagnosis_only: bool = False,
    mod_name: str = "Mate_new",
    depth: int = 1,
):
    mate = __import__(mod_name)
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "LLM_LEMMA_DIAGNOSIS": "on",
            "LLM_PARSE_RETRIES": retries,
        }), patch(
            f"{mod_name}.create_prompt",
            return_value=(
                [{"role": "system", "content": "s"}, {"role": "user", "content": "u"}],
                {},
            ),
        ), patch(f"{mod_name}.llm", fake_llm):
            lemmas = mate.generate_lemmas_with_llm(
                _GOAL,
                "p",
                smt,
                tmp,
                "template",
                "./prompts_ours",
                depth=depth,
                diagnosis_only=diagnosis_only,
            )
            stored = mate.load_failed_lemmas(tmp, "template").get("last_llm_reason", "")
    return lemmas, stored


def test_generate_reason_without_markers_stores_reason() -> None:
    for mod_name in ("Mate_new", "Mate_new_vampire"):
        mate = __import__(mod_name)
        fake_llm = MagicMock()
        fake_llm.invoke.return_value = _InvalidGoalOnlyReply()
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
            with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on", "LLM_PARSE_RETRIES": "0"}), patch(
                f"{mod_name}.create_prompt",
                return_value=(
                    [
                        {"role": "system", "content": "s"},
                        {"role": "user", "content": "u"},
                    ],
                    {},
                ),
            ), patch(f"{mod_name}.llm", fake_llm):
                lemmas = mate.generate_lemmas_with_llm(
                    _GOAL,
                    "prove_prompt_equational_reasoning",
                    Path(tmp) / "template.smt2",
                    tmp,
                    "template",
                    "./prompts_ours",
                    depth=1,
                )
            assert lemmas == []
            stored = mate.load_failed_lemmas(tmp, "template").get("last_llm_reason", "")
            assert "plus" in stored, mod_name


def test_generate_unmarked_without_reason_still_raises() -> None:
    import Mate_new as mate

    class Fake:
        content = "I will propose lemmas but forgot the markers."

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = Fake()
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on", "LLM_PARSE_RETRIES": "0"}), patch(
            "Mate_new.create_prompt",
            return_value=(
                [{"role": "system", "content": "s"}, {"role": "user", "content": "u"}],
                {},
            ),
        ), patch("Mate_new.llm", fake_llm):
            raised = False
            try:
                mate.generate_lemmas_with_llm(
                    _GOAL,
                    "p",
                    Path(tmp) / "template.smt2",
                    tmp,
                    "template",
                    "./prompts_ours",
                    depth=1,
                )
            except ValueError as exc:
                raised = True
                assert "输出标记" in str(exc)
            assert raised


def test_parse_retry_recovers_on_second_call() -> None:
    class Unmarked:
        content = "I will propose lemmas but forgot the markers."

    class Fixed:
        content = f"<output>\n<lemma>{SNOC_LEMMA}</lemma>\n</output>\n"

    for mod_name in ("Mate_new", "Mate_new_vampire"):
        mate = __import__(mod_name)
        fake_llm = MagicMock()
        fake_llm.invoke.side_effect = [Unmarked(), Fixed()]
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
            with patch.dict(os.environ, {
                "LLM_LEMMA_DIAGNOSIS": "on",
                "LLM_PARSE_RETRIES": "1",
            }), patch(
                f"{mod_name}.create_prompt",
                return_value=(
                    [
                        {"role": "system", "content": "s"},
                        {"role": "user", "content": "u"},
                    ],
                    {},
                ),
            ), patch(f"{mod_name}.llm", fake_llm):
                lemmas = mate.generate_lemmas_with_llm(
                    _GOAL,
                    "p",
                    Path(tmp) / "template.smt2",
                    tmp,
                    "template",
                    "./prompts_ours",
                    depth=1,
                )
        assert lemmas == [SNOC_LEMMA], mod_name
        assert fake_llm.invoke.call_count == 2, mod_name
        retry_messages = fake_llm.invoke.call_args_list[1][0][0]
        assert retry_messages[-2]["role"] == "assistant"
        assert "forgot the markers" in retry_messages[-2]["content"]
        assert retry_messages[-1]["role"] == "user"
        assert "<output>" in retry_messages[-1]["content"]


def test_parse_retry_exhausted_still_raises() -> None:
    class Unmarked:
        content = "I will propose lemmas but forgot the markers."

    for mod_name in ("Mate_new", "Mate_new_vampire"):
        fake_llm = MagicMock()
        fake_llm.invoke.return_value = Unmarked()
        raised = False
        try:
            _run_generate_lemmas(fake_llm, retries="1", mod_name=mod_name)
        except ValueError as exc:
            raised = True
            assert "输出标记" in str(exc)
        assert raised, mod_name
        assert fake_llm.invoke.call_count == 2, mod_name


def test_parse_retry_default_budget_is_three_calls() -> None:
    class Unmarked:
        content = "I will propose lemmas but forgot the markers."

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = Unmarked()
    raised = False
    try:
        _run_generate_lemmas(fake_llm, retries="2")
    except ValueError:
        raised = True
    assert raised
    assert fake_llm.invoke.call_count == 3


def test_empty_output_does_parse_retry() -> None:
    class Empty:
        content = "<output></output>\n"

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = Empty()
    raised = False
    try:
        _run_generate_lemmas(fake_llm, retries="2")
    except ValueError as exc:
        raised = True
        assert str(exc) == PARSE_ERR_EMPTY
    assert raised
    assert fake_llm.invoke.call_count == 3


def test_empty_output_with_invalid_goal_stores_reason() -> None:
    class TaggedInvalid:
        content = (
            "<output></output>\n"
            "; INVALID_GOAL: plus has no axioms\n"
        )

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = TaggedInvalid()
    lemmas, stored = _run_generate_lemmas(fake_llm, retries="2")
    assert lemmas == []
    assert "plus" in stored
    assert fake_llm.invoke.call_count == 1


def test_api_error_does_not_parse_retry() -> None:
    fake_llm = MagicMock()
    fake_llm.invoke.side_effect = RuntimeError("api down")
    raised = False
    try:
        _run_generate_lemmas(fake_llm, retries="2")
    except RuntimeError as exc:
        raised = True
        assert "api down" in str(exc)
    assert raised
    assert fake_llm.invoke.call_count == 1


def test_final_diagnosis_does_not_parse_retry() -> None:
    class Prose:
        content = "not a structured verdict"

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = Prose()
    lemmas, stored = _run_generate_lemmas(
        fake_llm, retries="2", diagnosis_only=True,
    )
    assert lemmas == []
    assert stored == "failed"
    assert fake_llm.invoke.call_count == 1


def test_parse_retry_does_not_consume_extra_attempt() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    class Unmarked:
        content = "I will propose lemmas but forgot the markers."

    class TaggedInvalid:
        content = (
            "<output></output>\n"
            "; INVALID_GOAL: plus has no axioms\n"
        )

    fake_llm = MagicMock()
    fake_llm.invoke.side_effect = [Unmarked(), TaggedInvalid()]
    real_gen = mate.generate_lemmas_with_llm
    gen_calls = {"n": 0}

    def counting(*args, **kwargs):
        gen_calls["n"] += 1
        return real_gen(*args, **kwargs)

    timeout = CvcResult(status="timeout", proved=False, elapsed=0.05)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "LLM_LEMMA_DIAGNOSIS": "on",
            "LLM_PARSE_RETRIES": "1",
            "CHILD_LLM_ATTEMPTS": "2",
            "SUBGOAL_SAT_ABORT": "off",
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY": "off",
        }), patch("Mate_new.run_cvc_routed", return_value=timeout), patch(
            "Mate_new.llm", fake_llm
        ), patch("Mate_new.generate_lemmas_with_llm", counting):
            ok = mate.prove_run(tmp, "template", depth=1)
        outcome = mate.load_failed_lemmas(tmp, "template")["node_outcome"]
    assert ok is False
    assert gen_calls["n"] == 1
    assert fake_llm.invoke.call_count == 2
    assert outcome.get("kind") == "invalid"
    assert "plus" in outcome.get("reason", "")


def test_lemma_prompt_xml_contract() -> None:
    packs = [
        ROOT / "prompts_ours" / "prove_prompt_equational_reasoning",
        ROOT / "prompts_ours" / "prove_prompt_term_rewrite",
        ROOT / "prompts_naive" / "prompt_naive",
    ]
    for folder in packs:
        system = (folder / "system_prompt.txt").read_text(encoding="utf-8")
        user = (folder / "user_prompt.txt").read_text(encoding="utf-8")
        assert "<output>" in system, folder.name
        assert "<lemma>" in system, folder.name
        assert "If you output no lemmas, still emit" not in system, folder.name
        assert "wrapped in <input></input>" in system, folder.name
        assert "; Output begin" not in system, folder.name
        assert "; Input begin" not in system, folder.name
        assert "fill the content between comments" not in system, folder.name
        assert "<input>" in user, folder.name
        assert "</input>" in user, folder.name
        assert "; Input begin" not in user, folder.name
        assert "; Output begin" not in user, folder.name


def test_generate_cot_reason_without_tag_still_raises() -> None:
    import Mate_new as mate

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = _CotReasonOnlyReply()
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on", "LLM_PARSE_RETRIES": "0"}), patch(
            "Mate_new.create_prompt",
            return_value=(
                [{"role": "system", "content": "s"}, {"role": "user", "content": "u"}],
                {},
            ),
        ), patch("Mate_new.llm", fake_llm):
            raised = False
            try:
                mate.generate_lemmas_with_llm(
                    _GOAL,
                    "p",
                    Path(tmp) / "template.smt2",
                    tmp,
                    "template",
                    "./prompts_ours",
                    depth=1,
                )
            except ValueError as exc:
                raised = True
                assert "输出标记" in str(exc)
            assert raised
            stored = mate.load_failed_lemmas(tmp, "template").get("last_llm_reason", "")
            assert stored == ""


def test_empty_output_cot_reason_does_not_store_invalid() -> None:
    import Mate_new as mate

    class Fake:
        content = (
            "; Output begin\n\n; Output end\n"
            "reason: the IH does not match the conclusion.\n"
        )

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = Fake()
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": "on", "LLM_PARSE_RETRIES": "0"}), patch(
            "Mate_new.create_prompt",
            return_value=(
                [{"role": "system", "content": "s"}, {"role": "user", "content": "u"}],
                {},
            ),
        ), patch("Mate_new.llm", fake_llm):
            raised = False
            try:
                mate.generate_lemmas_with_llm(
                    _GOAL,
                    "p",
                    Path(tmp) / "template.smt2",
                    tmp,
                    "template",
                    "./prompts_ours",
                    depth=1,
                )
            except ValueError as exc:
                raised = True
                assert str(exc) == PARSE_ERR_EMPTY
            assert raised
        stored = mate.load_failed_lemmas(tmp, "template").get("last_llm_reason", "")
        assert stored == ""


def test_root_tree_prompt_does_not_ask_to_judge_goal_invalid() -> None:
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
    judge = "judge whether the CURRENT goal is also invalid"
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        data = mate._empty_failed_data()
        data["obligation"] = append_attempt({}, "obligation_tree", tree)
        data["invalid_lemmas"] = [{"lemma": PLUS_LEMMA, "reason": "plus has no axioms"}]
        mate.save_failed_lemmas(tmp, "template", data)
        with patch.dict(os.environ, {
            "OBLIGATION_TREE": "on",
            "LEMMA_LIBRARY": "off",
            "LLM_LEMMA_DIAGNOSIS": "on",
            "FEEDBACK_REPAIR_HINTS": "off",
        }):
            root, root_extra = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=0,
            )
            child, child_extra = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1,
            )
            final, final_extra = mate.create_prompt(
                _GOAL, "prove_prompt_equational_reasoning", tmp, "template",
                "./prompts_ours", depth=1, diagnosis_only=True,
            )
        assert "L1  invalid [plus has no axioms]" in root_extra
        assert judge not in root[1]["content"]
        assert judge not in root_extra
        assert judge in child_extra
        assert judge in child[1]["content"]
        assert "INVALID_GOAL: <short explanation>" in child[1]["content"]
        assert "Invalid lemma 1 (plus has no axioms)" in final_extra
        assert "Last obligation tree" not in final_extra
        assert "INVALID_GOAL: <short explanation>" in final[1]["content"]
        assert "Using INVALID child lemmas" in final[1]["content"]


def test_cvc5_unmarked_reason_marks_child_invalid() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    fake_llm = MagicMock()
    fake_llm.invoke.return_value = _InvalidGoalOnlyReply()
    timeout = CvcResult(status="timeout", proved=False, elapsed=0.05)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "LLM_LEMMA_DIAGNOSIS": "on",
            "SUBGOAL_SAT_ABORT": "off",
            "SOLVER_ROUTING": "off",
            "LEMMA_LIBRARY": "off",
            "CHILD_LLM_ATTEMPTS": "2",
        }), patch("Mate_new.run_cvc_routed", return_value=timeout), patch(
            "Mate_new.create_prompt",
            return_value=(
                [{"role": "system", "content": "s"}, {"role": "user", "content": "u"}],
                {},
            ),
        ), patch("Mate_new.llm", fake_llm):
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        assert fake_llm.invoke.call_count == 1
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
        with patch.dict(os.environ, {"OBLIGATION_TREE": "on"}):
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
                "context": "initial_goal",
                "detail": "root stuck",
                "suggested_actions": [],
            },
            {
                "kind": "induction_stuck",
                "context": "subgoal:template_1",
                "detail": "child stuck",
                "suggested_actions": ["weaken"],
            },
            {
                "kind": "need_arithmetic_lemma",
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
    assert "root stuck" in txt
    assert "root rewrite" not in txt
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

    def fake_parallel(base_path, *_args, **_kwargs):
        mate.add_invalid_lemma(
            base_path, "template", PLUS_LEMMA, "plus has no axioms",
        )
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
            "OBLIGATION_TREE": "off",
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


def test_final_diagnosis_prompt_is_invalid_only() -> None:
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
        assert "Using INVALID child lemmas" in text
        assert "Invalid lemma 1 (plus has no axioms)" in extra
        assert "The following lemmas are INVALID or CANNOT" in extra
        assert "Last obligation tree" not in extra
        assert "L1  invalid" not in extra
        assert "USEFUL BUT UNPROVED" not in text
        assert "USEFUL BUT UNPROVED" not in extra
        assert "SOLVER-GUIDED REPAIR" not in extra
        assert "root rewrite" not in extra
        assert "Previous empty output reason" not in text
        assert "Previous empty output reason" not in gen_extra
        assert "The following lemmas are INVALID or CANNOT" in gen_extra
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

    def fake_parallel(base_path, *_args, **_kwargs):
        mate.add_invalid_lemma(
            base_path, "template", PLUS_LEMMA, "plus has no defining axioms",
        )
        return False, [child]

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
            "OBLIGATION_TREE": "off",
        }), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch(
            "Mate_new_vampire.quick_run", side_effect=fake_quick
        ), patch(
            "Mate_new_vampire.prove_subgoals_parallel",
            side_effect=fake_parallel,
        ), patch(
            "Mate_new_vampire.generate_lemmas_with_llm", side_effect=fake_gen
        ):
            ok = mate.prove_run(tmp, "template", depth=1)
        assert ok is False
        outcome = mate.load_failed_lemmas(tmp, "template")["node_outcome"]
        assert outcome.get("kind") == "invalid"
        assert "plus" in outcome.get("reason", "")
        assert outcome.get("source") == "llm_final"


def test_final_diagnosis_skipped_without_invalid() -> None:
    import Mate_new_vampire as mate

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
            "OBLIGATION_TREE": "off",
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
        assert mate.load_failed_lemmas(tmp, "template").get("invalid_lemmas") in ([], None)
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
    test_lemma_same_as_goal_alpha()
    test_drop_failing_members_keeps_rest()
    test_static_screen_drops_undefined_keeps_defined()
    test_static_screen_drops_library_alpha_keeps_rest()
    test_known_invalid_match_whitespace_not_substring()
    test_unproved_dedup_whitespace_and_alpha()
    test_add_unproved_lemma_dedups_equivalent()
    test_situation_a_dual_writes_revival_not_into_child_pending()
    test_promote_child_pending_skips_library_blocking_timeout()
    test_promote_inherits_child_revival_not_deeper_files()
    test_parse_llm_reason()
    test_parse_llm_lemmas_xml_and_legacy()
    test_parse_llm_lemmas_salvage_and_paren_repair()
    test_repair_header_lists_usefulness_lemmas()
    test_last_attempt_omits_lemma_difficulty_tags()
    test_stale_lemma_usage_json_is_not_prompted()
    test_last_attempt_prompt_keeps_latest_group_and_drops()
    test_node_attempt_plan_child_cap()
    test_llm_parse_retries_env()
    test_tree_status_sat_is_invalid()
    test_tree_status_nested_invalid_does_not_mark_parent()
    test_repair_hint_for_prompt_drops_subgoal_atp()
    test_quick_run_rejects_undefined_plus()
    test_quick_run_drops_undefined_keeps_snoc()
    test_quick_run_library_duplicate_retries_goal_not_invalid()
    test_quick_run_filter_drop_off_aborts_whole_group()
    test_quick_run_skips_known_invalid_without_solver()
    test_quick_run_drops_known_invalid_keeps_other()
    test_sat_aborts_child_without_llm()
    test_diagnosis_suffix_flag()
    test_should_append_diagnosis_by_depth()
    test_child_empty_reason_stops_attempts()
    test_generate_reason_without_markers_stores_reason()
    test_generate_unmarked_without_reason_still_raises()
    test_parse_retry_recovers_on_second_call()
    test_parse_retry_exhausted_still_raises()
    test_parse_retry_default_budget_is_three_calls()
    test_empty_output_does_parse_retry()
    test_empty_output_with_invalid_goal_stores_reason()
    test_api_error_does_not_parse_retry()
    test_final_diagnosis_does_not_parse_retry()
    test_parse_retry_does_not_consume_extra_attempt()
    test_lemma_prompt_xml_contract()
    test_generate_cot_reason_without_tag_still_raises()
    test_empty_output_cot_reason_does_not_store_invalid()
    test_root_tree_prompt_does_not_ask_to_judge_goal_invalid()
    test_cvc5_unmarked_reason_marks_child_invalid()
    test_invalid_child_records_invalid_not_unproved()
    test_cancelled_invalid_child_keeps_reason()
    test_prompt_invalid_not_unproved_and_drops_child_atp()
    test_invalid_child_does_not_stop_parent_attempts()
    test_final_diagnosis_prompt_is_invalid_only()
    test_final_diagnosis_marks_goal_invalid()
    test_final_diagnosis_skipped_without_invalid()
    test_final_diagnosis_skipped_at_root()
    print("lemma gate tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
