#!/usr/bin/env python3
"""Lemma library, last-normal-tree selection, and compressed prompt text."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from obligation_tree import (
    add_proved_lemma,
    append_attempt,
    classify_failed_attempt,
    compact_atp_from_failed_data,
    format_diagnosis_tree_prompt,
    format_obligation_prompt,
    inject_library_axioms,
    first_invalid_reason,
    last_normal_tree,
    lemma_library_enabled,
    lemma_library_path,
    load_lemma_library,
    make_child_node,
    make_goal_tree,
    materialize_smt_with_library,
    obligation_tree_enabled,
    render_obligation_tree,
    solver_smt_content,
)


def test_library_dedup_and_ids(tmp_path: Path) -> None:
    formula = "(forall ((x Nat)) (= (plus x zero) x))"
    with _patch_flags("on", "on"):
        first = add_proved_lemma(str(tmp_path), formula, origin="template_1", attempt=2, depth=1)
        second = add_proved_lemma(
            str(tmp_path),
            "(forall  ((x   Nat))  (= (plus x zero) x))",
            origin="template_3",
            attempt=4,
            depth=1,
        )
        other = add_proved_lemma(
            str(tmp_path),
            "(forall ((x Nat) (y Nat)) (= (plus x y) (plus y x)))",
            origin="template_2",
            attempt=2,
            depth=1,
        )
        assert first == "lib_1"
        assert second == "lib_1"
        assert other == "lib_2"
        stored = load_lemma_library(str(tmp_path))
        assert [item["id"] for item in stored] == ["lib_1", "lib_2"]


def test_last_normal_tree_skips_empty_invalid_useless() -> None:
    state = {}
    state = append_attempt(state, "empty")
    state = append_attempt(state, "invalid")
    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula="(forall ((x Nat)) (= (plus x zero) x))",
                status="proved",
                lib="lib_1",
            ),
            make_child_node(
                node_id="template_2",
                formula="(forall ((x Nat) (y Nat)) (= (plus x y) (plus y x)))",
                status="failed",
                atp={"hints": ["need_rewrite"], "focus": ["(plus x y)"]},
                children=[
                    make_child_node(
                        node_id="template_2_1",
                        formula="(forall ((x Nat)) (= (plus zero x) x))",
                        status="proved",
                        lib="lib_2",
                    ),
                    make_child_node(
                        node_id="template_2_2",
                        formula="(forall ((x Nat) (y Nat)) (= (plus y x) (plus x y)))",
                        status="cancelled",
                    ),
                ],
            ),
        ],
        proved=False,
    )
    state = append_attempt(state, "obligation_tree", tree)
    state = append_attempt(state, "empty")
    state = append_attempt(state, "useless")
    found = last_normal_tree(state)
    assert found is not None
    assert found["children"][0]["lib"] == "lib_1"
    assert found["children"][1]["status"] == "failed"
    assert state["last_normal_tree_id"] == 3


def test_classify_failed_attempt() -> None:
    lemmas = ["(forall ((x Nat)) (= x x))"]
    assert classify_failed_attempt([], {}) == "empty"
    assert classify_failed_attempt(lemmas, {"invalid_lemmas": [{"lemma": lemmas[0]}]}) == "invalid"
    assert classify_failed_attempt(
        lemmas,
        {"useless_lemma_groups": [{"lemmas": lemmas, "status": "timeout"}]},
    ) == "useless"


def test_inject_library_axioms_before_proof_goal() -> None:
    smt = """(set-logic ALL)
; proof goal
(assert (not (forall ((x Nat)) true)))
; proof goal end
(check-sat)
"""
    out = inject_library_axioms(
        smt,
        [{"id": "lib_1", "formula": "(forall ((x Nat)) (= (plus x zero) x))"}],
    )
    assert "; proved lemma library" in out
    assert "(assert (forall ((x Nat)) (= (plus x zero) x)))" in out
    assert out.index("; proved lemma library") < out.index("; proof goal")
    again = inject_library_axioms(out, [{"id": "lib_1", "formula": "(forall ((x Nat)) (= (plus x zero) x))"}])
    assert again.count("; proved lemma library end") == 1


def test_compressed_prompt_matches_expected_shape() -> None:
    library = [
        {"id": "lib_1", "formula": "(forall ((x Nat)) (= (plus x zero) x))"},
        {"id": "lib_2", "formula": "(forall ((x Nat)) (= (plus zero x) x))"},
    ]
    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula="(forall ((x Nat)) (= (plus x zero) x))",
                status="proved",
                lib="lib_1",
            ),
            make_child_node(
                node_id="template_2",
                formula="(forall ((x Nat) (y Nat)) (= (plus x y) (plus y x)))",
                status="failed",
                atp={"hints": ["need_rewrite"], "focus": ["(plus x y)"]},
                children=[
                    make_child_node(
                        node_id="template_2_1",
                        formula="(forall ((x Nat)) (= (plus zero x) x))",
                        status="proved",
                        lib="lib_2",
                    ),
                    make_child_node(
                        node_id="template_2_2",
                        formula="(forall ((x Nat) (y Nat)) (= (plus y x) (plus x y)))",
                        status="cancelled",
                    ),
                ],
            ),
        ],
        proved=False,
    )
    obligation = append_attempt({}, "obligation_tree", tree)
    with _patch_flags("on", "on"):
        text = format_obligation_prompt(library, obligation)
    assert "Library (already proved, in axioms):" in text
    assert "lib_1: (forall ((x Nat)) (= (plus x zero) x))" in text
    assert "Last obligation tree (attempt 1; for reference only):" in text
    assert "G  open" in text
    assert "├─ lib_1  proved" in text
    assert "└─ L2  failed" in text
    assert "need_rewrite" not in text
    assert "lib_2  proved" in text
    assert "L2_2  cancelled" in text
    assert "CURRENT goal" in text
    rendered = "\n".join(render_obligation_tree(tree))
    assert "│  " in rendered or "   ├─" in rendered or "   └─" in rendered


def test_first_invalid_reason_walks_nested() -> None:
    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula="(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))",
                status="failed",
                children=[
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
            ),
        ],
        proved=False,
    )
    assert first_invalid_reason(tree) == "plus has no defining axioms"
    assert first_invalid_reason({"status": "open", "children": []}) == ""


def test_invalid_node_shows_reason_not_atp_hints() -> None:
    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula="(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))",
                status="invalid",
                reason="undefined_symbol:plus",
                atp={"hints": ["need_rewrite"], "focus": ["(plus x y)"]},
            ),
        ],
        proved=False,
    )
    obligation = append_attempt({}, "obligation_tree", tree)
    with _patch_flags("off", "on"):
        text = format_obligation_prompt([], obligation)
    assert "L1  invalid [undefined_symbol:plus]" in text
    assert "need_rewrite" not in text
    assert "do not weaken" in text
    assert "Child invalid: use its reason to judge whether the CURRENT goal is also invalid." in text


def test_diagnosis_tree_prompt_omits_library_and_generation_legend() -> None:
    library = [{"id": "lib_1", "formula": "(forall ((x Nat)) (= x x))"}]
    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula="(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))",
                status="invalid",
                reason="plus has no axioms",
            ),
        ],
        proved=False,
    )
    obligation = append_attempt({}, "obligation_tree", tree)
    with _patch_flags("on", "on"):
        text = format_diagnosis_tree_prompt(obligation)
        mixed = format_obligation_prompt(library, obligation, for_diagnosis=True)
    assert "Last obligation tree" in text
    assert "L1  invalid [plus has no axioms]" in text
    assert "do not propose lemmas" in text
    assert "generate lemmas for the CURRENT goal only" not in text
    assert "Library (already proved, in axioms):" not in text
    assert "lib_1" not in mixed
    assert "Library (already proved, in axioms):" not in mixed


def test_compact_atp_keeps_actionable_hints() -> None:
    atp = compact_atp_from_failed_data({
        "repair_hints": [
            {
                "kind": "timeout",
                "detail": "timeout",
                "induction_focus": [],
            },
            {
                "kind": "need_rewrite",
                "detail": "need rewrite",
                "induction_focus": ["(plus x y)", "(plus y x)"],
            },
            {
                "kind": "induction_stuck",
                "detail": "stuck",
                "induction_focus": ["(plus x y)"],
            },
        ]
    })
    assert atp["hints"] == ["need_rewrite", "induction_stuck"]
    assert atp["focus"] == ["(plus x y)", "(plus y x)"]


def _patch_flags(library: str, tree: str):
    return patch.dict(os.environ, {
        "LEMMA_LIBRARY": library,
        "OBLIGATION_TREE": tree,
    })


def _sample_obligation():
    tree = make_goal_tree(
        "template",
        [
            make_child_node(
                node_id="template_1",
                formula="(forall ((x Nat)) (= (plus x zero) x))",
                status="proved",
                lib="lib_1",
            ),
            make_child_node(
                node_id="template_2",
                formula="(forall ((x Nat) (y Nat)) (= (plus x y) (plus y x)))",
                status="failed",
                atp={"hints": ["need_rewrite"], "focus": ["(plus x y)"]},
            ),
        ],
        proved=False,
    )
    library = [{"id": "lib_1", "formula": "(forall ((x Nat)) (= (plus x zero) x))"}]
    return library, append_attempt({}, "obligation_tree", tree)


def test_flags_default_on_and_off_synonyms() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("LEMMA_LIBRARY", None)
        os.environ.pop("OBLIGATION_TREE", None)
        assert lemma_library_enabled() is True
        assert obligation_tree_enabled() is True
    for val in ("on", "ON", "true", "1", "yes"):
        with _patch_flags(val, val):
            assert lemma_library_enabled() is True
            assert obligation_tree_enabled() is True
    for val in ("off", "0", "false", "no"):
        with _patch_flags(val, "on"):
            assert lemma_library_enabled() is False
            assert obligation_tree_enabled() is True
        with _patch_flags("on", val):
            assert lemma_library_enabled() is True
            assert obligation_tree_enabled() is False


def test_library_flag_controls_persist_and_inject() -> None:
    smt = """(set-logic ALL)
; proof goal
(assert (not (forall ((x Nat)) true)))
; proof goal end
"""
    formula = "(forall ((x Nat)) (= (plus x zero) x))"
    with tempfile.TemporaryDirectory() as tmp:
        smt_path = Path(tmp) / "template.smt2"
        smt_path.write_text(smt, encoding="utf-8")
        with _patch_flags("off", "on"):
            assert add_proved_lemma(tmp, formula, origin="template_1") is None
            assert not lemma_library_path(tmp).exists()
            assert solver_smt_content(smt, tmp) == smt
            assert materialize_smt_with_library(smt_path, tmp) == smt_path
        with _patch_flags("on", "off"):
            assert add_proved_lemma(tmp, formula, origin="template_1") == "lib_1"
            assert lemma_library_path(tmp).exists()
            injected = solver_smt_content(smt, tmp)
            assert "(assert (forall ((x Nat)) (= (plus x zero) x)))" in injected
            assert injected.index("; proved lemma library") < injected.index("; proof goal")
            out = materialize_smt_with_library(smt_path, tmp)
            assert out != smt_path
            assert "; proved lemma library" in out.read_text(encoding="utf-8")
        with _patch_flags("off", "on"):
            # leftover file must not be injected when the library flag is off
            assert solver_smt_content(smt, tmp) == smt
            assert materialize_smt_with_library(smt_path, tmp) == smt_path


def test_prompt_flags_distinguish_library_and_tree() -> None:
    library, obligation = _sample_obligation()
    with _patch_flags("on", "on"):
        both = format_obligation_prompt(library, obligation)
        assert "Library (already proved, in axioms):" in both
        assert "lib_1:" in both
        assert "Last obligation tree" in both
        assert "G  open" in both
        assert "L2  failed" in both
    with _patch_flags("off", "on"):
        tree_only = format_obligation_prompt(library, obligation)
        assert "Library (already proved, in axioms):" not in tree_only
        assert "lib_1:" not in tree_only
        assert "Last obligation tree" in tree_only
        assert "G  open" in tree_only
        assert "LEMMA LIBRARY:" not in tree_only
    with _patch_flags("on", "off"):
        lib_only = format_obligation_prompt(library, obligation)
        assert "Library (already proved, in axioms):" in lib_only
        assert "lib_1:" in lib_only
        assert "Last obligation tree" not in lib_only
        assert "G  open" not in lib_only
        assert "L2  failed" not in lib_only
    with _patch_flags("off", "off"):
        assert format_obligation_prompt(library, obligation) == ""


def test_mate_feedback_and_recording_respect_flags() -> None:
    import Mate_new as mate

    library, obligation = _sample_obligation()
    formula = "(forall ((x Nat)) (= (plus x zero) x))"
    payload = {
        "repair_hints": [],
        "invalid_lemmas": [],
        "useless_lemma_groups": [],
        "progress_lemmas": [],
        "unproved_lemmas": [],
        "routing": {},
        "obligation": obligation,
    }
    with tempfile.TemporaryDirectory() as tmp:
        with _patch_flags("on", "on"):
            add_proved_lemma(tmp, formula, origin="template_1")
            both = mate.format_solver_feedback_for_prompt(payload, base_path=tmp)
            assert "Library (already proved, in axioms):" in both
            assert "Last obligation tree" in both
        with _patch_flags("off", "on"):
            tree_only = mate.format_solver_feedback_for_prompt(payload, base_path=tmp)
            assert "Library (already proved, in axioms):" not in tree_only
            assert "Last obligation tree" in tree_only
        with _patch_flags("on", "off"):
            lib_only = mate.format_solver_feedback_for_prompt(payload, base_path=tmp)
            assert "Library (already proved, in axioms):" in lib_only
            assert "Last obligation tree" not in lib_only
        with _patch_flags("off", "off"):
            neither = mate.format_solver_feedback_for_prompt(payload, base_path=tmp)
            assert "Library (already proved, in axioms):" not in neither
            assert "Last obligation tree" not in neither
            assert "OBLIGATION HISTORY" not in neither

        with _patch_flags("on", "off"):
            mate._record_obligation_attempt(tmp, "template", "empty")
            data = mate.load_failed_lemmas(tmp, "template")
            assert (data.get("obligation") or {}).get("attempts") in ([], None)
        with _patch_flags("off", "on"):
            node = mate._child_obligation_node(
                tmp, "template_1", formula, "proved", depth=1, attempt=1
            )
            assert node["lib"] is None
            # file may exist from earlier on-library add; do not add a new id
            before = load_lemma_library(tmp)
            node2 = mate._child_obligation_node(
                tmp, "template_2", "(forall ((y Nat)) (= y y))", "proved",
                depth=1, attempt=1,
            )
            assert node2["lib"] is None
            assert load_lemma_library(tmp) == before
        with _patch_flags("on", "on"):
            mate._record_obligation_attempt(tmp, "template", "empty")
            data = mate.load_failed_lemmas(tmp, "template")
            kinds = [a["kind"] for a in data["obligation"]["attempts"]]
            assert "empty" in kinds
            node = mate._child_obligation_node(
                tmp, "template_3", "(forall ((z Nat)) (= z z))", "proved",
                depth=1, attempt=2,
            )
            assert node["lib"]
            assert any(item["formula"] == "(forall ((z Nat)) (= z z))" for item in load_lemma_library(tmp))


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        test_library_dedup_and_ids(Path(tmp))
    test_last_normal_tree_skips_empty_invalid_useless()
    test_classify_failed_attempt()
    test_inject_library_axioms_before_proof_goal()
    test_compressed_prompt_matches_expected_shape()
    test_first_invalid_reason_walks_nested()
    test_invalid_node_shows_reason_not_atp_hints()
    test_diagnosis_tree_prompt_omits_library_and_generation_legend()
    test_compact_atp_keeps_actionable_hints()
    test_flags_default_on_and_off_synonyms()
    test_library_flag_controls_persist_and_inject()
    test_prompt_flags_distinguish_library_and_tree()
    test_mate_feedback_and_recording_respect_flags()
    print("obligation tree tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
