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
    harvest_retry_timeout_s,
    invalid_lemma_records,
    invalid_lemmas_enabled,
    last_normal_tree,
    lemma_library_enabled,
    lemma_library_path,
    lemma_library_role,
    load_lemma_library,
    local_lemma_harvest_enabled,
    scheme_helpers_in_text,
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


def test_library_dedup_alpha_renaming(tmp_path: Path) -> None:
    with _patch_flags("on", "on"):
        first = add_proved_lemma(
            str(tmp_path),
            "(forall ((x Nat)) (= (plus x zero) x))",
            origin="template_1",
        )
        second = add_proved_lemma(
            str(tmp_path),
            "(forall ((y Nat)) (= (plus y zero) y))",
            origin="template_2",
        )
        assert first == "lib_1"
        assert second == "lib_1"
        assert len(load_lemma_library(str(tmp_path))) == 1


def test_add_proved_lemma_drops_equivalent_unproved(tmp_path: Path) -> None:
    import json

    proved = "(forall ((x Nat)) (= (plus x zero) x))"
    alpha = "(forall ((y Nat)) (= (plus y zero) y))"
    other = "(forall ((x Nat) (y Nat)) (= (plus x y) (plus y x)))"
    invalid_keep = "(forall ((x Nat)) false)"
    (tmp_path / "failed_lemmas.json").write_text(
        json.dumps({
            "invalid_lemmas": [{"lemma": invalid_keep, "reason": "unsat"}],
            "unproved_lemmas": [
                {"lemma": proved, "status": "timeout"},
                {"lemma": other, "status": "timeout"},
            ],
            "revival_lemmas": [
                {"lemma": proved, "origin": "situation_a", "status": "timeout"},
                {"lemma": other, "origin": "child_pending", "status": "timeout"},
            ],
        }),
        encoding="utf-8",
    )
    (tmp_path / "failed_lemmas_1.json").write_text(
        json.dumps({
            "unproved_lemmas": [
                {"lemma": alpha, "status": "unknown"},
                {"lemma": other, "status": "timeout"},
            ],
            "revival_lemmas": [
                {"lemma": alpha, "origin": "situation_a", "status": "unknown"},
                {"lemma": other, "origin": "child_pending", "status": "timeout"},
            ],
        }),
        encoding="utf-8",
    )
    with _patch_flags("on", "on"):
        assert add_proved_lemma(str(tmp_path), proved, origin="template_1") == "lib_1"
    root = json.loads((tmp_path / "failed_lemmas.json").read_text(encoding="utf-8"))
    child = json.loads((tmp_path / "failed_lemmas_1.json").read_text(encoding="utf-8"))
    assert [item["lemma"] for item in root["unproved_lemmas"]] == [other]
    assert [item["lemma"] for item in root["revival_lemmas"]] == [other]
    assert root["invalid_lemmas"] == [{"lemma": invalid_keep, "reason": "unsat"}]
    assert [item["lemma"] for item in child["unproved_lemmas"]] == [other]
    assert [item["lemma"] for item in child["revival_lemmas"]] == [other]


def test_add_proved_lemma_drops_unproved_when_library_off(tmp_path: Path) -> None:
    import json

    proved = "(forall ((x Nat)) (= (plus x zero) x))"
    (tmp_path / "failed_lemmas.json").write_text(
        json.dumps({"unproved_lemmas": [{"lemma": proved, "status": "timeout"}]}),
        encoding="utf-8",
    )
    with _patch_flags("off", "on"):
        assert add_proved_lemma(str(tmp_path), proved) is None
    out = json.loads((tmp_path / "failed_lemmas.json").read_text(encoding="utf-8"))
    assert out["unproved_lemmas"] == []
    assert not lemma_library_path(str(tmp_path)).exists()


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


def test_inject_scheme_prelude_and_skip_undeclared_helpers() -> None:
    """Measure pins must inject declare-fun; polluted rows without prelude are skipped."""
    smt = """(set-logic ALL)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun len (Lst) Nat)
; proof goal
(assert (not true))
; proof goal end
"""
    prelude = (
        "; induction scheme Nat→Int for measure comparisons\n"
        "(declare-fun __scheme_nat_to_int (Nat) Int)\n"
        "(assert (= (__scheme_nat_to_int zero) 0))\n"
        "(assert (forall ((__n Nat)) "
        "(= (__scheme_nat_to_int (succ __n)) (+ 1 (__scheme_nat_to_int __n)))))\n"
    )
    formula = "(forall ((x Lst)) (>= (__scheme_nat_to_int (len x)) 0))"
    good = {
        "id": "lib_1",
        "formula": formula,
        "prelude": prelude,
    }
    polluted = {
        "id": "lib_2",
        "formula": "(forall ((y Lst)) (= (__scheme_nat_to_int (len y)) "
                   "(__scheme_nat_to_int (len y))))",
        # no prelude — old bug shape
    }
    unrelated = {
        "id": "lib_3",
        "formula": "(forall ((n Nat)) (= n n))",
    }
    # Only polluted: must skip so wellformed SMT stays clean.
    polluted_only = inject_library_axioms(smt, [polluted, unrelated])
    assert "(declare-fun __scheme_nat_to_int" not in polluted_only
    assert "; lib_2" not in polluted_only
    assert "; lib_3" in polluted_only
    assert "(forall ((n Nat)) (= n n))" in polluted_only

    # With a prelude-bearing pin, helpers are declared once; siblings may reuse.
    out = inject_library_axioms(smt, [good, polluted, unrelated])
    assert "(declare-fun __scheme_nat_to_int (Nat) Int)" in out
    assert out.count("(declare-fun __scheme_nat_to_int") == 1
    assert "; lib_1" in out
    assert "; lib_2" in out  # declared via shared prelude from lib_1
    assert "; lib_3" in out
    assert scheme_helpers_in_text("(forall ((n Nat)) (= n n))") == []


def test_inject_upgrades_ufdt_when_int_measure_prelude() -> None:
    """UFDT + __scheme_list_len→Int must become UFDTLIA so CVC parse-only works."""
    smt = """(set-logic UFDT)
(declare-datatypes ((nat 0)) (((zero) (succ (pred nat)))))
(declare-datatypes ((list 0)) (((nil) (cons (head nat) (tail list)))))
(declare-fun append (list list) list)
; proof goal
(assert (not (forall ((ys list)) (= (append ys nil) ys))))
; proof goal end
"""
    prelude = (
        "(declare-fun __scheme_list_len (list) Int)\n"
        "(assert (= (__scheme_list_len nil) 0))\n"
        "(assert (forall ((__x nat) (__xs list)) "
        "(= (__scheme_list_len (cons __x __xs)) (+ 1 (__scheme_list_len __xs)))))\n"
    )
    # Pin that carries Int prelude (scheme measure) plus an Int-free sibling lemma.
    lemmas = [
        {
            "id": "lib_1",
            "formula": "(forall ((xs list)) (>= (__scheme_list_len xs) 0))",
            "prelude": prelude,
        },
        {
            "id": "lib_2",
            "formula": "(forall ((ys list)) (= (append ys nil) ys))",
        },
    ]
    out = inject_library_axioms(smt, lemmas)
    assert "(set-logic UFDTLIA)" in out
    assert "(set-logic UFDT)" not in out
    assert "(declare-fun __scheme_list_len (list) Int)" in out
    # Innocent lemma still present for screening / prove.
    assert "(forall ((ys list)) (= (append ys nil) ys))" in out

    # Without upgrade this is the user-reported false parse_error.
    from cvc5_runner import check_lemma_wellformed

    innocent = "(forall ((ys list)) (= (append ys nil) ys))"
    # Background without upgrade (raw UFDT + Int prelude) fails.
    poisoned = smt.replace(
        "; proof goal",
        "; proved lemma library\n" + prelude + "; proved lemma library end\n; proof goal",
    )
    bad = check_lemma_wellformed(innocent, poisoned)
    assert not bad.ok, bad
    assert "Int" in (bad.message or "")

    # Injected background (upgraded) must accept the same lemma.
    good = check_lemma_wellformed(innocent, out)
    assert good.ok, good


def test_ensure_smt_logic_for_arith_noop_when_already_lia() -> None:
    from obligation_tree import ensure_smt_logic_for_arith

    smt = "(set-logic UFDTLIA)\n(assert true)\n"
    assert ensure_smt_logic_for_arith(smt, need_int=True, need_real=False) == smt
    assert ensure_smt_logic_for_arith(
        "(set-logic ALL)\n", need_int=True, need_real=True,
    ) == "(set-logic ALL)\n"
    assert "(set-logic UFDTLIA)" in ensure_smt_logic_for_arith(
        "(set-logic UFDT)\n", need_int=True, need_real=False,
    )


def test_add_proved_lemma_stores_prelude() -> None:
    prelude = "(declare-fun __scheme_nat_to_int (Nat) Int)\n"
    formula = "(forall ((x Nat)) (>= (__scheme_nat_to_int x) 0))"
    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"LEMMA_LIBRARY": "on"}):
            lib_id = add_proved_lemma(
                tmp, formula, origin="scheme:g:nonneg", role="pin", prelude=prelude,
            )
            assert lib_id == "lib_1"
            items = load_lemma_library(tmp)
            assert items[0]["prelude"].strip().startswith("(declare-fun __scheme_nat_to_int")
            # α-dup without prelude attaches stored prelude.
            lib_id2 = add_proved_lemma(
                tmp, formula, origin="scheme:g:again", role="pin", prelude="",
            )
            assert lib_id2 == "lib_1"
            # Promote path: pin with prelude fills empty.
            items[0]["prelude"] = ""
            from obligation_tree import save_lemma_library
            save_lemma_library(tmp, items)
            add_proved_lemma(
                tmp, formula, origin="scheme:g:fix", role="pin", prelude=prelude,
            )
            assert load_lemma_library(tmp)[0]["prelude"].strip().startswith(
                "(declare-fun __scheme_nat_to_int"
            )


def test_obligation_prompt_shows_library_prelude() -> None:
    library = [
        {
            "id": "lib_1",
            "formula": "(forall ((x Nat)) (>= (__scheme_nat_to_int x) 0))",
            "prelude": (
                "(declare-fun __scheme_nat_to_int (Nat) Int)\n"
                "(assert (= (__scheme_nat_to_int zero) 0))\n"
            ),
        },
    ]
    with _patch_flags("on", "off"):
        text = format_obligation_prompt(library, None)
    assert "Scheme measure prelude (definition in SMT axioms):" in text
    assert "(declare-fun __scheme_nat_to_int (Nat) Int)" in text
    assert "lib_1:" in text


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
    assert "judge whether the CURRENT goal is also invalid" not in text
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
        child = format_obligation_prompt([], obligation, depth=1)
        diag = format_obligation_prompt([], obligation, for_diagnosis=True)
    assert "L1  invalid [undefined_symbol:plus]" in text
    assert "need_rewrite" not in text
    assert "do not weaken" in text
    assert "judge whether the CURRENT goal is also invalid" not in text
    assert "judge whether the CURRENT goal is also invalid" in child
    assert "judge whether the CURRENT goal is also invalid" in diag


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
    with _patch_flags("on", "off"):
        assert format_diagnosis_tree_prompt(obligation) == ""
    assert "Last obligation tree" in text
    assert "L1  invalid [plus has no axioms]" in text
    assert "do not propose lemmas" in text
    assert "judge whether the CURRENT goal is also invalid" in text
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
        "LEMMA_LIBRARY_LOCAL": "on",
    })


def _formula(i: int) -> str:
    return f"(forall ((x Nat)) (= (f{i} x) x))"


def test_library_has_no_size_cap(tmp_path: Path) -> None:
    with _patch_flags("on", "on"):
        pin_ids = [
            add_proved_lemma(str(tmp_path), _formula(i), role="pin")
            for i in range(12)
        ]
        local_id = add_proved_lemma(str(tmp_path), _formula(99), role="local")
        extra_local = add_proved_lemma(str(tmp_path), _formula(100), role="local")
        extra_pin = add_proved_lemma(str(tmp_path), _formula(101), role="pin")
        assert all(pin_ids)
        assert local_id and extra_local and extra_pin
        stored = load_lemma_library(str(tmp_path))
        assert len(stored) == 15
        roles = [lemma_library_role(item) for item in stored]
        assert roles.count("pin") == 13
        assert roles.count("local") == 2
        ids = [item["id"] for item in stored]
        assert local_id in ids and extra_local in ids and extra_pin in ids


def test_library_no_fifo_when_harvest_off(tmp_path: Path) -> None:
    with patch.dict(os.environ, {
        "LEMMA_LIBRARY": "on",
        "OBLIGATION_TREE": "on",
        "LEMMA_LIBRARY_LOCAL": "off",
    }):
        ids = [
            add_proved_lemma(str(tmp_path), _formula(i), role="pin")
            for i in range(15)
        ]
        assert all(ids)
        stored = load_lemma_library(str(tmp_path))
        assert len(stored) == 15
        assert [item["id"] for item in stored] == [f"lib_{i}" for i in range(1, 16)]


def test_library_promote_local_to_pin_keeps_id(tmp_path: Path) -> None:
    formula = _formula(1)
    with _patch_flags("on", "on"):
        local_id = add_proved_lemma(str(tmp_path), formula, role="local")
        pin_id = add_proved_lemma(str(tmp_path), formula, role="pin")
        assert local_id == pin_id == "lib_1"
        stored = load_lemma_library(str(tmp_path))
        assert len(stored) == 1
        assert lemma_library_role(stored[0]) == "pin"


def test_library_missing_role_is_pin(tmp_path: Path) -> None:
    import json
    path = lemma_library_path(str(tmp_path))
    lemmas = [
        {"id": f"lib_{i}", "formula": _formula(i), "status": "proved"}
        for i in range(1, 13)
    ]
    path.write_text(json.dumps({"lemmas": lemmas}), encoding="utf-8")
    with _patch_flags("on", "on"):
        local_id = add_proved_lemma(str(tmp_path), _formula(99), role="local")
        stored = load_lemma_library(str(tmp_path))
        assert local_id == "lib_13"
        assert len(stored) == 13
        assert all(lemma_library_role(item) == "pin" for item in stored[:12])
        assert lemma_library_role(stored[-1]) == "local"


def test_local_harvest_flag_blocks_local_insert(tmp_path: Path) -> None:
    with patch.dict(os.environ, {
        "LEMMA_LIBRARY": "on",
        "LEMMA_LIBRARY_LOCAL": "off",
    }):
        assert local_lemma_harvest_enabled() is False
        assert add_proved_lemma(str(tmp_path), _formula(1), role="local") is None
        assert add_proved_lemma(str(tmp_path), _formula(1), role="pin") == "lib_1"


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


def test_flags_default_and_off_synonyms() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("LEMMA_LIBRARY", None)
        os.environ.pop("OBLIGATION_TREE", None)
        os.environ.pop("INVALID_LEMMAS", None)
        assert lemma_library_enabled() is True
        assert obligation_tree_enabled() is True
        assert invalid_lemmas_enabled() is True
    for val in ("on", "ON", "true", "1", "yes"):
        with _patch_flags(val, val):
            assert lemma_library_enabled() is True
            assert obligation_tree_enabled() is True
        with patch.dict(os.environ, {"INVALID_LEMMAS": val}):
            assert invalid_lemmas_enabled() is True
    for val in ("off", "0", "false", "no"):
        with _patch_flags(val, "on"):
            assert lemma_library_enabled() is False
            assert obligation_tree_enabled() is True
        with _patch_flags("on", val):
            assert lemma_library_enabled() is True
            assert obligation_tree_enabled() is False
        with patch.dict(os.environ, {"INVALID_LEMMAS": val}):
            assert invalid_lemmas_enabled() is False


def test_invalid_lemmas_flag_gates_write_prompt_and_screen() -> None:
    """Module-2 INVALID_LEMMAS: off ⇒ hard+soft memory ignored for write/prompt/screen."""
    import Mate_new as mate
    from lemma_gates import (
        apply_static_lemma_screen,
        format_diagnosis_invalid_prompt,
        format_soft_rejected_prompt,
        lemma_same_as_goal,
    )
    from obligation_tree import soft_rejected_lemma_records

    bad = "(forall ((x Nat)) false)"
    soft_lem = "(forall ((x Nat)) (= (f x) x))"
    other = "(forall ((x Nat)) (= x x))"
    stale = {
        "invalid_lemmas": [{"lemma": bad, "reason": "stale"}],
        "soft_rejected_lemmas": [
            {"lemma": soft_lem, "reason": "Same as original goal", "gate": "same_as_goal"},
        ],
        "useless_lemma_groups": [],
        "progress_lemmas": [],
        "repair_hints": [],
        "routing": {},
    }
    screen_env = {"LEMMA_WELLFORMED_CHECK": "off", "LEMMA_DEFINED_SYMBOLS": "off"}
    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"INVALID_LEMMAS": "on", **screen_env}):
            mate.add_invalid_lemma(tmp, "template", bad, "contradicts")
            mate.add_soft_rejected_lemma(
                tmp, "template", soft_lem, "Same as original goal", gate="same_as_goal",
            )
            data = mate.load_failed_lemmas(tmp, "template")
            assert len(data["invalid_lemmas"]) == 1
            assert len(data["soft_rejected_lemmas"]) == 1
            assert invalid_lemma_records(stale) and soft_rejected_lemma_records(stale)
            prompt_on = mate.format_solver_feedback_for_prompt(stale)
            assert "INVALID:" in prompt_on
            assert "NODE-LOCAL SUPPRESSIONS" in prompt_on
            assert "INVALID:" in format_diagnosis_invalid_prompt(stale)
            assert format_soft_rejected_prompt(stale)
            kept, dropped = apply_static_lemma_screen(
                [bad, soft_lem, other],
                original_forall="(forall ((z Nat)) true)",
                smt="(set-logic ALL)\n",
                invalid_records=invalid_lemma_records(stale),
                soft_rejected_records=soft_rejected_lemma_records(stale),
                same_as_goal=lemma_same_as_goal,
            )
            assert kept == [other]
            gates = {g for _l, _r, g in dropped}
            assert "known_invalid" in gates and "known_soft_rejected" in gates

        with patch.dict(os.environ, {"INVALID_LEMMAS": "off", **screen_env}):
            mate.add_invalid_lemma(tmp, "template2", "(forall ((y Nat)) false)", "x")
            mate.add_soft_rejected_lemma(
                tmp, "template2", soft_lem, "Same as original goal", gate="same_as_goal",
            )
            data2 = mate.load_failed_lemmas(tmp, "template2")
            assert data2["invalid_lemmas"] == []
            assert data2.get("soft_rejected_lemmas", []) == []
            assert invalid_lemma_records(stale) == []
            assert soft_rejected_lemma_records(stale) == []
            prompt = mate.format_solver_feedback_for_prompt(stale)
            assert "INVALID:" not in prompt
            assert "NODE-LOCAL SUPPRESSIONS" not in prompt
            assert format_diagnosis_invalid_prompt(stale) == ""
            assert format_soft_rejected_prompt(stale) == ""
            kept2, dropped2 = apply_static_lemma_screen(
                [bad, soft_lem, other],
                original_forall="(forall ((z Nat)) true)",
                smt="(set-logic ALL)\n",
                invalid_records=[{"lemma": bad, "reason": "stale"}],
                soft_rejected_records=[
                    {"lemma": soft_lem, "reason": "Same as original goal", "gate": "same_as_goal"},
                ],
                same_as_goal=lemma_same_as_goal,
            )
            assert bad in kept2 and soft_lem in kept2 and other in kept2
            assert not any(
                g in ("known_invalid", "known_soft_rejected") for _l, _r, g in dropped2
            )


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


def test_harvest_retry_timeout_s_default_and_override() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("HARVEST_RETRY_TIMEOUT", None)
        assert harvest_retry_timeout_s() == 2
    with patch.dict(os.environ, {"HARVEST_RETRY_TIMEOUT": "5"}):
        assert harvest_retry_timeout_s() == 5
    with patch.dict(os.environ, {"HARVEST_RETRY_TIMEOUT": "0"}):
        assert harvest_retry_timeout_s() == 1
    with patch.dict(os.environ, {"HARVEST_RETRY_TIMEOUT": "bogus"}):
        assert harvest_retry_timeout_s() == 2


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for i, fn in enumerate((
            test_library_dedup_and_ids,
            test_library_dedup_alpha_renaming,
            test_library_has_no_size_cap,
            test_library_no_fifo_when_harvest_off,
            test_library_promote_local_to_pin_keeps_id,
            test_library_missing_role_is_pin,
            test_local_harvest_flag_blocks_local_insert,
        )):
            d = root / str(i)
            d.mkdir()
            fn(d)
    test_last_normal_tree_skips_empty_invalid_useless()
    test_classify_failed_attempt()
    test_inject_library_axioms_before_proof_goal()
    test_inject_scheme_prelude_and_skip_undeclared_helpers()
    test_inject_upgrades_ufdt_when_int_measure_prelude()
    test_ensure_smt_logic_for_arith_noop_when_already_lia()
    test_add_proved_lemma_stores_prelude()
    test_obligation_prompt_shows_library_prelude()
    test_compressed_prompt_matches_expected_shape()
    test_first_invalid_reason_walks_nested()
    test_invalid_node_shows_reason_not_atp_hints()
    test_diagnosis_tree_prompt_omits_library_and_generation_legend()
    test_compact_atp_keeps_actionable_hints()
    test_harvest_retry_timeout_s_default_and_override()
    test_flags_default_and_off_synonyms()
    test_invalid_lemmas_flag_gates_write_prompt_and_screen()
    test_library_flag_controls_persist_and_inject()
    test_prompt_flags_distinguish_library_and_tree()
    test_mate_feedback_and_recording_respect_flags()
    print("obligation tree tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
