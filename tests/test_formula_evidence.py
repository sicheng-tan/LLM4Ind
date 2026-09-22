#!/usr/bin/env python3
"""Difficulty + ``-o lemmas`` formula evidence (FEEDBACK_FORMULA_EVIDENCE)."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from cvc5_runner import (
    CvcResult,
    FORMULA_EVIDENCE_KIND,
    _cvc_prove_cmd,
    _fun_jaccard,
    _relevance_term,
    cvc_profile_specs,
    derive_repair_hints,
    parse_cvc_lemmas,
    select_formula_evidence_samples,
)
from lemma_gates import (
    FORMULA_EVIDENCE_EXPLAIN,
    compact_repair_snapshot,
    format_attempt_feedback_for_prompt,
)

DROP_AXIOM = "(forall ((x Lst)) (= x (drop 0 x)))"
DROP_INST = (
    "(=> (forall ((x Lst)) (= x (drop 0 x))) "
    "(= @quantifiers_skolemize_3 (drop 0 @quantifiers_skolemize_3)))"
)
LEN_INST = (
    "(=> (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))) "
    "(= (len (cons 0 nil)) (+ 1 (len nil))))"
)
GOAL = "(not (forall ((n Int) (xs Lst)) (= (len (drop n xs)) n)))"
SPLIT = "(or (= @quantifiers_skolemize_15 (- 1)) (not (= @quantifiers_skolemize_15 (- 1))))"
DROP_REC = (
    "(forall ((x Int) (y Int) (z Lst)) "
    "(or (not (>= x 0)) (= (drop x z) (drop (+ 1 x) (cons y z)))))"
)
DROP_REC_INST = (
    "(=> (forall ((x Int) (y Int) (z Lst)) "
    "(or (not (>= x 0)) (= (drop x z) (drop (+ 1 x) (cons y z))))) "
    "(or (not (>= 0 0)) (= (drop 0 nil) (drop 1 (cons 0 nil)))))"
)
LEN_AXIOM = "(forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y))))"
MINUS_AXIOM = (
    "(forall ((n Int) (m Int)) "
    "(=> (and (>= n 0) (>= m 0)) (= (minus n m) (ite (< n m) 0 (- n m)))))"
)
MINUS_INST = (
    "(=> (forall ((n Int) (m Int)) "
    "(=> (and (>= n 0) (>= m 0)) (= (minus n m) (ite (< n m) 0 (- n m))))) "
    "(= (minus (len nil) 0) 0))"
)
SKOLEM_GOAL = (
    "(let ((_let_1 (>= @quantifiers_skolemize_1 0))) "
    "(or (forall ((n Int) (xs Lst)) "
    "(or (not (>= n 0)) (= (len (drop n xs)) (minus (len xs) n)))) "
    "(not (or _let_1 (forall ((BOUND_VARIABLE_1 Lst)) "
    "(= (len (drop (+ (- 1) @quantifiers_skolemize_1) BOUND_VARIABLE_1)) "
    "(minus (len BOUND_VARIABLE_1) (+ (- 1) @quantifiers_skolemize_1))))))))"
)
assert len(SKOLEM_GOAL) > 240
DROP_INST_B = (
    "(=> (forall ((x Lst)) (= x (drop 0 x))) "
    "(= @quantifiers_skolemize_9 (drop 0 @quantifiers_skolemize_9)))"
)


def test_parse_cvc_lemmas_skips_splits_and_keeps_source() -> None:
    text = "\n".join([
        f"(lemma {DROP_INST} :source QUANTIFIERS_INST_CBQI_PROP)",
        f"(lemma {SPLIT} :source COMBINATION_SPLIT)",
        f"(lemma {LEN_INST} :source QUANTIFIERS_INST_E_MATCHING)",
        "unknown",
    ])
    items = parse_cvc_lemmas(text)
    sources = {item["source"] for item in items}
    assert "COMBINATION_SPLIT" not in sources
    assert "QUANTIFIERS_INST_CBQI_PROP" in sources
    assert "QUANTIFIERS_INST_E_MATCHING" in sources
    assert any("drop 0" in item["formula"] for item in items)


def test_cmd_lemmas_only_when_flag_on() -> None:
    cfg = cvc_profile_specs()["cvc5_simple"]
    off = _cvc_prove_cmd(
        cfg, Path("x.smt2"), 60, collect_stats=True, collect_difficulty=True,
    )
    assert "lemmas" not in off
    with patch.dict(os.environ, {"FEEDBACK_FORMULA_EVIDENCE": "on"}):
        on = _cvc_prove_cmd(
            cfg, Path("x.smt2"), 60, collect_stats=True, collect_difficulty=True,
        )
        probe = _cvc_prove_cmd(
            cfg, Path("x.smt2"), 2, collect_stats=True, collect_difficulty=False,
        )
    assert on.count("-o") >= 2
    assert "lemmas" in on
    assert "inst" in on
    assert "lemmas" not in probe


def test_select_matches_quantifier_and_caps() -> None:
    result = CvcResult(
        status="unknown",
        strategy="cvc5_inductive",
        goal_term=GOAL,
        difficulty=[(DROP_AXIOM, 12), (GOAL, 3)],
        lemmas=[
            {"formula": DROP_INST, "source": "QUANTIFIERS_INST_CBQI_PROP"},
            {"formula": LEN_INST, "source": "QUANTIFIERS_INST_E_MATCHING"},
            {
                "formula": "(=> (forall ((x Int)) (= x x)) (= 1 1))",
                "source": "QUANTIFIERS_INST_E_MATCHING",
            },
            {
                "formula": "(=> ((_ is cons) t) (= t (cons (head t) (tail t))))",
                "source": "DATATYPES_INST",
            },
        ],
    )
    samples = select_formula_evidence_samples(result)
    assert 1 <= len(samples) <= 4
    matched = [s for s in samples if s["relation"] == "matched_quantifier"]
    assert matched, samples
    assert any(DROP_AXIOM in (s.get("related_axiom") or "") for s in matched)
    assert all(s.get("profile") == "cvc5_inductive" for s in samples)


def test_relevance_uses_instance_not_quantifier_prefix() -> None:
    inst_term, scope = _relevance_term(DROP_INST)
    assert scope == "instance"
    assert "forall" not in inst_term
    assert "drop 0" in inst_term
    r_inst = _fun_jaccard(inst_term, GOAL)
    r_full = _fun_jaccard(DROP_INST, GOAL)
    # Whole implication also contains drop, so scores may be close; instance
    # must not be empty and must ignore the copied axiom prefix's bound vars.
    assert r_inst > 0
    assert r_inst <= r_full + 1e-9


def test_shared_symbols_do_not_inherit_difficulty() -> None:
    result = CvcResult(
        status="unknown",
        strategy="cvc5_inductive",
        goal_term=GOAL,
        difficulty=[(DROP_REC, 8000)],
        lemmas=[{"formula": LEN_INST, "source": "QUANTIFIERS_INST_E_MATCHING"}],
    )
    samples = select_formula_evidence_samples(result)
    assert samples
    row = samples[0]
    assert row["relation"] == "shared_symbols"
    assert row["hotspot_known"] is False
    assert row["origin_hotness"] == 0.0


def test_selection_prefers_instances_over_early_skolem() -> None:
    result = CvcResult(
        status="unknown",
        strategy="cvc5_inductive",
        goal_term=GOAL,
        difficulty=[
            (DROP_REC, 135),
            (LEN_AXIOM, 53),
            (MINUS_AXIOM, 23),
            (DROP_AXIOM, 13),
        ],
        lemmas=[
            {"formula": SKOLEM_GOAL, "source": "QUANTIFIERS_SKOLEMIZE"},
            {"formula": SKOLEM_GOAL.replace("BOUND_VARIABLE_1", "BOUND_VARIABLE_2"),
             "source": "QUANTIFIERS_SKOLEMIZE"},
            {"formula": DROP_INST, "source": "QUANTIFIERS_INST_CBQI_PROP"},
            {"formula": DROP_INST_B, "source": "QUANTIFIERS_INST_CBQI_PROP"},
            {"formula": LEN_INST, "source": "QUANTIFIERS_INST_E_MATCHING"},
            {"formula": DROP_REC_INST, "source": "QUANTIFIERS_INST_E_MATCHING"},
            {"formula": MINUS_INST, "source": "QUANTIFIERS_INST_E_MATCHING"},
        ],
    )
    samples = select_formula_evidence_samples(result)
    assert 1 <= len(samples) <= 4
    skolem_n = sum(1 for s in samples if "SKOLEMIZE" in (s.get("source") or ""))
    assert skolem_n <= 1, samples
    formulas = "\n".join(s["formula"] for s in samples)
    assert "drop 0" in formulas or "len (cons" in formulas or "minus" in formulas
    matched = [s for s in samples if s["relation"] == "matched_quantifier"]
    assert matched, samples
    drop_zero = [
        s for s in samples
        if s["relation"] == "matched_quantifier" and DROP_AXIOM in (s.get("related_axiom") or "")
    ]
    assert len(drop_zero) <= 1, samples
    for s in samples:
        assert "selection_score" in s
        assert 0.0 <= s["selection_score"] <= 1.0 + 1e-9


def test_prompt_omits_selection_scores() -> None:
    result = CvcResult(
        status="timeout",
        strategy="cvc5_inductive",
        elapsed=1.0,
        goal_term=GOAL,
        difficulty=[(DROP_AXIOM, 9)],
        lemmas=[{"formula": DROP_INST, "source": "QUANTIFIERS_INST_CBQI_PROP"}],
    )
    with patch.dict(os.environ, {"FEEDBACK_FORMULA_EVIDENCE": "on"}):
        hints = derive_repair_hints(result, context="usefulness_check")
    sample = next(h for h in hints if h["kind"] == FORMULA_EVIDENCE_KIND)["samples"][0]
    assert "selection_score" in sample
    txt = format_attempt_feedback_for_prompt({"repair_hints": hints}, backend="cvc5")
    assert "selection_score" not in txt
    assert "goal_relevance" not in txt
    assert "origin_hotness" not in txt
    assert "0.6" not in txt


def test_derive_and_prompt_gated_by_flag() -> None:
    result = CvcResult(
        status="timeout",
        strategy="cvc5_inductive",
        elapsed=1.0,
        goal_term=GOAL,
        difficulty=[(DROP_AXIOM, 9)],
        lemmas=[{"formula": DROP_INST, "source": "QUANTIFIERS_INST_CBQI_PROP"}],
    )
    off_hints = derive_repair_hints(result, context="usefulness_check")
    assert all(h["kind"] != FORMULA_EVIDENCE_KIND for h in off_hints)
    with patch.dict(os.environ, {"FEEDBACK_FORMULA_EVIDENCE": "on"}):
        hints = derive_repair_hints(result, context="usefulness_check")
    kinds = [h["kind"] for h in hints]
    assert "high_difficulty_assertions" in kinds
    assert FORMULA_EVIDENCE_KIND in kinds
    evidence = next(h for h in hints if h["kind"] == FORMULA_EVIDENCE_KIND)
    hd = next(h for h in hints if h["kind"] == "high_difficulty_assertions")
    assert evidence.get("attempt_id") == hd.get("attempt_id")
    snap = compact_repair_snapshot(hints)
    assert any(h.get("samples") for h in snap if h.get("kind") == FORMULA_EVIDENCE_KIND)
    txt = format_attempt_feedback_for_prompt(
        {"repair_hints": snap}, backend="cvc5",
    )
    assert "selected solver formulas:" in txt
    assert "drop 0" in txt
    assert FORMULA_EVIDENCE_EXPLAIN in txt
    assert "instance of the hotspot assertion" in txt


def test_stale_hotspot_not_shown_with_new_samples() -> None:
    txt = format_attempt_feedback_for_prompt(
        {
            "repair_hints": [
                {
                    "kind": "high_difficulty_assertions",
                    "attempt_id": "old:simple:1:0",
                    "hard_axioms": [DROP_AXIOM],
                },
                {
                    "kind": FORMULA_EVIDENCE_KIND,
                    "attempt_id": "new:inductive:2:4",
                    "samples": [{
                        "profile": "cvc5_inductive",
                        "source": "QUANTIFIERS_INST_E_MATCHING",
                        "formula": LEN_INST,
                        "related_axiom": "",
                        "relation": "unlinked",
                    }],
                },
            ],
        },
        backend="cvc5",
    )
    assert "selected solver formulas:" in txt
    assert "high-difficulty axiom" not in txt
    assert "drop 0 x" not in txt


def test_evidence_without_difficulty_still_emits() -> None:
    result = CvcResult(
        status="unknown",
        strategy="cvc5_simple",
        lemmas=[{"formula": LEN_INST, "source": "QUANTIFIERS_INST_E_MATCHING"}],
        goal_term=GOAL,
    )
    with patch.dict(os.environ, {"FEEDBACK_FORMULA_EVIDENCE": "on"}):
        hints = derive_repair_hints(result, context="initial_goal")
    evidence = [h for h in hints if h["kind"] == FORMULA_EVIDENCE_KIND]
    assert evidence, hints
    assert evidence[0]["samples"][0]["relation"] in {
        "shared_symbols", "unlinked", "matched_quantifier",
    }


if __name__ == "__main__":
    test_parse_cvc_lemmas_skips_splits_and_keeps_source()
    test_cmd_lemmas_only_when_flag_on()
    test_select_matches_quantifier_and_caps()
    test_relevance_uses_instance_not_quantifier_prefix()
    test_shared_symbols_do_not_inherit_difficulty()
    test_selection_prefers_instances_over_early_skolem()
    test_prompt_omits_selection_scores()
    test_derive_and_prompt_gated_by_flag()
    test_stale_hotspot_not_shown_with_new_samples()
    test_evidence_without_difficulty_still_emits()
    print("ok")
