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
    assert DROP_AXIOM in matched[0]["related_axiom"]
    assert matched[0]["profile"] == "cvc5_inductive"


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
    test_derive_and_prompt_gated_by_flag()
    test_stale_hotspot_not_shown_with_new_samples()
    test_evidence_without_difficulty_still_emits()
    print("ok")
