#!/usr/bin/env python3
"""FEEDBACK_LLM_HINTS: short prose note from difficulty observations."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from exp_flags import feedback_llm_hints_enabled
from feedback_llm_hints import (
    build_observation_pack,
    format_llm_hints_for_prompt,
    format_observation_prompt_body,
    has_difficulty_observations,
    maybe_refresh_llm_hints,
    parse_llm_feedback_hints,
)
from lemma_gates import format_attempt_feedback_for_prompt
import Mate_new as mate


AX = "(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m))))"
GOAL = "(forall ((n Nat)) (= (plus n zero) n))"


def _hd_data(**extra):
    data = {
        "repair_hints": [{
            "kind": "high_difficulty_assertions",
            "attempt_id": "initial_goal:cvc5_simple:1.0:0",
            "context": "initial_goal",
            "hard_axioms": [AX],
            "hard_axiom_scores": {AX: 12},
            "rarely_instantiated": [AX],
            "goal_fragments": [GOAL],
        }],
        "baseline_diag": {"goal_term": GOAL, "status": "timeout", "difficulty": [[AX, 12]]},
        "useless_lemma_groups": [],
        "llm_hints": {},
    }
    data.update(extra)
    return data


def test_flag_default_off() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("FEEDBACK_LLM_HINTS", None)
        assert feedback_llm_hints_enabled() is False
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}):
        assert feedback_llm_hints_enabled() is True


def test_skip_without_difficulty() -> None:
    empty = {"repair_hints": [], "baseline_diag": {}}
    assert has_difficulty_observations(empty) is False
    assert build_observation_pack(empty) is None


def test_pack_from_hd_without_smt_parse() -> None:
    pack = build_observation_pack(_hd_data())
    assert pack is not None
    assert pack["goal"]["id"] == "G1"
    assert pack["hard_axioms"]
    assert pack["axioms"]
    assert any(e["kind"] == "difficulty" for e in pack["evidence"])
    body = format_observation_prompt_body(pack)
    assert "=== GOAL ===" in body
    assert "=== HARD AXIOMS" in body
    assert "dump_complete" not in body
    assert "OPTIONAL NOTE" not in body


def test_pack_candidates_attributed_stats_and_prove() -> None:
    from feedback_llm_hints import format_observation_prompt_body

    lemma_a = "(forall ((n Nat)) (= (plus n zero) n))"
    lemma_b = "(forall ((x Nat)) (= x x))"
    data = _hd_data(
        baseline_diag={
            "goal_term": GOAL,
            "status": "timeout",
            "difficulty": [[AX, 12]],
            "stats": {"CONJ_TOTAL": 40, "INST_TOTAL": 120, "QUANTIFIERS_SKOLEMIZE": 3},
        },
        useless_lemma_groups=[{
            "lemmas": [lemma_a, lemma_b],
            "status": "timeout",
            "candidate_ids": {"C1": lemma_a, "C2": lemma_b},
            "attributed_ids": ["C1"],
            "mix_stats": {"CONJ_TOTAL": 52, "INST_TOTAL": 118, "QUANTIFIERS_SKOLEMIZE": 3},
            "difficulty_dump_complete": True,
            "repair_hints": [{
                "kind": "high_difficulty_assertions",
                "attempt_id": "usefulness:cvc5_simple:1.0:1",
                "hard_axioms": [AX],
                "hard_axiom_scores": {AX: 12},
                "rarely_instantiated": [AX],
                "goal_fragments": [GOAL],
            }],
        }],
        unproved_lemmas=[
            {"lemma": lemma_a, "status": "timeout"},
        ],
        invalid_lemmas=[],
        obligation={
            "last_normal_tree_id": 1,
            "attempts": [{
                "id": 1,
                "kind": "obligation_tree",
                "tree": {
                    "role": "goal",
                    "children": [
                        {"role": "lemma", "formula": lemma_b, "status": "proved"},
                    ],
                },
            }],
        },
    )
    pack = build_observation_pack(data)
    assert pack is not None
    cands = pack["previous_candidates"]
    assert cands[0]["attributed"] is True
    assert cands[0]["prove"] == "timeout"
    assert cands[1]["attributed"] is False
    assert cands[1]["prove"] == "proved"
    assert "not useful" not in str(cands[1]).lower()
    body = format_observation_prompt_body(pack)
    assert "=== LAST CANDIDATE LEMMAS" in body
    assert "prove=timeout" in body
    assert "prove=proved" in body
    assert "not useful" not in body.lower()
    assert "=== SEARCH CHANGE VS BASELINE (for reference) ===" in body
    assert "Read as:" not in body
    assert "↑" in body or "flat" in body
    assert "dump_complete" not in body


def test_pack_prove_invalid_and_unknown() -> None:
    from feedback_llm_hints import format_observation_prompt_body

    lemma_bad = "(forall ((x Nat)) (P x))"
    lemma_unk = "(forall ((y Nat)) (Q y))"
    data = _hd_data(
        useless_lemma_groups=[{
            "lemmas": [lemma_bad, lemma_unk],
            "status": "timeout",
            "candidate_ids": {"C1": lemma_bad, "C2": lemma_unk},
            "attributed_ids": [],
            "mix_stats": {"CONJ_TOTAL": 1, "INST_TOTAL": 1, "QUANTIFIERS_SKOLEMIZE": 0},
            "difficulty_dump_complete": True,
            "repair_hints": [{
                "kind": "high_difficulty_assertions",
                "attempt_id": "usefulness:x",
                "hard_axioms": [AX],
                "hard_axiom_scores": {AX: 12},
                "rarely_instantiated": [],
                "goal_fragments": [GOAL],
            }],
        }],
        invalid_lemmas=[{"lemma": lemma_bad, "reason": "sat"}],
    )
    pack = build_observation_pack(data)
    assert pack is not None
    assert pack["previous_candidates"][0]["prove"] == "invalid"
    assert pack["previous_candidates"][1]["prove"] == "unknown"
    body = format_observation_prompt_body(pack)
    assert "prove=invalid" in body
    assert "prove=unknown" in body


def test_parse_plain_and_prompt_block() -> None:
    raw = (
        "The plus-succ hotspot looks unused in the inductive step. "
        "Try a directed rewrite bridging zero and succ on the accumulator. E1"
    )
    diag = parse_llm_feedback_hints(raw)
    assert diag is not None
    assert "plus-succ hotspot" in diag["text"]
    assert "E1" not in diag["text"]
    txt = format_llm_hints_for_prompt({
        "attempt_id": "x",
        "hints": diag,
    })
    assert "SOLVER HINTS" in txt
    assert "plus-succ hotspot" in txt
    assert "evidence:" not in txt
    assert "hypothesis (" not in txt


def test_parse_legacy_json_collapsed() -> None:
    raw = """```json
{
  "hypotheses": [{
    "interpretation": "need a bridge on plus; E1 hotspot",
    "alternative_explanation": "hotspot may be irrelevant",
    "candidate_lemma": "(forall ((n Nat)) (= (plus n zero) n))",
    "goal_connection": "covers the zero case"
  }]
}
```"""
    diag = parse_llm_feedback_hints(raw)
    assert diag is not None
    assert "need a bridge on plus" in diag["text"]
    assert "E1" not in diag["text"]
    assert "Alternative:" in diag["text"]


def test_maybe_refresh_skips_without_difficulty(tmp_path: Path) -> None:
    base = str(tmp_path)
    (tmp_path / "template.smt2").write_text("(assert true)\n", encoding="utf-8")
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}):
        out = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
    assert out is None
    assert mate.load_failed_lemmas(base, "template").get("llm_hints") in ({}, None)


def test_maybe_refresh_runs_and_stores(tmp_path: Path) -> None:
    base = str(tmp_path)
    mate.save_failed_lemmas(base, "template", _hd_data())
    raw = (
        "Generalize the accumulator so the inductive hypothesis matches the "
        "succ case of plus; avoid repeating the previous candidate set."
    )
    fake_resp = MagicMock()
    fake_resp.content = raw
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
        return_value=(fake_resp, MagicMock(apply=False)),
    ):
        rec = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
    assert rec is not None
    stored = mate.load_failed_lemmas(base, "template")["llm_hints"]
    assert "Generalize the accumulator" in stored["hints"]["text"]

    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
    ) as inv:
        again = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_not_called()
    assert again["attempt_id"] == stored["attempt_id"]


def test_prompt_llm_hints_replace_program_hints_inside_last_attempt() -> None:
    data = _hd_data(
        useless_lemma_groups=[{
            "lemmas": ["(forall ((x Nat)) (= x x))"],
            "status": "timeout",
            "repair_hints": [{
                "kind": "high_difficulty_assertions",
                "attempt_id": "usefulness:cvc5_simple:1.0:1",
                "hard_axioms": [AX],
                "rarely_instantiated": [AX],
                "goal_fragments": [GOAL],
            }],
        }],
        llm_hints={
            "attempt_id": "usefulness:cvc5_simple:1.0:1",
            "hints": {
                "text": (
                    "Try a directed equality that connects the hard plus "
                    "axiom into the inductive step."
                ),
            },
        },
    )
    with patch.dict(os.environ, {
        "FEEDBACK_LLM_HINTS": "on",
        "PROMPT_ADVICE": "on",
        "FEEDBACK_REPAIR_HINTS": "on",
    }):
        txt = mate.format_solver_feedback_for_prompt(data)
    assert "LAST ATTEMPT" in txt
    assert "SOLVER HINTS" in txt
    assert txt.index("LAST ATTEMPT") < txt.index("SOLVER HINTS")
    assert txt.index("SOLVER HINTS") < txt.index("You may refine kept lemmas")
    assert "directed equality" in txt
    assert "advice: TRIGGER" not in txt
    assert "high-difficulty axiom" not in txt
    assert "repair hints:" not in txt
    assert "\n\nSOLVER HINTS" not in txt


def test_format_attempt_suppress_advice_flag() -> None:
    data = _hd_data()
    with patch.dict(os.environ, {"PROMPT_ADVICE": "on"}):
        on = format_attempt_feedback_for_prompt(data, backend="cvc5")
        off = format_attempt_feedback_for_prompt(
            data, backend="cvc5", suppress_advice=True,
        )
    assert "advice: TRIGGER" in on
    assert "advice:" not in off


if __name__ == "__main__":
    test_flag_default_off()
    test_skip_without_difficulty()
    test_pack_from_hd_without_smt_parse()
    test_pack_candidates_attributed_stats_and_prove()
    test_pack_prove_invalid_and_unknown()
    test_parse_plain_and_prompt_block()
    test_parse_legacy_json_collapsed()
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_skips_without_difficulty(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_runs_and_stores(Path(tmp))
    test_prompt_llm_hints_replace_program_hints_inside_last_attempt()
    test_format_attempt_suppress_advice_flag()
    print("feedback_llm_hints tests passed")
