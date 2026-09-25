#!/usr/bin/env python3
"""FEEDBACK_LLM_HINTS: short prose note from difficulty observations."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Optional
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
    has_hint_opportunity,
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


def _write_library(tmp_path: Path, lemmas: Optional[list] = None) -> None:
    items = lemmas if lemmas is not None else [{
        "id": "lib_1",
        "formula": AX,
        "role": "pin",
        "status": "proved",
    }]
    (tmp_path / "lemma_library.json").write_text(
        json.dumps({"lemmas": items}),
        encoding="utf-8",
    )


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


def test_pack_without_difficulty_omits_hard_axioms() -> None:
    lemma = "(forall ((n Nat)) (= (plus n zero) n))"
    data = {
        "repair_hints": [],
        "baseline_diag": {},
        "useless_lemma_groups": [{
            "lemmas": [lemma],
            "status": "timeout",
        }],
        "unproved_lemmas": [{"lemma": lemma, "status": "timeout"}],
        "obligation": {
            "last_normal_tree_id": 1,
            "attempts": [{
                "id": 1,
                "kind": "obligation_tree",
                "tree": {"role": "goal", "formula": GOAL, "status": "open", "children": []},
            }],
        },
    }
    assert has_difficulty_observations(data) is False
    pack = build_observation_pack(data)
    assert pack is not None
    assert pack["hard_axioms"] == []
    assert pack["goal"]["formula"]
    assert "(unknown)" not in pack["goal"]["formula"]
    assert GOAL in pack["goal"]["formula"]
    assert pack["previous_candidates"]
    assert pack["revival_candidates"]
    body = format_observation_prompt_body(pack)
    assert "=== HARD AXIOMS" not in body
    assert "=== LAST CANDIDATE LEMMAS" in body
    assert "previous generation round" in body
    assert "=== REVIVAL CANDIDATES" in body
    assert "historical unproved" in body
    assert GOAL in body
    assert "(unknown)" not in body
    assert "hotspot" not in body.lower()
    assert "attributed" not in body


def test_pack_goal_prefers_current_node_over_hd_fragments() -> None:
    fragment = "(plus n zero)"
    data = _hd_data()
    data["repair_hints"][0]["goal_fragments"] = [fragment]
    data["baseline_diag"]["goal_term"] = fragment
    pack = build_observation_pack(data, current_goal=GOAL)
    assert pack is not None
    assert pack["goal"]["formula"] == GOAL


def test_pack_keeps_long_formulas() -> None:
    from feedback_llm_hints import _prompt_formula

    long_goal = "(forall (" + " ".join(f"(x{i} Nat)" for i in range(40)) + ") true)"
    assert len(long_goal) > 280
    data = {
        "repair_hints": [],
        "baseline_diag": {},
        "useless_lemma_groups": [{"lemmas": [long_goal], "status": "timeout"}],
        "unproved_lemmas": [{"lemma": long_goal, "status": "timeout"}],
        "obligation": {
            "last_normal_tree_id": 1,
            "attempts": [{
                "id": 1,
                "kind": "obligation_tree",
                "tree": {"role": "goal", "formula": long_goal, "status": "open", "children": []},
            }],
        },
    }
    pack = build_observation_pack(data, library=[{
        "id": "lib_9", "formula": long_goal, "role": "pin",
    }], prev_library_ids=[])
    assert pack is not None
    assert pack["goal"]["formula"] == _prompt_formula(long_goal)
    assert not pack["goal"]["formula"].endswith("...")
    body = format_observation_prompt_body(pack)
    assert _prompt_formula(long_goal) in body
    assert "lib_9" not in body
    assert "[NEW]" in body
    assert "added since the last diagnoser baseline" in body


def test_pack_library_shows_all_and_marks_new() -> None:
    old = "(forall ((n Nat)) (= (plus n zero) n))"
    new = AX
    data = _hd_data_with_useless()
    pack = build_observation_pack(
        data,
        library=[
            {"id": "lib_1", "formula": old, "role": "pin"},
            {"id": "lib_2", "formula": new, "role": "local"},
        ],
        prev_library_ids=["lib_1"],
    )
    assert pack is not None
    assert pack["library_new"] is True
    assert len(pack["library"]) == 2
    assert pack["library"][0]["new"] is False
    assert pack["library"][1]["new"] is True
    body = format_observation_prompt_body(pack)
    assert "=== LEMMA LIBRARY (proved axioms already available) ===" in body
    assert "added since the last diagnoser baseline" in body
    assert f"{old} [pin]" in body
    assert f"{new} [local] [NEW]" in body
    assert "lib_1" not in body and "lib_2" not in body


def test_pack_from_hd_without_smt_parse() -> None:
    pack = build_observation_pack(_hd_data_with_useless())
    assert pack is not None
    assert pack["goal"]["id"] == "G1"
    assert pack["hard_axioms"]
    assert pack["axioms"]
    assert any(e["kind"] == "difficulty" for e in pack["evidence"])
    body = format_observation_prompt_body(pack)
    assert "=== GOAL ===" in body
    assert "=== HARD AXIOMS" in body
    assert "last usefulness dump" in body
    assert "dump_complete" not in body
    assert "OPTIONAL NOTE" not in body


def test_pack_skips_initial_and_baseline_hd() -> None:
    lemma = GOAL
    data = {
        "repair_hints": [{
            "kind": "high_difficulty_assertions",
            "context": "initial_goal",
            "attempt_id": "initial_goal:cvc5_simple:1.0:0",
            "hard_axioms": [AX],
            "goal_fragments": [GOAL],
        }],
        "baseline_diag": {
            "goal_term": GOAL,
            "status": "timeout",
            "difficulty": [[GOAL, 99], [AX, 12]],
        },
        "useless_lemma_groups": [{
            "lemmas": [lemma],
            "status": "timeout",
            "repair_hints": [{
                "kind": "high_difficulty_assertions",
                "context": "initial_goal",
                "attempt_id": "initial_goal:cvc5_simple:1.0:0",
                "hard_axioms": [AX],
            }],
        }],
        "unproved_lemmas": [{"lemma": lemma, "status": "timeout"}],
    }
    pack = build_observation_pack(data, current_goal=GOAL)
    assert pack is not None
    assert pack["hard_axioms"] == []
    body = format_observation_prompt_body(pack)
    assert "=== HARD AXIOMS" not in body


def test_pack_filters_goal_terms_from_usefulness_hd() -> None:
    from feedback_llm_hints import _prompt_formula

    data = _hd_data_with_useless()
    data["useless_lemma_groups"][-1]["repair_hints"][0]["hard_axioms"] = [GOAL, AX]
    data["useless_lemma_groups"][-1]["repair_hints"][0]["hard_axiom_scores"] = {
        GOAL: 99, AX: 12,
    }
    pack = build_observation_pack(data, current_goal=GOAL)
    assert pack is not None
    formulas = [item["formula"] for item in pack["hard_axioms"]]
    assert _prompt_formula(AX) in formulas
    assert _prompt_formula(GOAL) not in formulas


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
    assert "attributed=yes" in body
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
                "context": "usefulness_check",
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
    revive_ids = {item["formula"] for item in pack["revival_candidates"]}
    assert lemma_bad not in revive_ids
    assert lemma_unk in body or "(none)" in body
    assert "select by id" not in body
    assert "R1:" not in body


def test_parse_plain_and_prompt_block() -> None:
    raw = (
        "The plus-succ hotspot looks unused in the inductive step. "
        "Try a directed rewrite bridging zero and succ on the accumulator. E1"
    )
    diag = parse_llm_feedback_hints(raw)
    assert diag is not None
    assert "plus-succ hotspot" in diag["text"]
    assert "E1" not in diag["text"]
    assert diag.get("revive") == []
    txt = format_llm_hints_for_prompt({
        "attempt_id": "x",
        "hints": diag,
    })
    assert "SOLVER HINTS" in txt
    assert "plus-succ hotspot" in txt
    assert "new direction" in txt
    assert "pending (" not in txt
    assert "evidence:" not in txt
    assert "hypothesis (" not in txt


def test_parse_note_and_revive_json() -> None:
    cand = "(forall ((n Nat)) (= (plus n zero) n))"
    invented = "(forall ((n Nat)) false)"
    pool = [{"id": "R1", "formula": cand, "status": "timeout"}]
    raw = json.dumps({
        "mode": "REVISE_CANDIDATE",
        "note": (
            "Library now has plus-succ. The zero-case candidate is still unproved; "
            "decide whether it fits the CURRENT goal. R1"
        ),
        "revive": [
            {"formula": cand, "note": "zero case; still unproved after plus-succ landed"},
            {"formula": invented, "note": "invented"},
        ],
    })
    diag = parse_llm_feedback_hints(raw, revival_candidates=pool)
    assert diag is not None
    assert diag["mode"] == "revise_candidate"
    assert "plus-succ" in diag["text"]
    assert "R1" not in diag["text"]
    assert len(diag["revive"]) == 1
    assert diag["revive"][0]["formula"] == cand
    assert diag["revive"][0]["note"] == "zero case; still unproved after plus-succ landed"
    assert "action" not in diag["revive"][0]
    txt = format_llm_hints_for_prompt({"hints": diag})
    assert "pending candidates" in txt
    assert "pending (unproved; not assumed true or useful)" in txt
    assert "Decide for yourself how to use each one" in txt
    assert "note: zero case; still unproved after plus-succ landed" in txt
    assert "[weaken]" not in txt
    assert "[retry]" not in txt
    assert cand in txt
    assert "R1" not in txt


def test_parse_revive_still_accepts_pool_id() -> None:
    cand = "(forall ((n Nat)) (= (plus n zero) n))"
    pool = [{"id": "R1", "formula": cand, "status": "timeout"}]
    raw = json.dumps({
        "mode": "REVISE_CANDIDATE",
        "note": "The plus-zero candidate is still open now that plus-succ is in the library.",
        "revive": [{"id": "R1", "note": "library may supply the missing succ step"}],
    })
    diag = parse_llm_feedback_hints(raw, revival_candidates=pool)
    assert diag["revive"][0]["formula"] == cand
    assert "succ step" in diag["revive"][0]["note"]


def test_no_action_not_injected() -> None:
    cand = "(forall ((n Nat)) (= (plus n zero) n))"
    raw = json.dumps({
        "mode": "NO_ACTION",
        "note": "The last candidate set is still a reasonable try; do not steer.",
        "revive": [{"formula": cand, "note": "should not appear"}],
    })
    diag = parse_llm_feedback_hints(
        raw, revival_candidates=[{"id": "R1", "formula": cand}],
    )
    assert diag["mode"] == "no_action"
    assert diag["revive"] == []
    txt = format_llm_hints_for_prompt({"hints": diag})
    assert txt == ""
    assert "SOLVER HINTS" not in txt


def test_new_direction_text_only() -> None:
    cand = "(forall ((n Nat)) (= (plus n zero) n))"
    raw = json.dumps({
        "mode": "NEW_DIRECTION",
        "note": "Commutativity and n+0 copies are not worth reviving; try a directed succ-step lemma.",
        "revive": [{"formula": cand, "note": "should not appear"}],
    })
    diag = parse_llm_feedback_hints(
        raw, revival_candidates=[{"id": "R1", "formula": cand}],
    )
    assert diag["mode"] == "new_direction"
    assert diag["revive"] == []
    txt = format_llm_hints_for_prompt({"hints": diag})
    assert "new direction" in txt
    assert "different lemma shape" in txt
    assert "succ-step lemma" in txt
    assert cand not in txt
    assert "pending (" not in txt


def test_legacy_hold_not_injected() -> None:
    cand = "(forall ((n Nat)) (= (plus n zero) n))"
    raw = json.dumps({
        "note": "Keep the unproved plus-zero lemma off the generator prompt this round.",
        "revive": [{"formula": cand, "action": "hold", "why": "no library bridge yet"}],
    })
    diag = parse_llm_feedback_hints(
        raw, revival_candidates=[{"id": "R1", "formula": cand}],
    )
    assert diag["mode"] == "new_direction"
    assert diag["revive"] == []
    txt = format_llm_hints_for_prompt({"hints": diag})
    assert cand not in txt
    assert "[hold]" not in txt


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
    assert diag.get("revive") == []


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


def test_maybe_refresh_skips_without_useless_group(tmp_path: Path) -> None:
    """First-gen gate: HD alone must not trigger hints."""
    base = str(tmp_path)
    (tmp_path / "template.smt2").write_text("(assert true)\n", encoding="utf-8")
    mate.save_failed_lemmas(base, "template", _hd_data())  # empty useless groups
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
    ) as inv:
        out = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_not_called()
    assert out is None


def test_maybe_refresh_runs_without_difficulty(tmp_path: Path) -> None:
    lemma = "(forall ((n Nat)) (= (plus n zero) n))"
    base = str(tmp_path)
    mate.save_failed_lemmas(base, "template", {
        "repair_hints": [],
        "baseline_diag": {},
        "useless_lemma_groups": [{"lemmas": [lemma], "status": "timeout"}],
        "unproved_lemmas": [{"lemma": lemma, "status": "timeout"}],
        "llm_hints": {},
    })
    _write_library(tmp_path)
    raw = json.dumps({
        "mode": "NEW_DIRECTION",
        "note": "No hotspot dump is available; try a directed zero-case lemma instead of repeating the last set.",
        "revive": [],
    })
    fake_resp = MagicMock()
    fake_resp.content = raw
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
        return_value=(fake_resp, MagicMock(apply=False)),
    ) as inv:
        rec = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
            current_goal=GOAL,
        )
        inv.assert_called_once()
    user = inv.call_args.args[1][1]["content"]
    assert "=== HARD AXIOMS" not in user
    assert "=== LAST CANDIDATE LEMMAS" in user
    assert f"=== GOAL ===\n  {GOAL}" in user
    assert "(unknown)" not in user
    assert rec is not None
    assert rec["hints"]["mode"] == "new_direction"


def test_has_hint_opportunity_unproved_and_library_delta() -> None:
    lemma = "(forall ((n Nat)) (= (plus n zero) n))"
    empty = _hd_data(useless_lemma_groups=[{"lemmas": [lemma], "status": "timeout"}])
    assert has_hint_opportunity(empty) is False
    with_unproved = _hd_data(unproved_lemmas=[{"lemma": lemma, "status": "timeout"}])
    lib = [{"id": "lib_1", "formula": AX, "role": "pin"}]
    assert has_hint_opportunity(with_unproved) is False
    assert has_hint_opportunity(with_unproved, library=lib) is True
    assert has_hint_opportunity(with_unproved, library=lib, prev_library_ids=[]) is True
    assert has_hint_opportunity(with_unproved, library=lib, prev_library_ids=["lib_0"]) is True
    assert has_hint_opportunity(with_unproved, library=lib, prev_library_ids=["lib_1"]) is False
    assert has_hint_opportunity(empty, library=lib, prev_library_ids=["lib_0"]) is False


def test_maybe_refresh_skips_without_opportunity(tmp_path: Path) -> None:
    base = str(tmp_path)
    data = _hd_data_with_useless()
    data["unproved_lemmas"] = []
    mate.save_failed_lemmas(base, "template", data)
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
    ) as inv:
        out = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_not_called()
    assert out is None


def test_maybe_refresh_skips_unproved_without_library_delta(tmp_path: Path) -> None:
    base = str(tmp_path)
    data = _hd_data_with_useless()
    data["llm_hints"] = {"library_ids": ["lib_1"]}
    mate.save_failed_lemmas(base, "template", data)
    _write_library(tmp_path)
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
    ) as inv:
        out = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_not_called()
    assert out is None


def test_maybe_refresh_snapshots_then_runs_on_library_growth(tmp_path: Path) -> None:
    base = str(tmp_path)
    mate.save_failed_lemmas(base, "template", _hd_data_with_useless())
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
    ) as inv:
        out = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_not_called()
    assert out is None
    assert mate.load_failed_lemmas(base, "template")["llm_hints"]["library_ids"] == []
    _write_library(tmp_path)
    raw = json.dumps({
        "mode": "NEW_DIRECTION",
        "note": "Library now has plus-succ; try a directed zero-case lemma.",
        "revive": [],
    })
    fake_resp = MagicMock()
    fake_resp.content = raw
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
        return_value=(fake_resp, MagicMock(apply=False)),
    ) as inv:
        rec = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_called_once()
    assert rec is not None
    assert rec["hints"]["mode"] == "new_direction"


def test_maybe_refresh_first_call_nonempty_library_vs_empty(tmp_path: Path) -> None:
    """First diagnoser: any library lemmas count as growth vs empty."""
    base = str(tmp_path)
    mate.save_failed_lemmas(base, "template", _hd_data_with_useless())
    _write_library(tmp_path)
    raw = json.dumps({
        "mode": "NEW_DIRECTION",
        "note": "Existing library lemmas change the context; try a directed zero-case.",
        "revive": [],
    })
    fake_resp = MagicMock()
    fake_resp.content = raw
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
        return_value=(fake_resp, MagicMock(apply=False)),
    ) as inv:
        rec = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_called_once()
    user = inv.call_args.args[1][1]["content"]
    assert "[NEW]" in user
    assert "added since the last diagnoser baseline" in user
    assert AX in user or "plus" in user
    assert "lib_1" not in user
    assert "Re-evaluate the unproved revival candidates" in inv.call_args.args[1][0]["content"]
    assert rec is not None


def test_maybe_refresh_runs_on_library_delta(tmp_path: Path) -> None:
    base = str(tmp_path)
    data = _hd_data_with_useless()
    data["llm_hints"] = {
        "library_ids": ["lib_0"],
        "attempt_id": "old",
        "hints": {"text": "x" * 30, "revive": []},
    }
    mate.save_failed_lemmas(base, "template", data)
    _write_library(tmp_path)
    raw = json.dumps({
        "note": "New plus-succ axiom in the library; try a directed zero-case bridge.",
        "revive": [],
    })
    fake_resp = MagicMock()
    fake_resp.content = raw
    with patch.dict(os.environ, {"FEEDBACK_LLM_HINTS": "on"}), patch(
        "feedback_llm_hints.invoke_configured_chat",
        return_value=(fake_resp, MagicMock(apply=False)),
    ) as inv:
        rec = maybe_refresh_llm_hints(
            base,
            "template",
            llm=MagicMock(),
            config=mate.config,
            load_failed_lemmas=mate.load_failed_lemmas,
            save_failed_lemmas=mate.save_failed_lemmas,
        )
        inv.assert_called_once()
    assert rec is not None
    assert "plus-succ" in rec["hints"]["text"]


def _hd_data_with_useless(**extra):
    lemma = "(forall ((n Nat)) (= (plus n zero) n))"
    data = _hd_data(
        useless_lemma_groups=[{
            "lemmas": [lemma],
            "status": "timeout",
            "candidate_ids": {"C1": lemma},
            "attributed_ids": [],
            "mix_stats": {"CONJ_TOTAL": 1, "INST_TOTAL": 1, "QUANTIFIERS_SKOLEMIZE": 0},
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
        unproved_lemmas=[{"lemma": lemma, "status": "timeout"}],
    )
    data.update(extra)
    return data


def test_maybe_refresh_runs_and_stores(tmp_path: Path) -> None:
    base = str(tmp_path)
    data = _hd_data_with_useless()
    mate.save_failed_lemmas(base, "template", data)
    _write_library(tmp_path)
    cand = "(forall ((n Nat)) (= (plus n zero) n))"
    raw = json.dumps({
        "note": (
            "Generalize the accumulator so the inductive hypothesis matches "
            "the succ case of plus; avoid repeating the previous candidate set."
        ),
        "revive": [cand],
    })
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
    assert stored["hints"]["revive"][0]["formula"] == cand
    assert stored["hints"]["mode"] == "revise_candidate"
    assert "action" not in stored["hints"]["revive"][0]

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


def test_prompt_skips_llm_hints_without_useless_group() -> None:
    """Stored hints must not inject on INITIAL SOLVE before any useless group."""
    data = _hd_data(
        llm_hints={
            "attempt_id": "initial_goal:x",
            "hints": {"text": "Should not appear before usefulness failure.", "revive": []},
        },
    )
    with patch.dict(os.environ, {
        "FEEDBACK_LLM_HINTS": "on",
        "PROMPT_ADVICE": "on",
        "FEEDBACK_REPAIR_HINTS": "on",
    }):
        txt = mate.format_solver_feedback_for_prompt(data)
    assert "Should not appear" not in txt
    assert "SOLVER HINTS" not in txt
    assert "high-difficulty axiom" not in txt
    assert "repair hints:" not in txt


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


def test_hints_flag_omits_program_repair_without_llm_block() -> None:
    """Flag on: no HD/repair fallback, even when the diagnoser skipped or chose NO_ACTION."""
    group = {
        "lemmas": ["(forall ((x Nat)) (= x x))"],
        "status": "timeout",
        "repair_hints": [{
            "kind": "high_difficulty_assertions",
            "attempt_id": "usefulness:cvc5_simple:1.0:1",
            "hard_axioms": [AX],
            "rarely_instantiated": [AX],
            "goal_fragments": [GOAL],
        }],
    }
    skipped = _hd_data(useless_lemma_groups=[group])
    no_action = _hd_data(
        useless_lemma_groups=[group],
        llm_hints={
            "attempt_id": "x",
            "hints": {"mode": "no_action", "text": "", "revive": []},
        },
    )
    with patch.dict(os.environ, {
        "FEEDBACK_LLM_HINTS": "on",
        "PROMPT_ADVICE": "on",
        "FEEDBACK_REPAIR_HINTS": "on",
    }):
        skipped_txt = mate.format_solver_feedback_for_prompt(skipped)
        no_action_txt = mate.format_solver_feedback_for_prompt(no_action)
    for txt in (skipped_txt, no_action_txt):
        assert "LAST ATTEMPT" in txt
        assert "SOLVER HINTS" not in txt
        assert "repair hints:" not in txt
        assert "high-difficulty axiom" not in txt
        assert "advice: TRIGGER" not in txt


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
    test_pack_skips_initial_and_baseline_hd()
    test_pack_filters_goal_terms_from_usefulness_hd()
    test_pack_without_difficulty_omits_hard_axioms()
    test_pack_goal_prefers_current_node_over_hd_fragments()
    test_pack_keeps_long_formulas()
    test_pack_candidates_attributed_stats_and_prove()
    test_pack_prove_invalid_and_unknown()
    test_parse_plain_and_prompt_block()
    test_parse_note_and_revive_json()
    test_parse_revive_still_accepts_pool_id()
    test_no_action_not_injected()
    test_new_direction_text_only()
    test_legacy_hold_not_injected()
    test_parse_legacy_json_collapsed()
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_skips_without_difficulty(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_skips_without_useless_group(Path(tmp))
    test_has_hint_opportunity_unproved_and_library_delta()
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_skips_without_opportunity(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_skips_unproved_without_library_delta(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_snapshots_then_runs_on_library_growth(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_first_call_nonempty_library_vs_empty(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_runs_without_difficulty(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_runs_on_library_delta(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_maybe_refresh_runs_and_stores(Path(tmp))
    test_prompt_llm_hints_replace_program_hints_inside_last_attempt()
    test_prompt_skips_llm_hints_without_useless_group()
    test_hints_flag_omits_program_repair_without_llm_block()
    test_format_attempt_suppress_advice_flag()
    print("feedback_llm_hints tests passed")
