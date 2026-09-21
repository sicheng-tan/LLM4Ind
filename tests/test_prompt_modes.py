#!/usr/bin/env python3
"""v2 LAST ATTEMPT advice classifier and prompt lines."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from lemma_gates import (
    HD_AXIOM_GOAL_HINT,
    format_attempt_feedback_for_prompt,
)
from prompt_modes import (
    ADVICE_BRIDGE,
    ADVICE_GENERALIZE,
    ADVICE_LOCALIZE,
    ADVICE_PRUNE,
    ADVICE_TRIGGER,
    PRUNE_CONSTRAINT,
    advice_from_failed_data,
    format_advice_lines,
    format_local_vs_parent_lines,
    select_prompt_advice,
)

AX = "(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m))))"
ZERO = "(forall ((n Nat)) (= (plus zero n) n))"
GOAL = "(plus (succ x) (succ x))"
CHILD = "(forall ((n Nat)) (= (plus (succ n) zero) (succ n)))"
STEP_CHILD = "(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (plus n (succ m))))"
KEPT = "(forall ((x Nat)) (= (plus x x) (plus x x)))"


def _hd(**extra):
    hint = {
        "kind": "high_difficulty_assertions",
        "hard_axioms": [AX],
        "goal_fragments": [GOAL],
    }
    hint.update(extra)
    return hint


def test_default_mode_has_no_advice() -> None:
    data = {
        "strategy_mode": "default",
        "repair_hints": [_hd(rarely_instantiated=[AX])],
    }
    assert advice_from_failed_data(data) is None
    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "advice:" not in txt
    assert HD_AXIOM_GOAL_HINT in txt


def test_trigger_from_rare_inst() -> None:
    data = {
        "strategy_mode": "v2",
        "repair_hints": [_hd(rarely_instantiated=[AX])],
    }
    adv = advice_from_failed_data(data)
    assert adv is not None and adv.name == ADVICE_TRIGGER
    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "INITIAL SOLVE" in txt
    assert "advice: TRIGGER" in txt
    assert "because:" in txt
    assert "hint:" in txt
    assert "shape:" in txt
    assert "plus (succ n) m" in txt
    assert HD_AXIOM_GOAL_HINT not in txt
    assert ":pattern" not in txt


def test_default_simple_has_no_advice() -> None:
    data = {
        "strategy_mode": "default_simple",
        "repair_hints": [_hd(rarely_instantiated=[AX])],
    }
    assert advice_from_failed_data(data) is None


def test_v2_simple_keeps_advice() -> None:
    data = {
        "strategy_mode": "v2_simple",
        "repair_hints": [_hd(rarely_instantiated=[AX])],
    }
    adv = advice_from_failed_data(data)
    assert adv is not None and adv.name == ADVICE_TRIGGER


def test_prompt_advice_flag_off_skips_advice() -> None:
    """Ablation: v2 template + HD without explicit advice: lines."""
    data = {
        "strategy_mode": "v2_simple",
        "repair_hints": [_hd(rarely_instantiated=[AX])],
    }
    with patch.dict(os.environ, {"PROMPT_ADVICE": "off"}):
        assert advice_from_failed_data(data) is None
        txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "advice:" not in txt
    assert HD_AXIOM_GOAL_HINT in txt
    assert "high-difficulty axiom" in txt


def test_vampire_backend_skips_advice() -> None:
    data = {
        "strategy_mode": "v2",
        "repair_hints": [_hd(rarely_instantiated=[AX])],
    }
    assert advice_from_failed_data(data, backend="vampire") is None


def test_prune_uses_conj_inst_log_gain_and_goal_not_drop() -> None:
    base_stats = {"CONJ_TOTAL": 10, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 2}
    boom = {"CONJ_TOTAL": 40, "INST_TOTAL": 12, "QUANTIFIERS_SKOLEMIZE": 2}
    # search_explosion sidecar strings are ignored
    adv = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        dump_complete=True,
        attributed=True,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=8,
    )
    assert adv is None or adv.name != ADVICE_PRUNE
    adv = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        baseline_stats=base_stats,
        mix_stats=boom,
        dump_complete=False,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=8,
    )
    assert adv is None or adv.name != ADVICE_PRUNE
    adv = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        baseline_stats=base_stats,
        mix_stats=boom,
        dump_complete=True,
        attributed=True,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=8,
    )
    assert adv is not None and adv.name == ADVICE_BRIDGE
    assert adv.constraint is None
    constrained = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        baseline_stats=base_stats,
        mix_stats=boom,
        dump_complete=True,
        attributed=False,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=8,
    )
    assert constrained is not None
    assert constrained.name != ADVICE_PRUNE
    assert constrained.constraint == PRUNE_CONSTRAINT
    adv_drop = select_prompt_advice(
        has_kept=True,
        baseline_stats=base_stats,
        mix_stats=boom,
        dump_complete=True,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=2,
    )
    assert adv_drop is None or adv_drop.name != ADVICE_PRUNE


def test_generalize_needs_child_and_structure() -> None:
    adv = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        failed_children=[],
    )
    assert adv is None or adv.name != ADVICE_GENERALIZE
    adv = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        failed_children=[CHILD],
    )
    assert adv is not None and adv.name == ADVICE_GENERALIZE
    lines = "\n".join(format_advice_lines(adv))
    assert "advice: GENERALIZE" in lines
    assert "action:" not in lines
    assert "one-step unfold" in lines
    assert "constructor-case" in lines
    assert "too-specific" in lines
    assert "generalize variables" in lines
    assert "weaken" in lines
    no_ctor = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        failed_children=["(forall ((x Int)) (= (len x) (len x)))"],
    )
    assert no_ctor is None or no_ctor.name != ADVICE_GENERALIZE


def test_generalize_action_split() -> None:
    case = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX, ZERO],
        goal_fragments=[GOAL],
        failed_children=[AX],
    )
    assert case is not None and case.name == ADVICE_GENERALIZE
    assert "action:" not in "\n".join(format_advice_lines(case))
    step = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        failed_children=[STEP_CHILD],
    )
    assert step is not None and step.name == ADVICE_GENERALIZE
    mixed = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        failed_children=[CHILD, STEP_CHILD],
    )
    assert mixed is not None and mixed.name == ADVICE_GENERALIZE
    assert "one-step unfold" in mixed.hint and "constructor-case" in mixed.hint
    assert "too-specific" in mixed.hint
    assert "weaken" in mixed.hint
    assert "generalize variables" in mixed.hint
    assert "action:" not in "\n".join(format_advice_lines(mixed))


def test_local_vs_parent_contrast_in_last_attempt() -> None:
    """Proved locals + open parent appear under repair hints (tree_Flatten3-style)."""
    proved_local = (
        "(forall ((a Tree) (b Tree)) "
        "(= (flatten3 (Node a b)) (app (flatten3 a) (flatten3 b))))"
    )
    failed_local = (
        "(forall ((t Tree)) (= (flatten3 t) (flatten3 t)))"
    )
    parent = "(forall ((t Tree)) (= (flatten3 t) (flatten0 t)))"
    data = {
        "strategy_mode": "v2_simple",
        "baseline_diag": {"goal_term": parent},
        "obligation": {
            "attempts": [{
                "id": 1,
                "kind": "obligation_tree",
                "tree": {
                    "id": "G",
                    "role": "goal",
                    "formula": None,
                    "status": "open",
                    "children": [
                        {
                            "id": "L1",
                            "role": "lemma",
                            "status": "proved",
                            "formula": proved_local,
                            "children": [],
                        },
                        {
                            "id": "L2",
                            "role": "lemma",
                            "status": "failed",
                            "formula": failed_local,
                            "children": [],
                        },
                    ],
                },
            }],
        },
        "useless_lemma_groups": [{
            "lemmas": [KEPT],
            "status": "timeout",
            "repair_hints": [_hd()],
        }],
    }
    contrast = "\n".join(format_local_vs_parent_lines(data))
    assert "already proved (local):" in contrast
    assert "flatten3 (Node" in contrast or "flatten3" in contrast
    assert "still open (parent):" in contrast
    assert "flatten0" in contrast
    assert "do not resend proved locals" in contrast

    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "already proved (local):" in txt
    assert "still open (parent):" in txt
    assert txt.index("already proved (local):") < txt.index("still open (parent):")

    adv = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        failed_children=[CHILD],
        proved_children=[proved_local],
    )
    assert adv is not None and adv.name == ADVICE_GENERALIZE
    assert "already proved locally" in adv.because
    assert "open parent" in adv.hint


def test_localize_and_bridge() -> None:
    loc = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        baseline_stats={"CONJ_TOTAL": 10, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 4},
        mix_stats={"CONJ_TOTAL": 25, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 4},
    )
    assert loc is not None and loc.name == ADVICE_LOCALIZE
    loc_str = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        baseline_stats={"CONJ_TOTAL": 10, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 4},
        mix_stats={"CONJ_TOTAL": 10, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 4},
    )
    assert loc_str is None or loc_str.name != ADVICE_LOCALIZE
    br = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        dump_complete=True,
        attributed=True,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=8,
    )
    assert br is not None and br.name == ADVICE_BRIDGE
    hd_only = select_prompt_advice(
        has_kept=True,
        hard_axioms=[AX],
        goal_fragments=[GOAL],
        dump_complete=True,
        attributed=False,
        goal_difficulty_baseline=8,
        goal_difficulty_mix=8,
    )
    assert hd_only is None or hd_only.name != ADVICE_BRIDGE


def test_initial_solve_skips_prune_and_bridge() -> None:
    data = {
        "strategy_mode": "v2",
        "repair_hints": [_hd()],
        "baseline_diag": {
            "difficulty": [[GOAL, 3]],
            "stats": {"CONJ_TOTAL": 1, "INST_TOTAL": 0, "QUANTIFIERS_SKOLEMIZE": 0},
        },
    }
    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "INITIAL SOLVE" in txt
    assert "advice: PRUNE" not in txt
    assert "advice: BRIDGE" not in txt


def test_last_attempt_v2_trigger_keeps_lemmas_only() -> None:
    data = {
        "strategy_mode": "v2",
        "useless_lemma_groups": [{
            "lemmas": [KEPT],
            "status": "timeout",
            "repair_hints": [_hd(rarely_instantiated=[AX], source_lemmas=[KEPT])],
        }],
    }
    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "LAST ATTEMPT" in txt
    assert KEPT in txt
    assert "advice: TRIGGER" in txt
    assert "<lemma>" not in txt
    assert "[used" not in txt
    assert "[unused]" not in txt


def test_missing_dump_skips_prune_bridge() -> None:
    data = {
        "strategy_mode": "v2",
        "useless_lemma_groups": [{
            "lemmas": [KEPT],
            "status": "timeout",
            "progress_signals": ["search_explosion(+90%)"],
            "difficulty_dump_complete": False,
            "difficulty_attributed": True,
            "mix_stats": {"CONJ_TOTAL": 40, "INST_TOTAL": 12},
            "goal_difficulty_baseline": 8,
            "goal_difficulty_mix": 8,
            "repair_hints": [_hd()],
        }],
        "baseline_diag": {"difficulty": []},
    }
    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "advice: PRUNE" not in txt
    assert "advice: BRIDGE" not in txt
    assert "[unused]" not in txt


def test_per_profile_attribution_not_prune_advice() -> None:
    """Inductive CONJ boom + simple named hit → BRIDGE, not PRUNE advice."""
    data = {
        "strategy_mode": "v2",
        "useless_lemma_groups": [{
            "lemmas": [KEPT],
            "status": "timeout",
            "difficulty_dump_complete": True,
            "difficulty_attributed": True,
            "attributed_ids": ["C1"],
            "candidate_ids": {"C1": KEPT},
            "per_profile": {
                "cvc5_inductive": {
                    "status": "timeout",
                    "dump_complete": True,
                    "stats": {"CONJ_TOTAL": 40, "INST_TOTAL": 12, "QUANTIFIERS_SKOLEMIZE": 2},
                },
                "cvc5_simple": {
                    "status": "timeout",
                    "dump_complete": True,
                    "goal_difficulty": 8,
                    "attributed_ids": ["C1"],
                    "stats": {"CONJ_TOTAL": 4, "INST_TOTAL": 11, "QUANTIFIERS_SKOLEMIZE": 1},
                },
            },
            "repair_hints": [_hd()],
        }],
        "baseline_diag": {
            "difficulty": [[AX, 8]],
            "dump_complete": True,
            "portfolio_results": {
                "cvc5_inductive": {
                    "dump_complete": True,
                    "stats": {"CONJ_TOTAL": 10, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 2},
                },
                "cvc5_simple": {
                    "dump_complete": True,
                    "goal_difficulty": 8,
                    "stats": {"CONJ_TOTAL": 4, "INST_TOTAL": 10, "QUANTIFIERS_SKOLEMIZE": 1},
                },
            },
        },
    }
    adv = advice_from_failed_data(data)
    assert adv is not None and adv.name == ADVICE_BRIDGE
    assert adv.constraint is None
    txt = format_attempt_feedback_for_prompt(data, backend="cvc5")
    assert "advice: PRUNE" not in txt
    assert "advice: BRIDGE" in txt


def test_v2_lemma_general_covers_both_default_modes() -> None:
    """lemma_general merges both default modes and keeps paper examples."""
    folder = ROOT / "prompts_v2" / "lemma_general"
    system = (folder / "system_prompt.txt").read_text(encoding="utf-8")
    user = (folder / "user_prompt.txt").read_text(encoding="utf-8")
    ours_eq = (
        ROOT / "prompts_ours" / "prove_prompt_equational_reasoning" / "system_prompt.txt"
    ).read_text(encoding="utf-8")
    ours_rw = (
        ROOT / "prompts_ours" / "prove_prompt_term_rewrite" / "system_prompt.txt"
    ).read_text(encoding="utf-8")

    assert "<output>" in system and "<lemma>" in system
    assert "<input>" in user and "</input>" in user
    assert "induction scheme" in system
    assert "P (succ n)" in system
    assert "qreva" in system
    assert "(declare-datatypes ((Lst 0))" in system
    assert "Example1:" in system
    assert "Example2:" in system
    assert "Example3:" in system
    assert "(= (plus zero n) n)" in system
    assert "(= (plus m n) (plus n m))" in system
    assert "Pow2 (- i 1)" in system
    assert "restored to the original form" in system
    assert "unfolds on its first argument" in system
    assert "bridges the original premise" in system
    assert "inessential" in system
    assert "PROOF PATH GOALS" in system
    assert "INVALID_GOAL" in system
    assert "possible directions" in system or "not a closed menu" in system
    assert "CASE_SPLIT" not in system
    assert "action:" not in system
    assert ":pattern" not in system
    assert len(system) < len(ours_eq) + len(ours_rw)


def test_v2_simple_lemma_general_is_compact() -> None:
    full = (
        ROOT / "prompts_v2" / "lemma_general" / "system_prompt.txt"
    ).read_text(encoding="utf-8")
    compact = (
        ROOT / "prompts_v2_compact" / "lemma_general" / "system_prompt.txt"
    ).read_text(encoding="utf-8")
    user = (
        ROOT / "prompts_v2_compact" / "lemma_general" / "user_prompt.txt"
    ).read_text(encoding="utf-8")
    assert len(compact) < len(full)
    assert "<output>" in compact and "<lemma>" in compact
    assert "<input>" in user and "</input>" in user
    assert "induction scheme" in compact
    assert "P (succ n)" in compact
    assert "qreva" in compact
    assert "(= (plus zero n) n)" in compact
    assert "(= (plus m n) (plus n m))" in compact
    assert "Pow2 (- i 1)" in compact
    assert "restored to the original form" in compact
    assert "LAST ATTEMPT" in compact
    assert "not a closed menu" in compact
    assert "CASE_SPLIT" not in compact
    assert "action:" not in compact
    assert "pick one" not in compact.lower()
    assert "PROOF PATH GOALS" in compact
    assert "INVALID_GOAL" in compact
    assert "Example1:" not in compact
    assert ":pattern" not in compact


def main() -> int:
    test_default_mode_has_no_advice()
    test_trigger_from_rare_inst()
    test_default_simple_has_no_advice()
    test_v2_simple_keeps_advice()
    test_prompt_advice_flag_off_skips_advice()
    test_vampire_backend_skips_advice()
    test_prune_uses_conj_inst_log_gain_and_goal_not_drop()
    test_generalize_needs_child_and_structure()
    test_generalize_action_split()
    test_local_vs_parent_contrast_in_last_attempt()
    test_localize_and_bridge()
    test_initial_solve_skips_prune_and_bridge()
    test_last_attempt_v2_trigger_keeps_lemmas_only()
    test_missing_dump_skips_prune_bridge()
    test_per_profile_attribution_not_prune_advice()
    test_v2_lemma_general_covers_both_default_modes()
    test_v2_simple_lemma_general_is_compact()
    print("prompt mode tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
