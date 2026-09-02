#!/usr/bin/env python3
"""Ablation switches for PaperMate extras: feedback, prompt retarget, unproved."""

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

from exp_flags import (
    paper_schedule_prompt,
    progress_feedback_enabled,
    prompt_retarget_active,
    prompt_retarget_enabled,
    repair_hints_enabled,
    resolve_prompt_pack,
    unproved_not_invalid_enabled,
)
from lemma_gates import (
    defined_symbols_enabled,
    llm_lemma_diagnosis_enabled,
    subgoal_sat_abort_enabled,
)

_FLAG_NAMES = (
    "FEEDBACK_REPAIR_HINTS",
    "FEEDBACK_PROGRESS",
    "PROMPT_RETARGET",
    "UNPROVED_NOT_INVALID",
    "SUBGOAL_SAT_ABORT",
    "LEMMA_DEFINED_SYMBOLS",
    "LLM_LEMMA_DIAGNOSIS",
)

_FEEDBACK_PAYLOAD = {
    "invalid_lemmas": [],
    "useless_lemma_groups": [{"lemmas": ["(L1)"], "status": "timeout"}],
    "progress_lemmas": [{"lemma": "(L1)", "score": 1.2, "signals": ["more_instantiations"]}],
    "unproved_lemmas": [{"lemma": "(L2)", "status": "useful_but_unproved"}],
    "repair_hints": [{"kind": "need_rewrite", "detail": "rewrite more"}],
    "routing": {
        "backend": "cvc5",
        "active_profile": "adt_structural",
        "candidate_profiles": ["adt_structural"],
        "decision_mode": "relative",
        "decision_source": "relative",
        "theory_features": {"has_adt": True, "has_int": False, "mixed_adt_lia": False},
    },
}

_GOAL_SMT = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""


def _clear_flags():
    env = {name: os.environ.pop(name) for name in _FLAG_NAMES if name in os.environ}
    return env


def _restore_flags(saved):
    for name in _FLAG_NAMES:
        os.environ.pop(name, None)
    os.environ.update(saved)


def test_flags_default_on() -> None:
    saved = _clear_flags()
    try:
        assert repair_hints_enabled() is True
        assert progress_feedback_enabled() is True
        assert prompt_retarget_enabled() is True
        assert unproved_not_invalid_enabled() is True
        assert subgoal_sat_abort_enabled() is True
        assert defined_symbols_enabled() is True
        assert llm_lemma_diagnosis_enabled() is True
    finally:
        _restore_flags(saved)
    for val in ("off", "0", "false", "no"):
        with patch.dict(os.environ, {"FEEDBACK_REPAIR_HINTS": val}):
            assert repair_hints_enabled() is False
        with patch.dict(os.environ, {"FEEDBACK_PROGRESS": val}):
            assert progress_feedback_enabled() is False
        with patch.dict(os.environ, {"PROMPT_RETARGET": val}):
            assert prompt_retarget_enabled() is False
        with patch.dict(os.environ, {"UNPROVED_NOT_INVALID": val}):
            assert unproved_not_invalid_enabled() is False
        with patch.dict(os.environ, {"SUBGOAL_SAT_ABORT": val}):
            assert subgoal_sat_abort_enabled() is False
        with patch.dict(os.environ, {"LEMMA_DEFINED_SYMBOLS": val}):
            assert defined_symbols_enabled() is False
        with patch.dict(os.environ, {"LLM_LEMMA_DIAGNOSIS": val}):
            assert llm_lemma_diagnosis_enabled() is False


def test_resolve_prompt_pack() -> None:
    ours = resolve_prompt_pack("default", 3)
    assert ours["folder_path"] == "./prompts_ours"
    assert ours["strategies"] == [
        "prove_prompt_equational_reasoning",
        "prove_prompt_term_rewrite",
    ]
    assert ours["total_attempts"] == 6
    naive = resolve_prompt_pack("naive", 3)
    assert naive["folder_path"] == "./prompts_naive"
    assert naive["strategies"] == ["prompt_naive"]
    assert naive["total_attempts"] == 6
    assert prompt_retarget_active(len(naive["strategies"])) is False
    zero = resolve_prompt_pack("zero_shot", 3)
    assert zero["folder_path"] == "./prompts_ours"
    assert zero["total_attempts"] == 6


def test_naive_strategy_repeats_prompt_naive() -> None:
    import Mate_new as mate

    calls: list[str] = []

    def fake_quick_run(_base, _name, prompt_strategy, folder_path, *_args, **_kwargs):
        calls.append((prompt_strategy, folder_path))
        return False, [], []

    saved = _clear_flags()
    try:
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "template.smt2").write_text(_GOAL_SMT, encoding="utf-8")
            with patch.dict(os.environ, {"PROMPT_RETARGET": "on"}), patch(
                "Mate_new.routing_enabled", return_value=False
            ), patch(
                "Mate_new.perform_initial_verification", return_value=False
            ), patch("Mate_new.quick_run", side_effect=fake_quick_run), patch.dict(
                mate.config, {"MAX_ATTEMPTS_PER_PROMPT": 3}
            ):
                assert mate.prove_run(tmp, "template", strategy_mode="naive") is False
    finally:
        _restore_flags(saved)

    assert len(calls) == 6, calls
    assert all(name == "prompt_naive" for name, _folder in calls)
    assert all(folder == "./prompts_naive" for _name, folder in calls)


def test_paper_schedule_prompt() -> None:
    strats = ["prove_prompt_equational_reasoning", "prove_prompt_term_rewrite"]
    assert paper_schedule_prompt(strats, 0, 3) == "prove_prompt_equational_reasoning"
    assert paper_schedule_prompt(strats, 2, 3) == "prove_prompt_equational_reasoning"
    assert paper_schedule_prompt(strats, 3, 3) == "prove_prompt_term_rewrite"
    assert paper_schedule_prompt(strats, 5, 3) == "prove_prompt_term_rewrite"
    assert paper_schedule_prompt(strats, 99, 3) == "prove_prompt_term_rewrite"
    assert paper_schedule_prompt([], 0, 3) == ""


def test_prompt_hides_disabled_feedback_sections() -> None:
    import Mate_new as mate

    on_txt = mate.format_solver_feedback_for_prompt(_FEEDBACK_PAYLOAD)
    assert "SOLVER PROGRESS SIGNALS" in on_txt
    assert "USEFUL BUT UNPROVED" in on_txt
    assert "SOLVER-GUIDED REPAIR" in on_txt
    assert "SOLVER ROUTING" in on_txt
    assert "Useless group" in on_txt

    with patch.dict(os.environ, {
        "FEEDBACK_REPAIR_HINTS": "off",
        "FEEDBACK_PROGRESS": "off",
        "UNPROVED_NOT_INVALID": "off",
        "SOLVER_ROUTING": "off",
    }):
        off_txt = mate.format_solver_feedback_for_prompt(_FEEDBACK_PAYLOAD)
    assert "SOLVER PROGRESS SIGNALS" not in off_txt
    assert "USEFUL BUT UNPROVED" not in off_txt
    assert "SOLVER-GUIDED REPAIR" not in off_txt
    assert "SOLVER ROUTING" not in off_txt
    assert "Useless group" in off_txt


def test_add_repair_and_progress_respect_flags() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"FEEDBACK_REPAIR_HINTS": "off"}):
            mate.add_repair_hints(tmp, "template", [{"kind": "need_rewrite", "detail": "x"}])
        assert mate.load_failed_lemmas(tmp, "template")["repair_hints"] == []

        with patch.dict(os.environ, {"FEEDBACK_PROGRESS": "off"}):
            mate.add_progress_lemma(tmp, "template", "(L)", 1.0, ["sig"])
        assert mate.load_failed_lemmas(tmp, "template")["progress_lemmas"] == []

        mate.add_repair_hints(tmp, "template", [{"kind": "need_rewrite", "detail": "x"}])
        mate.add_progress_lemma(tmp, "template", "(L)", 1.0, ["sig"])
        data = mate.load_failed_lemmas(tmp, "template")
        assert data["repair_hints"][0]["kind"] == "need_rewrite"
        assert data["progress_lemmas"][0]["lemma"] == "(L)"


def test_progress_flag_skips_sidecar() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    with tempfile.TemporaryDirectory() as tmp:
        mate._store_cached_diag(
            tmp, "template", "baseline_diag",
            CvcResult(status="timeout", elapsed=60.0, stats={"CONJ_TOTAL": 8}),
        )
        with patch.dict(os.environ, {"FEEDBACK_PROGRESS": "off"}), patch(
            "Mate_new.run_cvc_diagnostic"
        ) as diag:
            ordered, _ = mate.analyze_lemma_progress(
                ["(forall ((x Int)) (P x))"],
                _GOAL_SMT,
                Path(tmp),
                "template",
                tmp,
            )
        assert ordered == []
        diag.assert_not_called()


def test_unproved_flag_writes_invalid() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    child = CvcResult(status="timeout", stats={"INST_TOTAL": 2}, strategy="cvc5_inductive")
    with tempfile.TemporaryDirectory() as tmp:
        mate._store_cached_diag(tmp, "template_1", "baseline_diag", child)
        with patch.dict(os.environ, {"UNPROVED_NOT_INVALID": "off"}), patch(
            "Mate_new.run_cvc_diagnostic"
        ) as diag:
            mate._record_subgoal_failure_feedback(
                tmp, "template", "template_1", ["(assert true)"]
            )
        diag.assert_not_called()
        parent = mate.load_failed_lemmas(tmp, "template")
        assert parent["unproved_lemmas"] == []
        assert parent["invalid_lemmas"][0]["lemma"] == "(assert true)"
        assert "Subgoal proof failed" in parent["invalid_lemmas"][0]["reason"]


def test_repair_hints_off_skips_subgoal_diagnostic() -> None:
    import Mate_new as mate

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template_1.smt2").write_text(_GOAL_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"FEEDBACK_REPAIR_HINTS": "off"}), patch(
            "Mate_new.run_cvc_diagnostic"
        ) as diag:
            mate._record_subgoal_failure_feedback(
                tmp, "template", "template_1", ["(assert true)"]
            )
        diag.assert_not_called()
        parent = mate.load_failed_lemmas(tmp, "template")
        assert parent["repair_hints"] == []
        assert parent["unproved_lemmas"] == []
        assert parent["invalid_lemmas"] == []


def test_prompt_retarget_off_uses_paper_order() -> None:
    import Mate_new as mate

    calls: list[str] = []

    def fake_quick_run(_base, _name, prompt_strategy, *_args, **_kwargs):
        calls.append(prompt_strategy)
        return False, [], []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL_SMT, encoding="utf-8")
        mate.add_repair_hints(
            tmp, "template",
            [{"kind": "need_stronger_lemma", "detail": "strengthen", "context": "goal"}],
        )
        with patch.dict(os.environ, {"PROMPT_RETARGET": "off"}), patch(
            "Mate_new.routing_enabled", return_value=False
        ), patch(
            "Mate_new.perform_initial_verification", return_value=False
        ), patch("Mate_new.quick_run", side_effect=fake_quick_run), patch.dict(
            mate.config, {"MAX_ATTEMPTS_PER_PROMPT": 3}
        ):
            assert mate.prove_run(tmp, "template") is False

    assert calls == (
        ["prove_prompt_equational_reasoning"] * 3
        + ["prove_prompt_term_rewrite"] * 3
    ), calls


def test_vampire_prompt_and_paper_order_respect_flags() -> None:
    import Mate_new_vampire as mate_v

    txt = mate_v.format_solver_feedback_for_prompt(_FEEDBACK_PAYLOAD)
    assert "SOLVER-GUIDED REPAIR" in txt
    with patch.dict(os.environ, {"FEEDBACK_REPAIR_HINTS": "off", "FEEDBACK_PROGRESS": "off"}):
        off_txt = mate_v.format_solver_feedback_for_prompt(_FEEDBACK_PAYLOAD)
    assert "SOLVER-GUIDED REPAIR" not in off_txt
    assert "SOLVER PROGRESS SIGNALS" not in off_txt

    calls: list[str] = []

    def fake_quick(_base, _name, prompt_strategy, *_args, **_kwargs):
        calls.append(prompt_strategy)
        return False, [], []

    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL_SMT, encoding="utf-8")
        with patch.dict(os.environ, {"PROMPT_RETARGET": "off"}), patch(
            "Mate_new_vampire.routing_enabled", return_value=False
        ), patch(
            "Mate_new_vampire.perform_initial_verification", return_value=False
        ), patch("Mate_new_vampire.quick_run", side_effect=fake_quick), patch.dict(
            mate_v.config, {"MAX_ATTEMPTS_PER_PROMPT": 3}
        ):
            assert mate_v.prove_run(tmp, "template") is False
    assert calls[:3] == ["prove_prompt_equational_reasoning"] * 3
    assert calls[3:] == ["prove_prompt_term_rewrite"] * 3


def main() -> int:
    test_flags_default_on()
    test_resolve_prompt_pack()
    test_paper_schedule_prompt()
    test_prompt_hides_disabled_feedback_sections()
    test_add_repair_and_progress_respect_flags()
    test_progress_flag_skips_sidecar()
    test_unproved_flag_writes_invalid()
    test_repair_hints_off_skips_subgoal_diagnostic()
    test_prompt_retarget_off_uses_paper_order()
    test_naive_strategy_repeats_prompt_naive()
    test_vampire_prompt_and_paper_order_respect_flags()
    print("exp flag tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
