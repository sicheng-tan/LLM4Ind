#!/usr/bin/env python3
"""Delayed harvest during usefulness: skip, pin, local, skip_initial."""

from __future__ import annotations

import os
import sys
import tempfile
import time
from pathlib import Path
from unittest.mock import MagicMock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from cvc5_runner import CvcResult
from obligation_tree import lemma_library_role, load_lemma_library

_GOAL = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""
_LEMMA = "(forall ((y Int)) (=> (P y) (P y)))"

_HARVEST_ENV = {
    "LEMMA_LIBRARY": "on",
    "LEMMA_LIBRARY_LOCAL": "on",
    "SOLVER_ROUTING": "off",
    "LEMMA_DEFINED_SYMBOLS": "off",
}


def _unsat(**kwargs) -> CvcResult:
    payload = {"proved": True, "status": "unsat", "elapsed": 0.01}
    payload.update(kwargs)
    return CvcResult(**payload)


def _timeout(**kwargs) -> CvcResult:
    payload = {"proved": False, "status": "timeout", "elapsed": 0.2}
    payload.update(kwargs)
    return CvcResult(**payload)


def _run_quick(tmp: str, *, delay: str, usefulness, harvest, retry=None):
    import Mate_new as mate

    env = dict(_HARVEST_ENV)
    env["USEFULNESS_HARVEST_DELAY_S"] = delay
    (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
    patches = [
        patch.dict(os.environ, env),
        patch("Mate_new.generate_lemmas_with_llm", return_value=[_LEMMA]),
        patch("Mate_new.validate_lemmas_parallel", side_effect=lambda _paths, lemmas, *_a, **_k: list(lemmas)),
        patch("Mate_new.verify_combined_lemmas", side_effect=usefulness),
        patch("Mate_new.run_cvc", side_effect=harvest),
    ]
    if retry is not None:
        patches.append(patch("Mate_new.perform_initial_verification", side_effect=retry))
    with patches[0], patches[1], patches[2], patches[3], patches[4]:
        if retry is not None:
            with patches[5]:
                return mate.quick_run(tmp, "template", "p", "./prompts_ours")
        return mate.quick_run(tmp, "template", "p", "./prompts_ours")


def test_fast_unsat_does_not_start_harvest() -> None:
    import Mate_new as mate

    harvest = MagicMock(return_value=_timeout())

    def usefulness(*_a, **_k):
        return True, [_LEMMA], _unsat(elapsed=0.01)

    with tempfile.TemporaryDirectory() as tmp:
        with patch("Mate_new.run_cvc", harvest):
            proved, subgoals, lemmas = _run_quick(
                tmp, delay="2", usefulness=usefulness, harvest=harvest,
            )
        dispatch = mate.load_failed_lemmas(tmp, "template").get("harvest_dispatch") or {}
        assert proved is True
        assert lemmas == [_LEMMA]
        assert subgoals == ["template_1"]
        assert dispatch.get("skip_initial") == []
        assert dispatch.get("pre_proved") == {}
        harvest.assert_not_called()


def test_timeout_harvest_local_retries_goal_without_prove_run() -> None:
    import Mate_new as mate

    def usefulness(*_a, **_k):
        time.sleep(0.08)
        return False, [], _timeout(elapsed=0.08)

    harvest = MagicMock(return_value=_unsat())
    retry = MagicMock(return_value=True)
    prove = MagicMock()

    with tempfile.TemporaryDirectory() as tmp:
        with patch("Mate_new.prove_run", prove):
            proved, subgoals, lemmas = _run_quick(
                tmp, delay="0.03", usefulness=usefulness, harvest=harvest, retry=retry,
            )
        stored = load_lemma_library(tmp)
        assert proved is True
        assert subgoals == []
        assert lemmas == [_LEMMA]
        assert len(stored) == 1
        assert lemma_library_role(stored[0]) == "local"
        retry.assert_called()
        prove.assert_not_called()
        assert harvest.call_count >= 1
        assert retry.call_args.kwargs.get("log_event") == "harvest_retry"
        assert retry.call_args.kwargs.get("timeout") == 2


def test_slow_unsat_proved_harvest_skips_prove_run_and_initial() -> None:
    import Mate_new as mate

    def usefulness(*_a, **_k):
        time.sleep(0.08)
        return True, [_LEMMA], _unsat(elapsed=0.08)

    harvest = MagicMock(return_value=_unsat())

    with tempfile.TemporaryDirectory() as tmp:
        proved, subgoals, lemmas = _run_quick(
            tmp, delay="0.03", usefulness=usefulness, harvest=harvest,
        )
        dispatch = mate.load_failed_lemmas(tmp, "template").get("harvest_dispatch") or {}
        stored = load_lemma_library(tmp)
        assert proved is True
        assert subgoals == []
        assert lemmas == [_LEMMA]
        assert "template_1" in (dispatch.get("pre_proved") or {})
        assert lemma_library_role(stored[0]) == "pin"
        harvest.assert_called()


def test_exhausted_harvest_unsat_sets_skip_initial() -> None:
    import Mate_new as mate

    def usefulness(*_a, **_k):
        time.sleep(0.08)
        return True, [_LEMMA], _unsat(elapsed=0.08)

    harvest = MagicMock(return_value=_timeout())

    with tempfile.TemporaryDirectory() as tmp:
        proved, subgoals, lemmas = _run_quick(
            tmp, delay="0.03", usefulness=usefulness, harvest=harvest,
        )
        dispatch = mate.load_failed_lemmas(tmp, "template").get("harvest_dispatch") or {}
        assert proved is True
        assert subgoals == ["template_1"]
        assert lemmas == [_LEMMA]
        assert dispatch.get("skip_initial") == ["template_1"]
        assert dispatch.get("pre_proved") == {}


def test_skip_initial_prove_run_does_not_call_initial() -> None:
    import Mate_new as mate

    initial = MagicMock(return_value=False)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "LLM_LEMMA_DIAGNOSIS": "off",
            "CHILD_LLM_ATTEMPTS": "1",
        }), patch("Mate_new.perform_initial_verification", initial), patch(
            "Mate_new.quick_run", return_value=(False, [], [])
        ):
            mate.prove_run(tmp, "template", depth=1, skip_initial=True)
        initial.assert_not_called()


def test_library_off_disables_harvest() -> None:
    harvest = MagicMock(return_value=_unsat())

    def usefulness(*_a, **_k):
        time.sleep(0.08)
        return False, [], _timeout(elapsed=0.08)

    import Mate_new as mate
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(_GOAL, encoding="utf-8")
        with patch.dict(os.environ, {
            "LEMMA_LIBRARY": "off",
            "LEMMA_LIBRARY_LOCAL": "on",
            "SOLVER_ROUTING": "off",
            "LEMMA_DEFINED_SYMBOLS": "off",
            "USEFULNESS_HARVEST_DELAY_S": "0.03",
        }), patch("Mate_new.generate_lemmas_with_llm", return_value=[_LEMMA]), patch(
            "Mate_new.validate_lemmas_parallel",
            side_effect=lambda _paths, lemmas, *_a, **_k: list(lemmas),
        ), patch("Mate_new.verify_combined_lemmas", side_effect=usefulness), patch(
            "Mate_new.run_cvc", harvest
        ), patch("Mate_new.perform_initial_verification", return_value=True):
            proved, subgoals, lemmas = mate.quick_run(
                tmp, "template", "p", "./prompts_ours"
            )
        assert proved is False
        assert subgoals == []
        assert lemmas == [_LEMMA]
        harvest.assert_not_called()
        assert load_lemma_library(tmp) == []


def main() -> int:
    test_fast_unsat_does_not_start_harvest()
    test_timeout_harvest_local_retries_goal_without_prove_run()
    test_slow_unsat_proved_harvest_skips_prove_run_and_initial()
    test_exhausted_harvest_unsat_sets_skip_initial()
    test_skip_initial_prove_run_does_not_call_initial()
    test_library_off_disables_harvest()
    print("lemma harvest tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
