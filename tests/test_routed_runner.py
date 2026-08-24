#!/usr/bin/env python3
"""Unit tests for primary-profile and paper-fallback runner routing."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from cvc5_runner import CvcResult, run_cvc_routed
from solver_routing import GoalSearchState
from vampire_runner import VampireResult, run_vampire_routed


def test_cvc5_routed_fallback() -> None:
    calls = []

    def fake_parallel(path, timeout, names, *, collect_stats, collect_difficulty=False):
        calls.append((timeout, list(names), collect_stats, collect_difficulty))
        if names == ["adt_structural"]:
            return CvcResult(
                status="timeout",
                strategy="adt_structural",
                elapsed=0.01,
                portfolio_results={"adt_structural": {"status": "timeout"}},
            )
        return CvcResult(
            proved=True,
            status="unsat",
            strategy="cvc5_simple",
            elapsed=0.01,
            portfolio_results={"cvc5_simple": {"status": "unsat"}},
        )

    state = GoalSearchState(
        backend="cvc5",
        candidate_profiles=["adt_structural"],
        active_profile="adt_structural",
        fallback_profiles=["cvc5_simple"],
    )
    with patch.dict(
        os.environ,
        {"SOLVER_ROUTING": "on", "SOLVER_ROUTING_FALLBACK": "on"},
        clear=False,
    ), patch("cvc5_runner._run_cvc_parallel", side_effect=fake_parallel):
        result = run_cvc_routed("unused.smt2", timeout=10, state=state)

    assert result.proved
    assert result.strategy == "cvc5_simple"
    assert [names for _, names, _, _ in calls] == [
        ["adt_structural"],
        ["cvc5_simple"],
    ]
    assert set(result.portfolio_results) == {"adt_structural", "cvc5_simple"}


def test_vampire_routed_fallback() -> None:
    calls = []

    def fake_parallel(path, timeout, names, *, collect_stats, collect_ucore, show_induction=False):
        calls.append((timeout, list(names), collect_stats, collect_ucore, show_induction))
        if names == ["struct_induction"]:
            return VampireResult(
                status="timeout",
                strategy="struct_induction",
                elapsed=0.01,
                portfolio_results={"struct_induction": {"status": "timeout"}},
            )
        return VampireResult(
            proved=True,
            status="unsat",
            strategy="induction_portfolio",
            elapsed=0.01,
            portfolio_results={"induction_portfolio": {"status": "unsat"}},
        )

    state = GoalSearchState(
        backend="vampire",
        candidate_profiles=["struct_induction"],
        active_profile="struct_induction",
        fallback_profiles=["induction_portfolio"],
    )
    with patch.dict(
        os.environ,
        {"SOLVER_ROUTING": "on", "SOLVER_ROUTING_FALLBACK": "on"},
        clear=False,
    ), patch("vampire_runner._run_vampire_parallel", side_effect=fake_parallel):
        result = run_vampire_routed("unused.smt2", timeout=10, state=state)

    assert result.proved
    assert result.strategy == "induction_portfolio"
    assert [names for _, names, _, _, _ in calls] == [
        ["struct_induction"],
        ["induction_portfolio"],
    ]
    assert set(result.portfolio_results) == {
        "struct_induction",
        "induction_portfolio",
    }


def test_routing_off_uses_paper_runner() -> None:
    cvc_result = CvcResult(status="timeout", strategy="cvc5_simple")
    with patch.dict(os.environ, {"SOLVER_ROUTING": "off"}, clear=False), patch(
        "cvc5_runner.run_cvc", return_value=cvc_result
    ) as cvc_run:
        assert run_cvc_routed(
            "unused.smt2",
            timeout=7,
            state=GoalSearchState(backend="cvc5", candidate_profiles=["adt_structural"]),
        ) is cvc_result
    cvc_run.assert_called_once_with(
        "unused.smt2", 7, collect_stats=False, collect_difficulty=False
    )

    vampire_result = VampireResult(status="timeout", strategy="induction_portfolio")
    with patch.dict(os.environ, {"SOLVER_ROUTING": "off"}, clear=False), patch(
        "vampire_runner.run_vampire", return_value=vampire_result
    ) as vampire_run:
        assert run_vampire_routed(
            "unused.smt2",
            timeout=7,
            state=GoalSearchState(backend="vampire", candidate_profiles=["struct_induction"]),
            collect_stats=False,
            collect_ucore=True,
        ) is vampire_result
    vampire_run.assert_called_once_with(
        "unused.smt2",
        7,
        collect_stats=False,
        collect_ucore=True,
        show_induction=False,
    )


def main() -> int:
    test_cvc5_routed_fallback()
    test_vampire_routed_fallback()
    test_routing_off_uses_paper_runner()
    print("routed runner tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
