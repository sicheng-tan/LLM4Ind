#!/usr/bin/env python3
"""Unit tests for primary-profile and paper-fallback runner routing."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from cvc5_runner import CvcResult, cvc_portfolio_jobs, run_cvc_routed
from solver_routing import CVC5_FALLBACK_PROFILES, GoalSearchState
from vampire_runner import VampireResult, run_vampire_routed


def test_cvc5_routed_fallback() -> None:
    calls = []

    def fake_parallel(
        path, timeout, names, *, collect_stats, collect_difficulty=False,
        pattern_smt2_path=None,
    ):
        calls.append(
            (timeout, list(names), collect_stats, collect_difficulty, pattern_smt2_path)
        )
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
    assert [names for _, names, _, _, _ in calls] == [
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


def test_cvc_portfolio_jobs_four_vs_six() -> None:
    smt = Path("/tmp/goal.smt2")
    names = list(CVC5_FALLBACK_PROFILES)
    jobs4 = cvc_portfolio_jobs(names, smt, None)
    assert [j[0] for j in jobs4] == names
    assert all(j[2] == smt for j in jobs4)

    pat = Path("/tmp/goal.__pat.smt2")
    jobs6 = cvc_portfolio_jobs(names, smt, pat)
    assert [j[0] for j in jobs6] == [
        *names,
        "cvc5_simple+pattern",
        "cvc5_inductive+pattern",
    ]
    assert jobs6[4][1] == "cvc5_simple" and jobs6[4][2] == pat
    assert jobs6[5][1] == "cvc5_inductive" and jobs6[5][2] == pat

    # Pattern arms only for E-matching specs already in this wave.
    jobs = cvc_portfolio_jobs(["cvc4_default"], smt, pat)
    assert [j[0] for j in jobs] == ["cvc4_default"]
    jobs_simple = cvc_portfolio_jobs(["cvc5_simple"], smt, pat)
    assert [j[0] for j in jobs_simple] == ["cvc5_simple", "cvc5_simple+pattern"]


def test_pattern_smt2_forwarded() -> None:
    calls = []

    def fake_parallel(
        path, timeout, names, *, collect_stats, collect_difficulty=False,
        pattern_smt2_path=None,
    ):
        calls.append((list(names), pattern_smt2_path))
        return CvcResult(
            proved=True,
            status="unsat",
            strategy="cvc5_simple",
            elapsed=0.01,
            portfolio_results={"cvc5_simple": {"status": "unsat"}},
        )

    state = GoalSearchState(
        backend="cvc5",
        candidate_profiles=["cvc5_simple"],
        active_profile="cvc5_simple",
        fallback_profiles=[],
    )
    with patch.dict(
        os.environ,
        {"SOLVER_ROUTING": "on", "SOLVER_ROUTING_FALLBACK": "off"},
        clear=False,
    ), patch("cvc5_runner._run_cvc_parallel", side_effect=fake_parallel):
        run_cvc_routed(
            "unused.smt2",
            timeout=10,
            state=state,
            pattern_smt2_path="goal.__pat.smt2",
        )
        run_cvc_routed("unused.smt2", timeout=10, state=state)

    assert calls == [
        (["cvc5_simple"], "goal.__pat.smt2"),
        (["cvc5_simple"], None),
    ]


def test_routing_off_forwards_pattern_smt2() -> None:
    cvc_result = CvcResult(status="timeout", strategy="cvc5_simple")
    with patch.dict(os.environ, {"SOLVER_ROUTING": "off"}, clear=False), patch(
        "cvc5_runner.run_cvc", return_value=cvc_result
    ) as cvc_run:
        run_cvc_routed(
            "unused.smt2",
            timeout=7,
            pattern_smt2_path="pat.smt2",
        )
    cvc_run.assert_called_once_with(
        "unused.smt2",
        7,
        collect_stats=False,
        collect_difficulty=False,
        pattern_smt2_path="pat.smt2",
    )


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
    test_cvc_portfolio_jobs_four_vs_six()
    test_pattern_smt2_forwarded()
    test_routing_off_forwards_pattern_smt2()
    test_routing_off_uses_paper_runner()
    print("routed runner tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
