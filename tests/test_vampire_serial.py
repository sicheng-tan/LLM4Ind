#!/usr/bin/env python3
"""Serial tip → portfolio → optional integer (one Vampire at a time)."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from vampire_runner import (
    VampireResult,
    run_vampire_routed,
    run_vampire_serial,
    should_integer_boost,
    vampire_integer_boost_s,
    vampire_integer_boost_scheme_s,
    vampire_serial_dual_enabled,
    vampire_serial_scheme_extra_s,
    vampire_serial_tip_s,
)


_ADT = """(set-logic UFDT)
(declare-datatypes ((nat 0)) (((zero) (s (p nat)))))
(assert (not (= zero zero)))
(check-sat)
"""

_INT = """(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (not (forall ((x Int)) (= (f x) (f x)))))
(check-sat)
"""


def _res(profile: str, *, proved: bool = False, status: str = "incomplete", elapsed: float = 0.05):
    return VampireResult(
        proved=proved,
        status="unsat" if proved else status,
        strategy=profile,
        elapsed=elapsed,
    )


def test_serial_defaults() -> None:
    with patch.dict(os.environ, {}, clear=False):
        for key in (
            "VAMPIRE_SERIAL_DUAL",
            "VAMPIRE_SERIAL_TIP_S",
            "VAMPIRE_SERIAL_SCHEME_EXTRA_S",
            "VAMPIRE_INTEGER_BOOST_S",
            "VAMPIRE_INTEGER_BOOST_SCHEME_S",
            "VAMPIRE_INTEGER_BOOST_ON_SCHEME",
        ):
            os.environ.pop(key, None)
        assert vampire_serial_dual_enabled() is True
        assert vampire_serial_tip_s() == 8
        assert vampire_integer_boost_s() == 8
        assert vampire_integer_boost_scheme_s() == 5
        assert vampire_serial_scheme_extra_s() == 5


def test_should_integer_boost_logic() -> None:
    assert should_integer_boost(_INT) is True
    assert should_integer_boost(_ADT) is False
    assert should_integer_boost(
        "(set-logic UFDT)\n(declare-fun __scheme_list_len (list) Int)\n"
    ) is True


def test_serial_tip_wins_early_stop() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=True)

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_ADT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_TIP_S": "8",
            "VAMPIRE_INTEGER_BOOST": "on",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            out = run_vampire_serial(path, 60, kind="main")
        assert out.proved
        assert out.strategy == "struct_induction_tip"
        assert calls == [("struct_induction_tip", 8)]
        assert set(out.portfolio_results) == {"struct_induction_tip"}
    finally:
        Path(path).unlink(missing_ok=True)


def test_serial_portfolio_gets_remainder_on_adt() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        if profile == "struct_induction_tip":
            return _res(profile, proved=False, status="incomplete", elapsed=0.1)
        return _res(profile, proved=True, elapsed=0.2)

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_ADT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_TIP_S": "8",
            "VAMPIRE_INTEGER_BOOST": "on",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            out = run_vampire_serial(path, 60, kind="main")
        assert out.proved
        assert out.strategy == "induction_portfolio"
        assert calls[0] == ("struct_induction_tip", 8)
        assert calls[1][0] == "induction_portfolio"
        # Non-Int: no reserve → portfolio ≈ full remainder.
        assert calls[1][1] >= 50
        assert "integer_induction" not in out.portfolio_results
    finally:
        Path(path).unlink(missing_ok=True)


def test_serial_int_reserves_portfolio_then_integer() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=False, status="incomplete", elapsed=0.05)

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_INT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_TIP_S": "8",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_S": "8",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            out = run_vampire_serial(path, 60, kind="main")
        assert [c[0] for c in calls] == [
            "struct_induction_tip",
            "induction_portfolio",
            "integer_induction",
        ]
        # tip 8; portfolio remain(~60)-8 ≈ 52; integer ≤8 from leftover.
        assert calls[1][1] <= 52
        assert calls[1][1] >= 45
        assert calls[2][1] <= 8
        assert out.strategy == "integer_induction"
        assert set(out.portfolio_results) == {
            "struct_induction_tip",
            "induction_portfolio",
            "integer_induction",
        }
    finally:
        Path(path).unlink(missing_ok=True)

    calls.clear()
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_ADT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_INTEGER_BOOST": "on",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            run_vampire_serial(path, 60, kind="main")
        assert [c[0] for c in calls] == [
            "struct_induction_tip",
            "induction_portfolio",
        ]
    finally:
        Path(path).unlink(missing_ok=True)


def test_scheme_gets_extra_wall_and_int_reserve() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=False, status="incomplete", elapsed=0.05)

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_INT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_SCHEME_TIP_S": "5",
            "VAMPIRE_SERIAL_SCHEME_EXTRA_S": "5",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_ON_SCHEME": "on",
            "VAMPIRE_INTEGER_BOOST_SCHEME_S": "5",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            # Caller still passes PROVE_TIMEOUT_S=10; serial adds +5 → 15.
            run_vampire_serial(path, 10, kind="scheme")
        assert calls[0] == ("struct_induction_tip", 5)
        assert calls[1][0] == "induction_portfolio"
        # T=15, tip~0, reserve 5 → portfolio ≈ 10.
        assert calls[1][1] <= 10
        assert calls[1][1] >= 8
        assert calls[2][0] == "integer_induction"
        assert calls[2][1] <= 5
    finally:
        Path(path).unlink(missing_ok=True)


def test_scheme_can_disable_integer() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=False, status="incomplete", elapsed=0.05)

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_INT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_SCHEME_TIP_S": "5",
            "VAMPIRE_SERIAL_SCHEME_EXTRA_S": "5",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_ON_SCHEME": "off",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            run_vampire_serial(path, 10, kind="scheme")
        assert calls[0][0] == "struct_induction_tip"
        assert calls[1][0] == "induction_portfolio"
        # No reserve → portfolio gets nearly full T=15 remainder.
        assert calls[1][1] >= 12
        assert all(c[0] != "integer_induction" for c in calls)
    finally:
        Path(path).unlink(missing_ok=True)


def test_serial_portfolio_unsat_skips_integer() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append(profile)
        if profile == "struct_induction_tip":
            return _res(profile, proved=False, status="incomplete")
        return _res(profile, proved=True)

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_INT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_S": "8",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            out = run_vampire_serial(path, 60, kind="main")
        assert out.proved and out.strategy == "induction_portfolio"
        assert calls == ["struct_induction_tip", "induction_portfolio"]
    finally:
        Path(path).unlink(missing_ok=True)


def test_serial_scales_tight_remain_across_port_and_int() -> None:
    """When tip already burned most of T, split remnant — do not drop portfolio."""
    import time as time_mod

    calls = []
    anchor = {"t0": None}
    real_time = time_mod.time

    def fake_time():
        if anchor["t0"] is None:
            anchor["t0"] = real_time()
            return anchor["t0"]
        n = len(calls)
        if n == 0:
            return anchor["t0"]
        if n == 1:
            return anchor["t0"] + 55.0
        port_t = next(c[1] for c in calls if c[0] == "induction_portfolio")
        if n == 2:
            return anchor["t0"] + 55.0 + float(port_t)
        return anchor["t0"] + 60.0

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=False, status="incomplete")

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_INT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_S": "8",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run), patch(
            "vampire_runner.time.time", side_effect=fake_time
        ):
            out = run_vampire_serial(path, 60, kind="main")
        names = [c[0] for c in calls]
        assert names == [
            "struct_induction_tip",
            "induction_portfolio",
            "integer_induction",
        ]
        # remain ≈ 5 after fake tip wall — both arms get a scaled slice.
        assert calls[1][1] + calls[2][1] <= 5
        assert calls[1][1] >= 1 and calls[2][1] >= 1
        assert out.strategy == "integer_induction"
    finally:
        Path(path).unlink(missing_ok=True)


def test_serial_scales_caps_when_total_short() -> None:
    """Last-round remnant T (e.g. 12s) shrinks tip/int so portfolio still runs."""
    from vampire_runner import _scale_serial_arm_caps

    tip, reserve = _scale_serial_arm_caps(12, 8, 8, want_int=True)
    assert tip + reserve + 2 <= 12
    assert tip >= 2 and reserve >= 2

    # T=6: lock 2+2+2 floors rather than scaling below 2s.
    tip6, res6 = _scale_serial_arm_caps(6, 8, 8, want_int=True)
    assert tip6 == 2 and res6 == 2

    tip4, res4 = _scale_serial_arm_caps(4, 8, 0, want_int=False)
    assert tip4 >= 2 and res4 == 0

    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=False, status="incomplete")

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_INT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_TIP_S": "8",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_S": "8",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            run_vampire_serial(path, 12, kind="main")
        assert [c[0] for c in calls] == [
            "struct_induction_tip",
            "induction_portfolio",
            "integer_induction",
        ]
        assert calls[0][1] == tip
        assert calls[1][1] >= 1
        assert calls[2][1] >= 1
        assert calls[2][1] <= reserve
        assert calls[1][1] <= 12 - reserve + 1
    finally:
        Path(path).unlink(missing_ok=True)


def test_scheme_non_int_uses_extra_wall_no_integer() -> None:
    calls = []

    def fake_run(path, timeout, **kwargs):
        profile = kwargs.get("profile")
        calls.append((profile, timeout))
        return _res(profile, proved=False, status="incomplete")

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tmp:
        tmp.write(_ADT)
        path = tmp.name
    try:
        with patch.dict(os.environ, {
            "VAMPIRE_SERIAL_DUAL": "on",
            "VAMPIRE_SERIAL_SCHEME_TIP_S": "5",
            "VAMPIRE_SERIAL_SCHEME_EXTRA_S": "5",
            "VAMPIRE_INTEGER_BOOST": "on",
            "VAMPIRE_INTEGER_BOOST_ON_SCHEME": "on",
        }), patch("vampire_runner.run_vampire", side_effect=fake_run):
            run_vampire_serial(path, 10, kind="scheme")
        assert calls[0] == ("struct_induction_tip", 5)
        assert calls[1][0] == "induction_portfolio"
        # T=15, no reserve → portfolio gets nearly full remainder.
        assert calls[1][1] >= 12
        assert all(c[0] != "integer_induction" for c in calls)
    finally:
        Path(path).unlink(missing_ok=True)


def test_routed_uses_serial_when_enabled() -> None:
    with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "on"}), patch(
        "vampire_runner.run_vampire_serial",
        return_value=_res("struct_induction_tip", proved=True),
    ) as serial, patch("vampire_runner._run_vampire_parallel") as parallel:
        out = run_vampire_routed("unused.smt2", timeout=60)
    assert out.proved
    serial.assert_called_once()
    parallel.assert_not_called()


def test_routed_falls_back_to_single_portfolio_when_serial_off() -> None:
    calls = []

    def fake_parallel(path, timeout, names, **kwargs):
        calls.append(list(names))
        return _res("induction_portfolio", proved=True)

    with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "off"}), patch(
        "vampire_runner._run_vampire_parallel", side_effect=fake_parallel
    ):
        out = run_vampire_routed("unused.smt2", timeout=60)
    assert out.proved
    assert calls == [["induction_portfolio"]]
