"""Live Vampire smoke: trivial local binary calls (skip if missing).

Mirrors ``test_real_cvc5_trivial_unsat_under_2s``. Most Vampire unit tests mock
the solver; this file exercises the real runner path on a tiny SMT.

Run::

    python3 -m pytest tests/test_vampire_live_smoke.py -q
"""

from __future__ import annotations

import os
import sys
import tempfile
import time
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("VAMPIRE_BINARY", str(ROOT / "vampire" / "vampire"))

from unittest.mock import patch

from solver_routing import VAMPIRE_RACE_PROFILES
from vampire_runner import run_vampire, run_vampire_race, run_vampire_routed

_TRIVIAL_UNSAT = """(set-logic ALL)
(assert false)
(check-sat)
"""


def _vampire_bin() -> Path:
    return Path(os.environ.get("VAMPIRE_BINARY") or (ROOT / "vampire" / "vampire"))


def _require_vampire() -> Path:
    binary = _vampire_bin()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        pytest.skip(f"no Vampire binary at {binary}")
    return binary


def test_live_vampire_trivial_unsat_under_2s() -> None:
    """Single-profile prove of ``(assert false)`` via ``run_vampire``."""
    _require_vampire()
    t0 = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "false.smt2"
        path.write_text(_TRIVIAL_UNSAT, encoding="utf-8")
        result = run_vampire(
            path,
            timeout=2,
            collect_stats=True,
            show_induction=False,
            profile="struct_single",
        )
    elapsed = time.time() - t0
    assert elapsed <= 2.5, f"live Vampire exceeded budget: {elapsed:.2f}s"
    assert result.proved and result.status == "unsat", result
    assert result.strategy == "struct_single"


def test_live_vampire_race_profiles_unsat() -> None:
    """Paper schedule race arm(s) used by usefulness / node prove / scheme."""
    _require_vampire()
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "false.smt2"
        path.write_text(_TRIVIAL_UNSAT, encoding="utf-8")
        result = run_vampire_race(
            path,
            3,
            list(VAMPIRE_RACE_PROFILES),
            collect_stats=False,
        )
    assert result.proved and result.status == "unsat", result
    assert result.strategy == "induction_portfolio"
    assert list(VAMPIRE_RACE_PROFILES) == ["induction_portfolio"]


def test_live_vampire_routed_matches_race() -> None:
    """``run_vampire_routed`` must use the same paper schedule set."""
    _require_vampire()
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "false.smt2"
        path.write_text(_TRIVIAL_UNSAT, encoding="utf-8")
        with patch.dict(os.environ, {"SOLVER_ROUTING": "off"}, clear=False):
            result = run_vampire_routed(
                path,
                timeout=3,
                collect_stats=False,
                show_induction=False,
            )
    assert result.proved and result.status == "unsat", result
    assert result.strategy == "induction_portfolio"
