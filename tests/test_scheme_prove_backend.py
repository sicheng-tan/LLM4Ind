"""Scheme short-prove backend / profile race wiring."""

from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

from induction_scheme.constants import PROVE_PROFILES, VAMPIRE_PROVE_PROFILES
from induction_scheme.mate_glue import scheme_prove_kwargs_for_backend
from induction_scheme.prove import default_vampire_prove
from vampire_runner import VAMPIRE_PROFILES


def test_scheme_prove_profile_sets_are_four_way() -> None:
    assert len(PROVE_PROFILES) == 4
    # Vampire: paper single schedule (not a multi-arm race).
    from solver_routing import VAMPIRE_RACE_PROFILES

    assert tuple(VAMPIRE_PROVE_PROFILES) == tuple(VAMPIRE_RACE_PROFILES)
    assert VAMPIRE_PROVE_PROFILES == ("induction_portfolio",)
    assert set(VAMPIRE_PROVE_PROFILES) <= set(VAMPIRE_PROFILES)
    for name in VAMPIRE_PROVE_PROFILES:
        assert VAMPIRE_PROFILES[name]["kind"] == "portfolio"
        assert VAMPIRE_PROFILES[name]["schedule"] == "induction"


def test_scheme_prove_kwargs_select_backend() -> None:
    cvc = scheme_prove_kwargs_for_backend("cvc5")
    vamp = scheme_prove_kwargs_for_backend("vampire")
    assert cvc["profiles"] == list(PROVE_PROFILES)
    assert vamp["profiles"] == list(VAMPIRE_PROVE_PROFILES)
    assert cvc["prove_fn"] is not vamp["prove_fn"]


def test_default_vampire_prove_races_vampire_profiles() -> None:
    import os

    fake = MagicMock(proved=True, status="unsat", elapsed=0.01)
    # Explicit multi-profile list still races (not serial dual).
    with patch(
        "vampire_runner.run_vampire_race", return_value=fake
    ) as race2:
        default_vampire_prove(
            Path("/tmp/x.smt2"), 10,
            ["struct_induction", "integer_induction"],
        )
    assert race2.call_args[0][2] == ["struct_induction", "integer_induction"]

    # Default paper list → serial dual when enabled.
    with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "on"}), patch(
        "vampire_runner.run_vampire_serial", return_value=fake
    ) as serial, patch("vampire_runner.run_vampire_race") as race:
        out = default_vampire_prove(Path("/tmp/x.smt2"), 10, [])
    assert out is fake
    serial.assert_called_once()
    assert serial.call_args.kwargs.get("kind") == "scheme"
    race.assert_not_called()

    with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "off"}), patch(
        "vampire_runner.run_vampire_race", return_value=fake
    ) as race_off:
        default_vampire_prove(Path("/tmp/x.smt2"), 10, ["cvc5_inductive"])
    assert race_off.call_args[0][2] == list(VAMPIRE_PROVE_PROFILES)
