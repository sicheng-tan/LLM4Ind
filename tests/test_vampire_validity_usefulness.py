"""Vampire 1s validity + usefulness status/error parsing (not CVC parsers)."""

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

from vampire_runner import (
    VampireResult,
    classify_status,
    extract_vampire_error_message,
    _vampire_result_from_output,
)


_USER_ERR = (
    "User error: SMTLIB2 parse error in file goal.smt2, line 12, column 3:\n"
    "unexpected token: )\n"
)


def test_classify_and_extract_vampire_user_error() -> None:
    assert classify_status("", _USER_ERR, 1, False) == "error"
    msg = extract_vampire_error_message("", _USER_ERR)
    assert msg is not None
    assert "User error:" in msg
    assert "unexpected token" in msg
    # Must not use CVC-style "Parse Error" classifier wording as the sole signal.
    assert "Parse Error" not in (msg or "")


def test_vampire_result_from_output_fills_error_field() -> None:
    result = _vampire_result_from_output(
        "struct_induction",
        "",
        _USER_ERR,
        0.01,
        1,
        collect_ucore=False,
    )
    assert result.status == "error"
    assert result.proved is False
    assert result.error and "User error:" in result.error
    assert "unexpected token" in result.error


def test_classify_sat_unsat_timeout_not_cvc() -> None:
    assert classify_status("% SZS status Unsatisfiable\n", "", 0, False) == "unsat"
    assert classify_status("Refutation found.\n", "", 0, False) == "unsat"
    assert classify_status("% SZS status Satisfiable\n", "", 0, False) == "sat"
    assert classify_status("", "", 0, True) == "timeout"
    # Bare "user:" must not become error (Vampire uses "User error:").
    assert classify_status("user: unused\n", "", 0, False) != "error"


def test_validate_lemmas_parallel_vampire_hard_soft_keep() -> None:
    import Mate_new_vampire as mate

    lemma_bad = "(forall ((x Int)) false)"
    lemma_err = "(forall ((x Int)) (bogus x))"
    lemma_ok = "(forall ((x Int)) true)"

    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        p_bad = base / "template_valid_1.smt2"
        p_err = base / "template_valid_2.smt2"
        p_ok = base / "template_valid_3.smt2"
        for p, lemma in (
            (p_bad, lemma_bad),
            (p_err, lemma_err),
            (p_ok, lemma_ok),
        ):
            p.write_text(
                f"(set-logic ALL)\n; proof goal\n(assert {lemma})\n"
                "; proof goal end\n(check-sat)\n",
                encoding="utf-8",
            )

        def _verify(path: Path):
            if path == p_bad:
                return path, VampireResult(proved=True, status="unsat", elapsed=0.01)
            if path == p_err:
                return path, VampireResult(
                    proved=False,
                    status="error",
                    error=None,
                    stdout="",
                    stderr=_USER_ERR,
                    elapsed=0.01,
                )
            return path, VampireResult(proved=False, status="timeout", elapsed=1.0)

        with patch.dict(os.environ, {"LEMMA_FILTER_DROP": "on"}), patch(
            "Mate_new_vampire.verify_single_lemma", side_effect=_verify
        ):
            kept = mate.validate_lemmas_parallel(
                [p_bad, p_err, p_ok],
                [lemma_bad, lemma_err, lemma_ok],
                tmp,
                "template",
            )

        data = mate.load_failed_lemmas(tmp, "template")
        assert kept == [lemma_ok]
        assert len(data["invalid_lemmas"]) == 1
        reason = data["invalid_lemmas"][0]["reason"]
        assert "contradicts axioms" in reason
        assert "vampire=" in reason
        assert "cvc=" not in reason
        soft = data["soft_rejected_lemmas"]
        assert soft and soft[0]["gate"] == "solver_error"
        assert "vampire error:" in soft[0]["reason"]
        assert "User error:" in soft[0]["reason"]
        assert "cvc error" not in soft[0]["reason"]


def test_validate_does_not_use_cvc_wellformed_helper() -> None:
    """Vampire validity must not call CVC wellformed on solver stdout."""
    import Mate_new_vampire as mate

    assert not hasattr(mate, "cvc_output_wellformed_failure")
    lemma = "(forall ((x Int)) true)"
    with tempfile.TemporaryDirectory() as tmp:
        valid = Path(tmp) / "template_valid_1.smt2"
        valid.write_text(
            f"(set-logic ALL)\n; proof goal\n(assert {lemma})\n"
            "; proof goal end\n(check-sat)\n",
            encoding="utf-8",
        )
        result = VampireResult(proved=False, status="timeout", elapsed=0.2)
        with patch(
            "Mate_new_vampire.verify_single_lemma", return_value=(valid, result)
        ):
            kept = mate.validate_lemmas_parallel([valid], [lemma], tmp, "template")
        assert kept == [lemma]


def test_usefulness_records_vampire_status_not_cvc_parser() -> None:
    import Mate_new_vampire as mate

    smt = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""
    lemma = "(forall ((y Int)) (P y))"
    original_assert, _formula = mate.extract_original_goal(smt)
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "combined.smt2"
        failed = VampireResult(
            proved=False,
            status="sat",
            elapsed=0.05,
            strategy="struct_induction",
            induction_focus=["(P x)"],
        )
        with patch.dict(os.environ, {
            "SOLVER_ROUTING": "off",
            "FEEDBACK_PROGRESS": "off",
            "FEEDBACK_REPAIR_HINTS": "off",
        }), patch(
            "Mate_new_vampire.run_vampire_routed", return_value=failed
        ) as routed:
            ok, progressive, vres = mate.verify_combined_lemmas(
                original_assert,
                [lemma],
                smt,
                out,
                base_path=tmp,
                goal_name="template",
            )
        assert ok is False
        assert progressive == []
        assert vres is failed
        routed.assert_called_once()
        data = mate.load_failed_lemmas(tmp, "template")
        groups = data.get("useless_lemma_groups") or []
        assert groups
        # Record shape: {"lemmas": [...], "status": ...} when meta is set.
        last = groups[-1]
        assert isinstance(last, dict)
        assert last.get("status") == "sat"
        assert "difficulty" not in last


def test_verify_single_lemma_uses_run_vampire() -> None:
    import Mate_new_vampire as mate

    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "lemma.smt2"
        path.write_text("(assert true)\n(check-sat)\n", encoding="utf-8")
        fake = VampireResult(proved=False, status="timeout", elapsed=0.01)
        with patch("Mate_new_vampire.run_vampire", return_value=fake) as run:
            got_path, got = mate.verify_single_lemma(path)
        run.assert_called_once()
        args, kwargs = run.call_args
        assert kwargs.get("timeout", args[1] if len(args) > 1 else None) == 1
        assert got_path == path
        assert got is fake
