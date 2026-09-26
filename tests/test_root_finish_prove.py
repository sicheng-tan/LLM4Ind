#!/usr/bin/env python3
"""Root finish prove: longer re-prove after LLM attempts (default 120s)."""

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

from obligation_tree import root_finish_prove_timeout_s
import Mate_new as mate


def test_root_finish_timeout_default_and_off() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("ROOT_FINISH_PROVE_TIMEOUT", None)
        assert root_finish_prove_timeout_s() == 120
    for off in ("0", "off", "false", "no"):
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": off}):
            assert root_finish_prove_timeout_s() == 0
    with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "90"}):
        assert root_finish_prove_timeout_s() == 90


def test_maybe_root_finish_skips_depth_gt_zero() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "120"}), patch.object(
            mate, "perform_initial_verification",
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=1) is False
            verify.assert_not_called()


def test_maybe_root_finish_skips_when_disabled() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text("(assert true)\n(check-sat)\n", encoding="utf-8")
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "off"}), patch.object(
            mate, "perform_initial_verification",
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=0) is False
            verify.assert_not_called()


def test_maybe_root_finish_runs_without_library_growth() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text("(assert true)\n(check-sat)\n", encoding="utf-8")
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "120"}), patch(
            "Mate_new.remaining_task_s", return_value=500.0,
        ), patch.object(
            mate, "perform_initial_verification", return_value=True,
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=0) is True
            verify.assert_called_once()
            kwargs = verify.call_args.kwargs
            assert kwargs["log_event"] == "root_finish_prove"
            assert kwargs["timeout"] == 120


def test_maybe_root_finish_caps_by_remaining_budget() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        smt = Path(tmp) / "template.smt2"
        smt.write_text("(assert true)\n(check-sat)\n", encoding="utf-8")
        with patch.dict(os.environ, {"ROOT_FINISH_PROVE_TIMEOUT": "120"}), patch(
            "Mate_new.remaining_task_s", return_value=45.0,
        ), patch.object(
            mate, "perform_initial_verification", return_value=False,
        ) as verify:
            assert mate.maybe_root_finish_prove(tmp, "template", depth=0) is False
            assert verify.call_args.kwargs["timeout"] == 45


if __name__ == "__main__":
    test_root_finish_timeout_default_and_off()
    test_maybe_root_finish_skips_depth_gt_zero()
    test_maybe_root_finish_skips_when_disabled()
    test_maybe_root_finish_runs_without_library_growth()
    test_maybe_root_finish_caps_by_remaining_budget()
    print("root_finish_prove tests passed")
