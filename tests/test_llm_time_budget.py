#!/usr/bin/env python3
"""Wall-clock LLM budget: LLM 2–LLM_TIMEOUT, usefulness reserve 2–60s (6s serial)."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from llm_time_budget import (
    LLM_CALL_MAX_S,
    SERIAL_USEFULNESS_RESERVE_MIN_S,
    allocate_llm_call,
    apply_llm_budget,
    arm_task_deadline,
    http_retries_from_config,
    invoke_chat,
    invoke_configured_chat,
    llm_call_max_s,
    remaining_task_s,
    set_task_deadline,
    usefulness_timeout_s,
)


def _paper(remaining_s, **kwargs):
    """Legacy paper policy (no serial dual floors / order)."""
    kwargs.setdefault("serial_policy", False)
    kwargs.setdefault("useful_min", 2.0)
    return allocate_llm_call(remaining_s, **kwargs)


def test_plenty_of_time_gives_full_llm_and_usefulness() -> None:
    b = _paper(1200, http_retries=1, call_max=180)
    assert b.apply is True
    assert b.timeout_s == 180
    assert b.max_retries == 1
    assert b.usefulness_reserve_s == 60


def test_shrink_llm_before_usefulness() -> None:
    # 2×180+60=420 > 400 ≥ 2×90+60=240 → T=(400-60)/2=170, U=60
    b = _paper(400, http_retries=1, call_max=180)
    assert b.timeout_s == 170
    assert b.max_retries == 1
    assert b.usefulness_reserve_s == 60


def test_shrink_usefulness_only_when_llm_would_fall_below_90s() -> None:
    # Paper: 2×90+60=240 > 200 ≥ 2×90+2=182 → T=90, U=20, retries kept
    b = _paper(200, http_retries=1, call_max=180)
    assert b.timeout_s == 90
    assert b.max_retries == 1
    assert b.usefulness_reserve_s == 20


def test_drop_retries_when_usefulness_would_fall_below_2s() -> None:
    # Paper: 2×90+2=182 > 150; one shot 90+60=150 → T=90, U=60
    b = _paper(150, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.timeout_s == 90
    assert b.usefulness_reserve_s == 60


def test_shrink_llm_below_90s_only_after_one_shot() -> None:
    # Paper: 90+2=92 > 70 ≥ 2+2 → one try, T=68, U=2
    b = _paper(70, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.usefulness_reserve_s == 2
    assert b.timeout_s == 68


def test_serial_drops_retries_before_shrinking_usefulness() -> None:
    # Serial: rem=200 < 2×90+60; drop retries → 90+60=150 fits → U stays 60.
    b = allocate_llm_call(
        200, http_retries=1, call_max=180, serial_policy=True, useful_min=6.0,
    )
    assert b.max_retries == 0
    assert b.timeout_s == 140  # (200-60)/1
    assert b.usefulness_reserve_s == 60


def test_serial_usefulness_floor_is_six() -> None:
    # One shot, rem=100: 90+6 ≤ 100 → T=90, U=10
    b = allocate_llm_call(
        100, http_retries=0, call_max=180, serial_policy=True, useful_min=6.0,
    )
    assert b.timeout_s == 90
    assert b.usefulness_reserve_s == 10
    # rem=95 < 90+6: sacrifice LLM to keep U=6
    b2 = allocate_llm_call(
        95, http_retries=0, call_max=180, serial_policy=True, useful_min=6.0,
    )
    assert b2.timeout_s == 89
    assert b2.usefulness_reserve_s == 6
    # rem=7: still U=6, LLM only 1s (< call_min 2)
    b3 = allocate_llm_call(
        7, http_retries=0, call_max=180, serial_policy=True, useful_min=6.0,
    )
    assert b3.usefulness_reserve_s == 6
    assert b3.timeout_s == 1.0
    assert SERIAL_USEFULNESS_RESERVE_MIN_S == 6.0


def test_serial_policy_follows_config_not_vampire_dual_alone() -> None:
    # VAMPIRE_SERIAL_DUAL=on must NOT flip LLM policy by itself (CVC safety).
    with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "on", "LLM_SERIAL_PROVE_BUDGET": "off"}):
        b = allocate_llm_call(200, http_retries=1, call_max=180)
        assert b.max_retries == 1
        assert b.timeout_s == 90
        assert b.usefulness_reserve_s == 20
    with patch.dict(os.environ, {"LLM_SERIAL_PROVE_BUDGET": "on"}):
        b = allocate_llm_call(200, http_retries=1, call_max=180)
        assert b.max_retries == 0
        assert b.usefulness_reserve_s == 60
    # Vampire Mate opts in via config even if env opt-in is off.
    with patch.dict(os.environ, {"LLM_SERIAL_PROVE_BUDGET": "off"}):
        class _Llm:
            timeout = 180
            max_retries = 1

            def invoke(self, messages):
                return "ok"

        set_task_deadline(200)
        try:
            _out, budget = invoke_configured_chat(
                _Llm(),
                ["m"],
                {
                    "LLM_TIMEOUT": 180,
                    "LLM_MAX_RETRIES": 1,
                    "COMBINED_CVC_TIMEOUT": 60,
                    "LLM_SERIAL_PROVE_BUDGET": True,
                },
            )
            assert budget.max_retries == 0
            assert budget.usefulness_reserve_s == 60
        finally:
            set_task_deadline(None)


def test_drop_http_retries_when_both_mins_need_it() -> None:
    b = _paper(5, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.usefulness_reserve_s == 2
    assert b.timeout_s == 3


def test_last_resort_still_requests_llm_min() -> None:
    b = _paper(3, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.timeout_s == 2
    assert b.usefulness_reserve_s == 1


def test_no_deadline_does_not_override() -> None:
    b = allocate_llm_call(None, http_retries=1, serial_policy=False)
    assert b.apply is False
    assert b.timeout_s is None
    assert b.max_retries is None


def test_zero_retries_is_one_try() -> None:
    b = _paper(240, http_retries=0, call_max=180)
    assert b.timeout_s == 180
    assert b.max_retries == 0
    assert b.usefulness_reserve_s == 60
    b = _paper(200, http_retries=0, call_max=180)
    assert b.timeout_s == 140
    assert b.usefulness_reserve_s == 60


def test_llm_call_max_respects_config() -> None:
    assert llm_call_max_s(None) == LLM_CALL_MAX_S
    assert llm_call_max_s(180) == 180
    assert llm_call_max_s(30) == 30


def test_http_retries_none_uses_langchain_default() -> None:
    assert http_retries_from_config(None) == 2
    assert http_retries_from_config(0) == 0
    assert http_retries_from_config(1) == 1


def test_usefulness_timeout_clamps_to_remaining() -> None:
    set_task_deadline(None)
    assert usefulness_timeout_s(60, serial_policy=False) == 60
    set_task_deadline(10)
    try:
        got = usefulness_timeout_s(60, serial_policy=False)
        assert 2 <= got <= 10
        got = usefulness_timeout_s(60, serial_policy=True)
        assert 6 <= got <= 10
    finally:
        set_task_deadline(None)


def test_arm_only_at_root() -> None:
    set_task_deadline(None)
    arm_task_deadline(1, 1200)
    assert remaining_task_s() is None
    arm_task_deadline(0, 1200)
    try:
        rem = remaining_task_s()
        assert rem is not None and 1190 < rem <= 1200
    finally:
        set_task_deadline(None)


def test_apply_budget_sets_and_restores() -> None:
    llm = SimpleNamespace(timeout=180.0, max_retries=1, request_timeout=180.0)
    b = _paper(100, http_retries=1, call_max=60)
    with apply_llm_budget(llm, b):
        assert llm.timeout == b.timeout_s
        assert llm.max_retries == b.max_retries
    assert llm.timeout == 180.0
    assert llm.max_retries == 1


def test_invoke_chat_returns_budget() -> None:
    class _Llm:
        def __init__(self):
            self.timeout = 180
            self.max_retries = 1
            self.seen = None

        def invoke(self, messages):
            self.seen = (self.timeout, self.max_retries, messages)
            return "ok"

    set_task_deadline(1200)
    try:
        with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "off"}):
            llm = _Llm()
            out, budget = invoke_chat(
                llm, ["m"], http_retries=1, call_max=60, useful_max=60,
            )
            assert out == "ok"
            assert budget.timeout_s == 60
            assert llm.seen[0] == 60
            assert llm.timeout == 180
    finally:
        set_task_deadline(None)


def test_invoke_configured_chat_uses_config_caps() -> None:
    class _Llm:
        def __init__(self):
            self.timeout = 180
            self.max_retries = 1

        def invoke(self, messages):
            return "ok"

    set_task_deadline(1200)
    try:
        with patch.dict(os.environ, {"VAMPIRE_SERIAL_DUAL": "off"}):
            out, budget = invoke_configured_chat(
                _Llm(),
                ["m"],
                {"LLM_TIMEOUT": 180, "LLM_MAX_RETRIES": 1, "COMBINED_CVC_TIMEOUT": 60},
            )
            assert out == "ok"
            assert budget.timeout_s == 180
            assert budget.max_retries == 1
            assert budget.usefulness_reserve_s == 60
    finally:
        set_task_deadline(None)


if __name__ == "__main__":
    test_plenty_of_time_gives_full_llm_and_usefulness()
    test_shrink_llm_before_usefulness()
    test_shrink_usefulness_only_when_llm_would_fall_below_90s()
    test_drop_retries_when_usefulness_would_fall_below_2s()
    test_shrink_llm_below_90s_only_after_one_shot()
    test_serial_drops_retries_before_shrinking_usefulness()
    test_serial_usefulness_floor_is_six()
    test_serial_policy_follows_env_flag()
    test_drop_http_retries_when_both_mins_need_it()
    test_last_resort_still_requests_llm_min()
    test_no_deadline_does_not_override()
    test_zero_retries_is_one_try()
    test_llm_call_max_respects_config()
    test_http_retries_none_uses_langchain_default()
    test_usefulness_timeout_clamps_to_remaining()
    test_arm_only_at_root()
    test_apply_budget_sets_and_restores()
    test_invoke_chat_returns_budget()
    test_invoke_configured_chat_uses_config_caps()
    print("llm time budget tests passed")
