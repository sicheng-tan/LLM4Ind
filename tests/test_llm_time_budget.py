#!/usr/bin/env python3
"""Wall-clock LLM budget: LLM 2–LLM_TIMEOUT, usefulness reserve 2–60s."""

from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from llm_time_budget import (
    LLM_CALL_MAX_S,
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


def test_plenty_of_time_gives_full_llm_and_usefulness() -> None:
    b = allocate_llm_call(1200, http_retries=1, call_max=180)
    assert b.apply is True
    assert b.timeout_s == 180
    assert b.max_retries == 1
    assert b.usefulness_reserve_s == 60


def test_shrink_llm_before_usefulness() -> None:
    # 2×180+60=420 > 400 ≥ 2×90+60=240 → T=(400-60)/2=170, U=60
    b = allocate_llm_call(400, http_retries=1, call_max=180)
    assert b.timeout_s == 170
    assert b.max_retries == 1
    assert b.usefulness_reserve_s == 60


def test_shrink_usefulness_only_when_llm_would_fall_below_90s() -> None:
    # 2×90+60=240 > 200 ≥ 2×90+2=182 → T=90, U=20, retries kept
    b = allocate_llm_call(200, http_retries=1, call_max=180)
    assert b.timeout_s == 90
    assert b.max_retries == 1
    assert b.usefulness_reserve_s == 20


def test_drop_retries_when_usefulness_would_fall_below_2s() -> None:
    # 2×90+2=182 > 150; one shot 90+60=150 → T=90, U=60
    b = allocate_llm_call(150, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.timeout_s == 90
    assert b.usefulness_reserve_s == 60


def test_shrink_llm_below_90s_only_after_one_shot() -> None:
    # 90+2=92 > 70 ≥ 2+2 → one try, T=68, U=2
    b = allocate_llm_call(70, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.usefulness_reserve_s == 2
    assert b.timeout_s == 68


def test_drop_http_retries_when_both_mins_need_it() -> None:
    b = allocate_llm_call(5, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.usefulness_reserve_s == 2
    assert b.timeout_s == 3


def test_last_resort_still_requests_llm_min() -> None:
    b = allocate_llm_call(3, http_retries=1, call_max=180)
    assert b.max_retries == 0
    assert b.timeout_s == 2
    assert b.usefulness_reserve_s == 1


def test_no_deadline_does_not_override() -> None:
    b = allocate_llm_call(None, http_retries=1)
    assert b.apply is False
    assert b.timeout_s is None
    assert b.max_retries is None


def test_zero_retries_is_one_try() -> None:
    b = allocate_llm_call(240, http_retries=0, call_max=180)
    assert b.timeout_s == 180
    assert b.max_retries == 0
    assert b.usefulness_reserve_s == 60
    b = allocate_llm_call(200, http_retries=0, call_max=180)
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
    assert usefulness_timeout_s(60) == 60
    set_task_deadline(10)
    try:
        got = usefulness_timeout_s(60)
        assert 2 <= got <= 10
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
    b = allocate_llm_call(100, http_retries=1, call_max=60)
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
