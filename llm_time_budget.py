"""Wall-clock budget for one LLM HTTP call, leaving time for usefulness.

Usefulness prefers the paper 60s budget (floor 2s). The LLM per-request cap is
``LLM_TIMEOUT`` (default 180s if unset); generations rarely hit that cap, so it is
the first thing to shrink. Prefer at least 90s per LLM try.

When the task deadline is tight:
1. shrink the LLM timeout toward 90s, keep 60s usefulness and HTTP retries;
2. if 90s×tries + 60s no longer fits, shrink usefulness toward 2s (LLM stays ≥90s);
3. if usefulness would fall below 2s, drop extra HTTP retries and re-allocate;
4. only then shrink the LLM below 90s, still leaving 2s for usefulness when possible.
"""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any, Iterator, Optional
import logging
import time

LLM_CALL_MAX_S = 180.0
LLM_CALL_PREF_S = 90.0
LLM_CALL_MIN_S = 2.0
USEFULNESS_RESERVE_MAX_S = 60.0
USEFULNESS_RESERVE_MIN_S = 2.0
# langchain ChatOpenAI default extra retries when LLM_MAX_RETRIES is unset
DEFAULT_HTTP_RETRIES = 2

_deadline_mono: Optional[float] = None


@dataclass(frozen=True)
class LlmCallBudget:
    apply: bool
    timeout_s: Optional[float]
    max_retries: Optional[int]
    usefulness_reserve_s: float


def set_task_deadline(timeout_s: Optional[float]) -> None:
    """Arm a monotonic deadline from now. ``timeout_s is None`` clears it."""
    global _deadline_mono
    if timeout_s is None or float(timeout_s) <= 0:
        _deadline_mono = None
        return
    _deadline_mono = time.monotonic() + float(timeout_s)


def arm_task_deadline(depth: int, timeout_s: Optional[float]) -> None:
    if int(depth) == 0:
        set_task_deadline(timeout_s)


def remaining_task_s() -> Optional[float]:
    if _deadline_mono is None:
        return None
    return _deadline_mono - time.monotonic()


def llm_call_max_s(config_timeout: Optional[float]) -> float:
    """Per-request cap: ``LLM_TIMEOUT`` if set, else 180s. Never below 2s."""
    if config_timeout:
        return max(LLM_CALL_MIN_S, float(config_timeout))
    return LLM_CALL_MAX_S


def http_retries_from_config(raw: Optional[int]) -> int:
    if raw is None:
        return DEFAULT_HTTP_RETRIES
    return max(0, int(raw))


def allocate_llm_call(
    remaining_s: Optional[float],
    *,
    http_retries: int = 0,
    call_max: float = LLM_CALL_MAX_S,
    call_pref: float = LLM_CALL_PREF_S,
    call_min: float = LLM_CALL_MIN_S,
    useful_max: float = USEFULNESS_RESERVE_MAX_S,
    useful_min: float = USEFULNESS_RESERVE_MIN_S,
) -> LlmCallBudget:
    """Pick per-request timeout and HTTP retries for the current invoke."""
    retries = max(0, int(http_retries))
    lmax = float(call_max)
    lmin = float(call_min)
    lpref = min(lmax, max(lmin, float(call_pref)))
    umax = float(useful_max)
    umin = float(useful_min)
    if remaining_s is None:
        return LlmCallBudget(False, None, None, umax)

    rem = max(0.0, float(remaining_s))
    n = 1 + retries

    if rem >= n * lmax + umax:
        return LlmCallBudget(True, lmax, retries, umax)

    # Shrink LLM toward 90s first; keep paper 60s usefulness and HTTP retries.
    if rem >= n * lpref + umax:
        return LlmCallBudget(True, min(lmax, (rem - umax) / n), retries, umax)

    # Would need LLM < 90s: shrink usefulness toward 2s instead.
    if rem >= n * lpref + umin:
        return LlmCallBudget(True, lpref, retries, rem - n * lpref)

    # Usefulness would fall below 2s: drop extra HTTP retries and re-allocate.
    if retries > 0:
        return allocate_llm_call(
            rem,
            http_retries=0,
            call_max=lmax,
            call_pref=lpref,
            call_min=lmin,
            useful_max=umax,
            useful_min=umin,
        )

    # One shot, still too tight: shrink LLM below 90s, leave usefulness if possible.
    if rem >= lmin + umin:
        return LlmCallBudget(True, min(lmax, rem - umin), 0, umin)

    timeout = lmin if rem >= lmin else max(rem, lmin)
    reserve = max(0.0, rem - timeout)
    return LlmCallBudget(True, timeout, 0, reserve)


def usefulness_timeout_s(preferred: int, *, tmin: int = 2) -> int:
    """Usefulness solver timeout: prefer ``preferred``, clamp to remaining in [tmin, preferred]."""
    preferred_i = max(int(tmin), int(preferred))
    rem = remaining_task_s()
    if rem is None:
        return preferred_i
    return int(max(tmin, min(preferred_i, rem)))


@contextmanager
def apply_llm_budget(llm: Any, budget: LlmCallBudget) -> Iterator[None]:
    if not budget.apply or type(llm).__name__ in {"MagicMock", "AsyncMock"}:
        yield
        return
    saved = {}
    for attr, value in (
        ("timeout", budget.timeout_s),
        ("request_timeout", budget.timeout_s),
        ("max_retries", budget.max_retries),
    ):
        if value is None or not hasattr(llm, attr):
            continue
        saved[attr] = getattr(llm, attr)
        try:
            setattr(llm, attr, value)
        except Exception:
            saved.pop(attr, None)
    try:
        yield
    finally:
        for attr, value in saved.items():
            try:
                setattr(llm, attr, value)
            except Exception:
                pass


def invoke_chat(
    llm: Any,
    messages: Any,
    *,
    http_retries: int,
    call_max: float,
    useful_max: float,
) -> tuple[Any, LlmCallBudget]:
    budget = allocate_llm_call(
        remaining_task_s(),
        http_retries=http_retries,
        call_max=call_max,
        useful_max=useful_max,
    )
    with apply_llm_budget(llm, budget):
        response = llm.invoke(messages)
    return response, budget


def invoke_configured_chat(llm: Any, messages: Any, config: dict) -> tuple[Any, LlmCallBudget]:
    """Allocate from remaining wall-clock, then invoke. No-op if no task deadline."""
    rem = remaining_task_s()
    budget = allocate_llm_call(
        rem,
        http_retries=http_retries_from_config(config.get("LLM_MAX_RETRIES")),
        call_max=llm_call_max_s(config.get("LLM_TIMEOUT")),
        useful_max=float(config.get("COMBINED_CVC_TIMEOUT") or USEFULNESS_RESERVE_MAX_S),
    )
    if budget.apply:
        logging.info(
            "LLM wall budget remaining=%.1fs timeout=%.1fs http_retries=%s usefulness_reserve=%.1fs",
            rem if rem is not None else -1.0,
            float(budget.timeout_s or 0.0),
            budget.max_retries,
            budget.usefulness_reserve_s,
        )
    with apply_llm_budget(llm, budget):
        response = llm.invoke(messages)
    return response, budget
