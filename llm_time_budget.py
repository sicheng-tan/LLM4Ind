"""Wall-clock budget for one LLM HTTP call, leaving time for usefulness.

Usefulness prefers the paper 60s budget. The LLM per-request cap is
``LLM_TIMEOUT`` (default 180s if unset); generations rarely hit that cap, so it is
the first thing to shrink. Prefer at least 90s per LLM try.

Default (``VAMPIRE_SERIAL_DUAL`` off / paper):
1. shrink LLM toward 90s, keep 60s usefulness and HTTP retries;
2. shrink usefulness toward 2s (LLM stays ≥90s);
3. drop extra HTTP retries and re-allocate;
4. shrink LLM below 90s, leave ≥2s usefulness when possible.

With ``VAMPIRE_SERIAL_DUAL=on`` (Vampire serial tip→portfolio→integer):
1. same — shrink LLM toward 90s, keep 60s usefulness;
2. **drop HTTP retries first** (prove arms matter more than a second LLM try);
3. shrink usefulness toward **6s** (3 schedules × 2s min);
4. if still tight, **sacrifice LLM below 90s / even below 2s** so usefulness
   keeps 6s whenever ``remaining ≥ 6``; only then shrink the prove floor.
"""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any, Iterator, Optional
import logging
import os
import time

LLM_CALL_MAX_S = 180.0
LLM_CALL_PREF_S = 90.0
LLM_CALL_MIN_S = 2.0
USEFULNESS_RESERVE_MAX_S = 60.0
USEFULNESS_RESERVE_MIN_S = 2.0
# Serial dual: tip / portfolio / integer each deserve a floor slice.
SERIAL_SCHEDULE_MIN_S = 2.0
SERIAL_USEFULNESS_RESERVE_MIN_S = 3 * SERIAL_SCHEDULE_MIN_S  # 6s
# langchain ChatOpenAI default extra retries when LLM_MAX_RETRIES is unset
DEFAULT_HTTP_RETRIES = 2

_OFF = frozenset({"0", "off", "false", "no"})

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


def vampire_serial_budget_policy() -> bool:
    """Serial LLM/prove floors (3×2s, retries-before-U).

    Default **off** so CVC / paper Mate keep the old wall policy. Vampire Mate
    opts in via ``config['LLM_SERIAL_PROVE_BUDGET']`` (tied to
    ``VAMPIRE_SERIAL_DUAL``) or env ``LLM_SERIAL_PROVE_BUDGET=on``.
    Do **not** infer from ``VAMPIRE_SERIAL_DUAL`` alone — that defaults on and
    would change CVC experiments.
    """
    return os.getenv("LLM_SERIAL_PROVE_BUDGET", "off").strip().lower() not in _OFF


def usefulness_reserve_min_s(*, serial_policy: Optional[bool] = None) -> float:
    """Floor reserved for usefulness when allocating LLM timeout."""
    serial = (
        vampire_serial_budget_policy()
        if serial_policy is None
        else bool(serial_policy)
    )
    if serial:
        return float(SERIAL_USEFULNESS_RESERVE_MIN_S)
    return float(USEFULNESS_RESERVE_MIN_S)


def llm_serial_prove_budget_from_config(config: Optional[dict]) -> bool:
    """Whether this Mate run uses serial prove LLM budgeting."""
    if not config:
        return vampire_serial_budget_policy()
    if "LLM_SERIAL_PROVE_BUDGET" in config:
        return bool(config.get("LLM_SERIAL_PROVE_BUDGET"))
    return vampire_serial_budget_policy()


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
    useful_min: Optional[float] = None,
    serial_policy: Optional[bool] = None,
) -> LlmCallBudget:
    """Pick per-request timeout and HTTP retries for the current invoke."""
    retries = max(0, int(http_retries))
    lmax = float(call_max)
    lmin = float(call_min)
    lpref = min(lmax, max(lmin, float(call_pref)))
    umax = float(useful_max)
    serial = (
        vampire_serial_budget_policy()
        if serial_policy is None
        else bool(serial_policy)
    )
    umin = float(
        useful_min
        if useful_min is not None
        else (
            SERIAL_USEFULNESS_RESERVE_MIN_S
            if serial
            else USEFULNESS_RESERVE_MIN_S
        )
    )
    if remaining_s is None:
        return LlmCallBudget(False, None, None, umax)

    rem = max(0.0, float(remaining_s))
    n = 1 + retries

    if rem >= n * lmax + umax:
        return LlmCallBudget(True, lmax, retries, umax)

    # Shrink LLM toward 90s first; keep paper 60s usefulness and HTTP retries.
    if rem >= n * lpref + umax:
        return LlmCallBudget(True, min(lmax, (rem - umax) / n), retries, umax)

    if serial:
        # Vampire serial: drop HTTP retries before cutting prove budget.
        if retries > 0:
            return allocate_llm_call(
                rem,
                http_retries=0,
                call_max=lmax,
                call_pref=lpref,
                call_min=lmin,
                useful_max=umax,
                useful_min=umin,
                serial_policy=True,
            )
        # One shot: keep LLM ≥90s while usefulness still has room above floor.
        if rem >= lpref + umin:
            return LlmCallBudget(True, lpref, 0, rem - lpref)
        # Tight: **sacrifice LLM** (even below call_min) so serial prove keeps
        # umin (6s = 3×2s arms). Only when rem itself is < umin do we give up.
        if rem >= umin:
            llm_t = rem - umin
            return LlmCallBudget(True, max(llm_t, 0.1), 0, umin)
        # Task remnant < prove floor: give almost all to prove, crumb to LLM.
        llm_t = min(lmin, max(0.1, rem * 0.2))
        if llm_t >= rem:
            llm_t = max(0.1, rem * 0.2)
        return LlmCallBudget(True, llm_t, 0, max(0.0, rem - llm_t))

    # Paper / non-serial: shrink usefulness before dropping retries.
    if rem >= n * lpref + umin:
        return LlmCallBudget(True, lpref, retries, rem - n * lpref)

    if retries > 0:
        return allocate_llm_call(
            rem,
            http_retries=0,
            call_max=lmax,
            call_pref=lpref,
            call_min=lmin,
            useful_max=umax,
            useful_min=umin,
            serial_policy=False,
        )

    if rem >= lmin + umin:
        return LlmCallBudget(True, min(lmax, rem - umin), 0, umin)

    timeout = lmin if rem >= lmin else max(rem, lmin)
    reserve = max(0.0, rem - timeout)
    return LlmCallBudget(True, timeout, 0, reserve)


def usefulness_timeout_s(
    preferred: int,
    *,
    tmin: Optional[int] = None,
    serial_policy: Optional[bool] = None,
) -> int:
    """Usefulness solver timeout: prefer ``preferred``, clamp to remaining in [tmin, preferred].

    When remaining is below the floor (serial 6s / paper 2s), use whatever rem is left
    rather than requesting more wall-clock than the task still has.
    """
    if tmin is None:
        floor = int(usefulness_reserve_min_s(serial_policy=serial_policy))
    else:
        floor = int(tmin)
    preferred_i = max(1, int(preferred))
    rem = remaining_task_s()
    if rem is None:
        return max(floor, preferred_i)
    rem_i = max(0, int(rem))
    if rem_i <= 0:
        return 1
    # min(preferred, rem), but not below min(floor, rem).
    return int(max(min(floor, rem_i), min(preferred_i, rem_i)))


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
    serial = llm_serial_prove_budget_from_config(config)
    budget = allocate_llm_call(
        rem,
        http_retries=http_retries_from_config(config.get("LLM_MAX_RETRIES")),
        call_max=llm_call_max_s(config.get("LLM_TIMEOUT")),
        useful_max=float(config.get("COMBINED_CVC_TIMEOUT") or USEFULNESS_RESERVE_MAX_S),
        serial_policy=serial,
    )
    if budget.apply:
        logging.info(
            "LLM wall budget remaining=%.1fs timeout=%.1fs http_retries=%s usefulness_reserve=%.1fs serial_policy=%s",
            rem if rem is not None else -1.0,
            float(budget.timeout_s or 0.0),
            budget.max_retries,
            budget.usefulness_reserve_s,
            serial,
        )
    with apply_llm_budget(llm, budget):
        response = llm.invoke(messages)
    return response, budget
