"""Delayed speculative direct-prove of candidate lemmas during usefulness.

Enabled only when ``LEMMA_LIBRARY`` and ``LEMMA_LIBRARY_LOCAL`` are on.
Does not replace usefulness: A∧C⊢G still runs first; A⊢c_i starts after a delay
if usefulness has not returned.
"""

from __future__ import annotations

import logging
import re
import threading
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, List, Optional, Sequence, Tuple

from exp_stats import log_exp
from obligation_tree import (
    HARVEST_CVC_PROFILES,
    HARVEST_DISPATCH_KEY,
    local_lemma_harvest_enabled,
    usefulness_harvest_delay_s,
)

UsefulnessFn = Callable[[], Tuple[bool, List[str], Any]]
ProveFn = Callable[[Path], Any]


@dataclass
class HarvestSlot:
    index: int
    formula: str
    name: str
    harvest_path: Path
    started: bool = False
    future: Optional[Future] = None
    result: Any = None


def write_negated_lemma_smt(smt_content: str, formula: str, dest: Path) -> None:
    """Replace the proof-goal block with ``(assert (not <formula>))``."""
    lemma_content = re.sub(
        r"; proof goal\s*\(assert.*?\)\s*; proof goal end",
        f"; proof goal\n(assert (not {formula}))\n; proof goal end",
        smt_content,
        flags=re.DOTALL,
    )
    dest.write_text(lemma_content, encoding="utf-8")


def make_harvest_slots(
    formulas: Sequence[str],
    smt_content: str,
    smt_dir: Path,
    goal_name: str,
) -> List[HarvestSlot]:
    slots: List[HarvestSlot] = []
    for i, formula in enumerate(formulas, 1):
        path = smt_dir / f"{goal_name}_harvest_{i}.smt2"
        write_negated_lemma_smt(smt_content, formula, path)
        slots.append(HarvestSlot(
            index=i,
            formula=formula,
            name=f"{goal_name}_{i}",
            harvest_path=path,
        ))
    return slots


def harvest_slot_kind(slot: HarvestSlot) -> str:
    if not slot.started:
        return "not_started"
    if slot.result is None:
        return "in_flight"
    if bool(getattr(slot.result, "proved", False)):
        return "proved"
    return "exhausted"


def join_harvest_slots(slots: Sequence[HarvestSlot]) -> None:
    for slot in slots:
        if slot.future is None:
            continue
        slot.result = slot.future.result()
        slot.future = None


def _start_slots(
    slots: Sequence[HarvestSlot],
    prove_fn: ProveFn,
    pool: ThreadPoolExecutor,
    *,
    goal: str,
    delay_s: float,
    profiles: Sequence[str],
) -> None:
    log_exp(
        "harvest_start",
        goal=goal,
        n_lemmas=len(slots),
        delay_s=delay_s,
        profiles=",".join(profiles),
    )
    for slot in slots:
        slot.started = True
        slot.future = pool.submit(prove_fn, slot.harvest_path)


def run_usefulness_with_delayed_harvest(
    *,
    usefulness_fn: UsefulnessFn,
    slots: Sequence[HarvestSlot],
    prove_fn: ProveFn,
    goal: str,
    delay_s: Optional[float] = None,
    enabled: Optional[bool] = None,
    profiles: Sequence[str] = HARVEST_CVC_PROFILES,
) -> Tuple[bool, List[str], Any]:
    """Run usefulness; start A⊢c_i only if it is still running after ``delay_s``.

    Always joins in-flight harvest jobs before returning (do not cancel+rerun).
    """
    delay = usefulness_harvest_delay_s() if delay_s is None else float(delay_s)
    harvest_on = local_lemma_harvest_enabled() if enabled is None else bool(enabled)
    if not harvest_on or not slots:
        return usefulness_fn()

    n_workers = 1 + max(1, len(slots))
    cancel_timer = threading.Event()
    with ThreadPoolExecutor(max_workers=n_workers) as pool:
        useful_fut = pool.submit(usefulness_fn)

        def _timer() -> None:
            if cancel_timer.wait(timeout=delay):
                return
            if useful_fut.done():
                return
            _start_slots(
                slots, prove_fn, pool, goal=goal, delay_s=delay, profiles=profiles,
            )

        timer = threading.Thread(target=_timer, name="harvest-delay", daemon=True)
        timer.start()
        try:
            useful, selected, result = useful_fut.result()
        finally:
            cancel_timer.set()
            timer.join()

        started = any(slot.started for slot in slots)
        status = str(getattr(result, "status", "") or "").lower()
        elapsed = float(getattr(result, "elapsed", 0.0) or 0.0)
        if not started:
            if useful:
                log_exp("harvest_skip", goal=goal, reason="usefulness_fast")
            elif status == "timeout" and elapsed + 1e-9 >= delay:
                logging.info("有用性 timeout 时投机尚未启动，补跑 A⊢c_i")
                _start_slots(
                    slots, prove_fn, pool, goal=goal, delay_s=delay, profiles=profiles,
                )
        join_harvest_slots(slots)
        return useful, selected, result
