#!/usr/bin/env python3
"""Mock-LLM, real-Vampire simulation of the two case-study problems.

Routing is off. The lemma generator is scripted; Vampire still does initial
prove, filter, usefulness, and recursive subgoal proofs.

Run from the repo root:

    python3 tests/test_case_mock_llm_vampire.py
"""

from __future__ import annotations

import json
import logging
import os
import re
import shutil
import sys
import time
from datetime import datetime
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ["OPENAI_API_KEY"] = os.environ.get("OPENAI_API_KEY") or "unit-test-placeholder"
os.environ.setdefault("MODEL_TYPE", "gpt-4o")
os.environ["SOLVER_ROUTING"] = "off"
os.environ["SOLVER_ROUTING_PROBES"] = "off"
os.environ["VAMPIRE_BINARY"] = str(ROOT / "vampire" / "vampire")
os.environ.setdefault("MAX_PARALLEL_TASKS", "1")

from exp_stats import load_task_summary, write_results_csv  # noqa: E402

CASES = ROOT / "experiments" / "cases"
RESULTS = ROOT / "experiments" / "results"
VAMPIRE_BIN = ROOT / "vampire" / "vampire"

# Empirically: A ∧ rev_app ⊢ rev(rev x)=x (0.2s); Vampire proves rev_app alone in ~15s.
REV_APP = "(forall ((x lst) (y lst)) (= (rev (app x y)) (app (rev y) (rev x))))"
APP_ASSOC = "(forall ((x lst) (y lst) (z lst)) (= (app (app x y) z) (app x (app y z))))"
APP_NIL = "(forall ((x lst)) (= (app x nil) x))"
# Empirically: A ∧ len_snoc ⊢ len(rev x)=len x; Vampire proves len_snoc in 0.02s.
LEN_SNOC = "(forall ((x Lst) (y Nat)) (= (len (append x (cons y nil))) (succ (len x))))"

_SPACE = re.compile(r"\s+")


def _compact(text: str) -> str:
    return _SPACE.sub(" ", text)


def wrap_lemmas(*lemmas: str) -> str:
    body = "\n".join(lemmas)
    return f"; Output begin\n{body}\n; Output end"


def lemmas_for_prompt(text: str) -> list[str]:
    compact = _compact(text)
    if "(= (rev (rev x)) x)" in compact:
        return [REV_APP]
    if "(= (len (rev x)) (len x))" in compact:
        return [LEN_SNOC]
    if "(= (rev (app x y)) (app (rev y) (rev x)))" in compact:
        return [APP_ASSOC, APP_NIL]
    if "(= (len (append x (cons y nil))) (succ (len x)))" in compact:
        return [LEN_SNOC]
    return []


def _message_text(messages) -> str:
    parts: list[str] = []
    for item in messages:
        if isinstance(item, dict):
            parts.append(str(item.get("content") or ""))
        else:
            parts.append(str(getattr(item, "content", item)))
    return "\n".join(parts)


class ScriptedLLM:
    """Drop-in for ChatOpenAI: returns canned lemmas, never hits the network."""

    def __init__(self) -> None:
        self.calls: list[dict] = []

    def invoke(self, messages, **_kwargs):
        text = _message_text(messages)
        lemmas = lemmas_for_prompt(text)
        self.calls.append(
            {
                "n_lemmas": len(lemmas),
                "lemmas": lemmas,
                "prompt_chars": len(text),
            }
        )
        logging.info("[mock-llm] call=%s lemmas=%s", len(self.calls), lemmas)
        return SimpleNamespace(content=wrap_lemmas(*lemmas))


def _ok(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _attach_task_log(folder: Path) -> logging.FileHandler:
    log_path = folder / (datetime.now().strftime("%Y%m%d_%H%M%S") + ".log")
    handler = logging.FileHandler(log_path, mode="w", encoding="utf-8")
    handler.setFormatter(
        logging.Formatter("%(asctime)s - %(levelname)s - %(message)s", "%Y-%m-%d %H:%M:%S")
    )
    root = logging.getLogger()
    root.setLevel(logging.INFO)
    root.addHandler(handler)
    return handler


def _run_one(mate, fake: ScriptedLLM, src: Path, dest: Path) -> tuple[bool, float, dict]:
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(src, dest)
    handler = _attach_task_log(dest)
    calls_before = len(fake.calls)
    started = time.time()
    try:
        proved = mate.prove_run(str(dest), "template", strategy_mode="default")
    finally:
        logging.getLogger().removeHandler(handler)
        handler.close()
    elapsed = time.time() - started
    summary = load_task_summary(str(dest)) or {}
    summary["n_mock_llm_calls"] = len(fake.calls) - calls_before
    return bool(proved), elapsed, summary


def _assert_updated_pipeline(name: str, proved: bool, summary: dict, mock_calls: int) -> None:
    _ok(proved, f"{name} was not proved")
    _ok(summary.get("solved_by") in ("llm", "llm_subgoals") or summary.get("exit_reason") in (
        "llm_subgoals",
        "llm_no_subgoals",
    ), f"{name} exit={summary.get('exit_reason')} solved_by={summary.get('solved_by')}")
    _ok(mock_calls >= 1, f"{name} never called the mock LLM")
    flags = str(summary.get("flags") or "")
    _ok("SOLVER_ROUTING=off" in flags, f"{name} routing not off: {flags}")
    solver_s = float(summary.get("solver_s") or 0)
    _ok(solver_s > 0, f"{name} did not record Vampire time")
    hints = summary.get("hint_kinds") or []
    _ok(bool(hints), f"{name} missing repair hints from the failed initial prove")
    _ok(
        int(summary.get("n_library_lemmas") or 0) >= 1
        or int(summary.get("n_subgoals_proved") or 0) >= 1
        or int(summary.get("n_obligation_trees") or 0) >= 1,
        f"{name} did not record a recursive obligation/library: {summary}",
    )


def test_mock_llm_case_experiments(result_parent: Path | None = None) -> Path:
    if not VAMPIRE_BIN.is_file() or not os.access(VAMPIRE_BIN, os.X_OK):
        raise AssertionError(f"Vampire binary missing or not executable: {VAMPIRE_BIN}")
    for name in ("p1_rev_rev", "p2_len_rev"):
        src = CASES / name / "template.smt2"
        _ok(src.is_file(), f"missing case file {src}")

    import Mate_new_vampire as mate

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = (result_parent or RESULTS) / f"{stamp}_mock_llm_cases"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "SOURCES.txt").write_text(
        "mock LLM + real Vampire; SOLVER_ROUTING=off\n"
        "p1_rev_rev: experiments/cases/p1_rev_rev\n"
        "p2_len_rev: experiments/cases/p2_len_rev\n",
        encoding="utf-8",
    )

    fake = ScriptedLLM()
    env = {
        "SOLVER_ROUTING": "off",
        "SOLVER_ROUTING_PROBES": "off",
        "VAMPIRE_BINARY": str(VAMPIRE_BIN),
        "LEMMA_LIBRARY": "on",
        "OBLIGATION_TREE": "on",
        "FEEDBACK_REPAIR_HINTS": "on",
        "FEEDBACK_PROGRESS": "on",
        "PROMPT_RETARGET": "on",
        "UNPROVED_NOT_INVALID": "on",
        "SUBGOAL_SAT_ABORT": "on",
        "LEMMA_DEFINED_SYMBOLS": "on",
        "LLM_LEMMA_DIAGNOSIS": "on",
        "CHILD_LLM_ATTEMPTS": "2",
    }
    results: list[tuple] = []
    with patch.dict(os.environ, env, clear=False), patch.object(mate, "llm", fake):
        for name in ("p1_rev_rev", "p2_len_rev"):
            dest = run_dir / name
            print(f"=== {name} ===", flush=True)
            proved, elapsed, summary = _run_one(mate, fake, CASES / name, dest)
            print(
                f"{name}: proved={proved} elapsed={elapsed:.1f}s "
                f"exit={summary.get('exit_reason')} mock_llm={summary.get('n_mock_llm_calls')}",
                flush=True,
            )
            _assert_updated_pipeline(
                name, proved, summary, int(summary.get("n_mock_llm_calls") or 0)
            )
            results.append((str(dest), proved, elapsed, None))

    csv_path = run_dir / f"results_{stamp}_mock_cases_default.csv"
    write_results_csv(results, str(csv_path), str(CASES))
    (run_dir / "mock_llm_calls.json").write_text(
        json.dumps(fake.calls, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"results: {run_dir}", flush=True)
    print(f"csv: {csv_path}", flush=True)
    return run_dir


def main() -> int:
    test_mock_llm_case_experiments()
    print("mock-LLM case simulation passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
