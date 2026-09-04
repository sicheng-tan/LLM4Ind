#!/usr/bin/env python3
"""Per-task experiment summaries and CSV columns."""

from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from exp_stats import (
    CSV_COLUMNS,
    csv_row,
    flags_compact,
    summarize_artifacts,
    write_results_csv,
    write_task_summary,
)


def _write(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_summarize_artifacts_counts_attempts_and_library(tmp_path: Path) -> None:
    _write(
        tmp_path / "failed_lemmas.json",
        {
            "exp_attempts": [
                {"kind": "empty"},
                {"kind": "useless"},
                {"kind": "obligation_tree", "has_tree": True},
            ],
            "repair_hints": [
                {"kind": "need_rewrite"},
                {"kind": "induction_stuck"},
            ],
            "progress_lemmas": [{"lemma": "(L1)", "score": 1.0}],
            "invalid_lemmas": [],
            "useless_lemma_groups": [{"lemmas": ["(L2)"]}],
            "unproved_lemmas": [{"lemma": "(L3)"}],
            "routing": {
                "active_profile": "adt_structural",
                "decision_mode": "relative",
                "theory_features": {"has_adt": True, "has_int": False, "mixed_adt_lia": False},
                "pair_history": [
                    {
                        "prompt_strategy": "prove_prompt_equational_reasoning",
                        "proved": True,
                        "winner_profile": "cvc5_inductive",
                        "fallback_used": True,
                    }
                ],
            },
            "obligation": {
                "attempts": [
                    {
                        "kind": "obligation_tree",
                        "tree": {
                            "children": [
                                {"status": "proved"},
                                {"status": "failed"},
                                {"status": "cancelled"},
                            ]
                        },
                    }
                ]
            },
        },
    )
    _write(
        tmp_path / "failed_lemmas_1_2.json",
        {"repair_hints": [{"kind": "need_arithmetic_lemma"}]},
    )
    _write(
        tmp_path / "lemma_library.json",
        {"lemmas": [{"id": "lib_1", "formula": "(forall ((x Nat)) true)"}]},
    )
    summary = summarize_artifacts(str(tmp_path))
    assert summary["n_llm_attempts"] == 3
    assert summary["n_empty"] == 1
    assert summary["n_useless"] == 1
    assert summary["n_obligation_trees"] == 1
    assert summary["n_library_lemmas"] == 1
    assert summary["n_progress_lemmas"] == 1
    assert summary["n_unproved"] == 1
    assert summary["theory"] == "adt"
    assert summary["max_goal_depth"] == 2
    assert "need_rewrite" in summary["hint_kinds"]
    assert "need_arithmetic_lemma" in summary["hint_kinds"]
    assert summary["winner_profile"] == "cvc5_inductive"
    assert summary["active_profile"] == "adt_structural"
    assert summary["n_cancelled"] == 1
    assert summary["n_subgoals_proved"] == 1
    assert summary["n_subgoals_failed"] == 1
    assert summary["n_fallback"] == 1
    assert summary["n_goals_touched"] == 2
    assert summary["n_invalid"] == 0
    assert summary["n_invalid_lemmas"] == 0


def test_write_task_summary_and_csv(tmp_path: Path) -> None:
    task = tmp_path / "bench" / "goal1"
    task.mkdir(parents=True)
    _write(
        task / "failed_lemmas.json",
        {
            "exp_attempts": [{"kind": "obligation_tree"}],
            "routing": {
                "active_profile": "cvc5_inductive",
                "theory_features": {"has_int": True, "has_adt": False},
                "pair_history": [],
            },
        },
    )
    summary = write_task_summary(
        str(task), proved=True, exit_reason="llm_subgoals"
    )
    assert summary["solved_by"] == "llm"
    assert (task / "exp_summary.json").exists()

    csv_path = tmp_path / "results.csv"
    jsonl_path = write_results_csv(
        [(str(task), True, 12.5, None)],
        str(csv_path),
        str(tmp_path / "bench"),
    )
    text = csv_path.read_text(encoding="utf-8")
    header = text.splitlines()[0]
    assert header.split(",") == CSV_COLUMNS
    row = csv_row(str(task), True, 12.5, str(tmp_path / "bench"))
    assert row[0].endswith("goal1")
    assert row[1] == "unsat"
    assert row[CSV_COLUMNS.index("solved_by")] == "llm"
    assert row[CSV_COLUMNS.index("exit_reason")] == "llm_subgoals"
    assert Path(jsonl_path).exists()
    payload = json.loads(Path(jsonl_path).read_text(encoding="utf-8").splitlines()[0])
    assert payload["proved"] is True
    assert payload["solved_by"] == "llm"


def test_flags_compact_includes_ablation_keys() -> None:
    compact = flags_compact()
    assert "SOLVER_ROUTING=" in compact
    assert "LEMMA_LIBRARY=" in compact
    assert "PROMPT_RETARGET=" in compact
    assert "MODEL_TYPE=" in compact
    assert "OPENAI_MODEL=" in compact
    assert "ENABLE_THINKING=" in compact
    assert "MAX_TOKENS=" in compact


def test_timeout_summary_from_artifacts(tmp_path: Path) -> None:
    _write(
        tmp_path / "failed_lemmas.json",
        {"exp_attempts": [{"kind": "useless"}], "routing": {}},
    )
    summary = write_task_summary(
        str(tmp_path), proved=False, exit_reason="timeout", error="任务超时 (1200秒)"
    )
    assert summary["solved_by"] == "timeout"
    assert summary["n_useless"] == 1


def test_prompt_blocks_and_timing_counters(tmp_path: Path) -> None:
    from exp_stats import (
        add_llm_time,
        add_solver_time,
        log_library_inject,
        log_prompt_blocks,
        load_counters,
        summarize_artifacts,
    )

    folder = str(tmp_path)
    feedback = (
        "INVALID: The following lemmas are INVALID or CANNOT be verified.\n"
        "The following lemma GROUPS (combinations) did not prove\n"
        "SOLVER PROGRESS SIGNALS (cvc5 stats/difficulty)\n"
        "USEFUL BUT UNPROVED: these lemmas helped\n"
        "SOLVER ROUTING (feedback-guided theory portfolio):\n"
        "SOLVER-GUIDED REPAIR (from cvc5 failure analysis).\n"
        "Library (already proved, in axioms):\n"
        "Last obligation tree (attempt 2; for reference only):\n"
    )
    inv = log_prompt_blocks(folder, "template", "prove_prompt_term_rewrite", feedback)
    assert inv["has_tree"] is True
    assert inv["has_lib"] is True
    assert inv["has_hints"] is True
    assert inv["has_progress"] is True
    add_llm_time(folder, 1.5)
    add_solver_time(folder, 12.0, fallback=True)
    log_library_inject(folder, "template", 2, "initial_prove")
    counters = load_counters(folder)
    assert counters["n_llm"] == 1
    assert counters["n_solver"] == 1
    assert counters["n_fallback"] == 1
    assert counters["n_prompt_with_tree"] == 1
    assert counters["n_library_injects"] == 1
    summary = summarize_artifacts(folder)
    assert summary["llm_s"] == 1.5
    assert summary["solver_s"] == 12.0
    assert summary["n_prompt_with_hints"] == 1


def test_record_llm_generation_writes_plain_prompt_dump(tmp_path: Path) -> None:
    from exp_stats import LLM_PROMPTS_FILENAME, record_llm_generation

    folder = str(tmp_path)
    system = "* Task Environment\nYou are an expert."
    user = "Input: SMTFile:\n(set-logic ALL)\nSOLVER-GUIDED REPAIR\nneed_rewrite"
    record = record_llm_generation(
        folder,
        goal="template",
        strategy="prove_prompt_equational_reasoning",
        prompt_folder="./prompts_ours",
        smt_file=str(tmp_path / "template.smt2"),
        system_text=system,
        user_text=user,
        lemmas=[
            "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))",
            "(forall ((n Nat)) (= (plus n zero) n))",
        ],
        elapsed=1.25,
        raw="; Output begin\n(forall ((n Nat)) (= (plus n zero) n))\n; Output end",
    )
    assert record["n"] == 2
    assert record["call"] == 1
    text = (tmp_path / LLM_PROMPTS_FILENAME).read_text(encoding="utf-8")
    assert "===== LLM CALL 1 =====" in text
    assert "* Task Environment" in text
    assert "(set-logic ALL)" in text
    assert "need_rewrite" in text
    assert "(forall ((n Nat)) (= (plus n zero) n))" in text
    assert "----- RAW RESPONSE -----" in text
    assert "; Output begin" in text

    record_llm_generation(
        folder,
        goal="template_1",
        strategy="prove_prompt_term_rewrite",
        system_text="sys2",
        user_text="user2 full prompt",
        lemmas=[],
        elapsed=0.4,
        parse_error="响应格式错误，缺少输出标记",
        raw="; INVALID_GOAL: plus is only declared, no defining axioms",
    )
    text = (tmp_path / LLM_PROMPTS_FILENAME).read_text(encoding="utf-8")
    assert "===== LLM CALL 2 =====" in text
    assert "user2 full prompt" in text
    assert "parse_error: 响应格式错误，缺少输出标记" in text
    assert "; INVALID_GOAL: plus is only declared, no defining axioms" in text


def test_summarize_direct_proved_child_without_failed_file(tmp_path: Path) -> None:
    """A child that proves on first check writes no failed_lemmas_1.json."""
    _write(
        tmp_path / "failed_lemmas.json",
        {
            "exp_attempts": [{"kind": "obligation_tree", "has_tree": True}],
            "invalid_lemmas": [],
            "obligation": {
                "attempts": [
                    {
                        "kind": "obligation_tree",
                        "tree": {
                            "id": "template",
                            "status": "open",
                            "children": [
                                {
                                    "id": "template_1",
                                    "status": "proved",
                                    "lib": "lib_1",
                                }
                            ],
                        },
                    }
                ]
            },
        },
    )
    _write(
        tmp_path / "lemma_library.json",
        {
            "lemmas": [
                {
                    "id": "lib_1",
                    "formula": "(forall ((x Lst)) (= (len (rev x)) (len x)))",
                    "origin": "template_1",
                    "depth": 1,
                }
            ]
        },
    )
    (tmp_path / "template_1.smt2").write_text("(set-logic ALL)\n", encoding="utf-8")
    assert not (tmp_path / "failed_lemmas_1.json").exists()
    summary = summarize_artifacts(str(tmp_path))
    assert summary["max_goal_depth"] == 1
    assert summary["n_goals_touched"] == 2
    assert summary["n_subgoals_proved"] == 1
    assert summary["n_subgoals_failed"] == 0
    assert summary["n_invalid"] == 0
    assert summary["n_library_lemmas"] == 1


def test_summarize_invalid_on_child_node(tmp_path: Path) -> None:
    """Invalid diagnosed on a child is copied to parent lemmas, not a root attempt kind."""
    plus = (
        "(forall ((a Lst) (b Lst)) (= (len (append a b)) (plus (len a) (len b))))"
    )
    _write(
        tmp_path / "failed_lemmas.json",
        {
            "exp_attempts": [
                {"kind": "useless"},
                {"kind": "obligation_tree", "has_tree": True},
            ],
            "invalid_lemmas": [{"lemma": plus, "reason": "plus has no axioms"}],
            "useless_lemma_groups": [{"lemmas": [plus]}],
            "obligation": {
                "attempts": [
                    {
                        "kind": "obligation_tree",
                        "tree": {
                            "id": "template",
                            "children": [
                                {
                                    "id": "template_1",
                                    "status": "invalid",
                                    "reason": "plus has no axioms",
                                },
                                {"id": "template_2", "status": "proved"},
                            ],
                        },
                    }
                ]
            },
        },
    )
    _write(
        tmp_path / "failed_lemmas_1.json",
        {
            "exp_attempts": [],
            "node_outcome": {
                "kind": "invalid",
                "reason": "plus has no axioms",
                "source": "llm",
            },
            "invalid_lemmas": [],
        },
    )
    summary = write_task_summary(
        str(tmp_path), proved=True, exit_reason="llm_subgoals"
    )
    assert summary["n_invalid"] == 1
    assert summary["n_invalid_lemmas"] == 1
    assert summary["n_useless"] == 1
    assert summary["max_goal_depth"] == 1
    assert summary["n_goals_touched"] == 3
    assert summary["n_subgoals_proved"] == 1
    dumped = (tmp_path / "exp_summary.json").read_text(encoding="utf-8")
    assert '"n_invalid": 1' in dumped
    assert '"n_invalid_lemmas": 1' in dumped


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        test_summarize_artifacts_counts_attempts_and_library(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_write_task_summary_and_csv(Path(tmp))
    test_flags_compact_includes_ablation_keys()
    with tempfile.TemporaryDirectory() as tmp:
        test_timeout_summary_from_artifacts(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_prompt_blocks_and_timing_counters(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_record_llm_generation_writes_plain_prompt_dump(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_summarize_direct_proved_child_without_failed_file(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        test_summarize_invalid_on_child_node(Path(tmp))
    print("exp_stats tests passed")
