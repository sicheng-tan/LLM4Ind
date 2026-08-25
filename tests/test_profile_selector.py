#!/usr/bin/env python3
"""Tests for the optional backend-specific LLM profile selector."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from profile_selector import choose_joint_action
from theory_features import analyze_smt


PROMPTS = [
    "prove_prompt_equational_reasoning",
    "prove_prompt_term_rewrite",
]


class FakeLLM:
    def __init__(self, content: str):
        self.content = content
        self.calls = 0

    def invoke(self, messages):
        self.calls += 1
        self.messages = messages
        return SimpleNamespace(content=self.content)


def _ok(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _features():
    return analyze_smt(
        "(set-logic UFDT)\n"
        "(declare-datatypes ((nat 0)) (((zero) (s (s0 nat)))))\n"
    )


def _with_env(value: str):
    old = os.environ.get("SOLVER_ROUTING_DECIDER")
    os.environ["SOLVER_ROUTING_DECIDER"] = value
    return old


def _restore(old):
    if old is None:
        os.environ.pop("SOLVER_ROUTING_DECIDER", None)
    else:
        os.environ["SOLVER_ROUTING_DECIDER"] = old


def test_relative_does_not_call_llm() -> None:
    old = _with_env("relative")
    try:
        fake = FakeLLM('{"profile":"not-used","confidence":1.0}')
        decision = choose_joint_action(
            llm=fake,
            backend="vampire",
            features=_features(),
            candidate_profiles=["struct_induction", "induction_portfolio"],
            prompt_strategies=PROMPTS,
        )
        _ok(fake.calls == 0, f"relative mode called LLM: {fake.calls}")
        _ok(decision.source == "relative", decision)
        _ok(decision.profile == "struct_induction", decision)
    finally:
        _restore(old)


def test_llm_selects_whitelisted_pair() -> None:
    old = _with_env("llm")
    try:
        fake = FakeLLM(
            '{"profile":"induction_portfolio",'
            '"prompt_strategy":"prove_prompt_term_rewrite",'
            '"confidence":0.91,"reason":"generalized rewrite bridge"}'
        )
        decision = choose_joint_action(
            llm=fake,
            backend="vampire",
            features=_features(),
            candidate_profiles=["struct_induction", "induction_portfolio"],
            prompt_strategies=PROMPTS,
        )
        _ok(fake.calls == 1, "LLM selector was not called")
        _ok(decision.source == "llm", decision)
        _ok(decision.profile == "induction_portfolio", decision)
        _ok(decision.prompt_strategy == "prove_prompt_term_rewrite", decision)
        _ok("Vampire" in fake.messages[0]["content"], fake.messages)
        _ok("induction_portfolio" in fake.messages[1]["content"], fake.messages)
        _ok("--schedule induction" in fake.messages[1]["content"], fake.messages)
    finally:
        _restore(old)


def test_invalid_llm_choice_falls_back_to_static() -> None:
    old = _with_env("llm")
    try:
        fake = FakeLLM(
            '{"profile":"invented_profile",'
            '"prompt_strategy":"prove_prompt_term_rewrite",'
            '"confidence":0.99,"reason":"invalid"}'
        )
        decision = choose_joint_action(
            llm=fake,
            backend="cvc5",
            features=_features(),
            candidate_profiles=["adt_structural", "cvc5_inductive"],
            prompt_strategies=PROMPTS,
        )
        _ok(decision.source == "static_fallback", decision)
        _ok(decision.profile == "adt_structural", decision)
        _ok(decision.error is not None, decision)
    finally:
        _restore(old)


def test_low_confidence_falls_back_to_static() -> None:
    old_mode = _with_env("llm")
    old_min = os.environ.get("SOLVER_ROUTING_LLM_MIN_CONFIDENCE")
    os.environ["SOLVER_ROUTING_LLM_MIN_CONFIDENCE"] = "0.55"
    try:
        fake = FakeLLM(
            '{"profile":"adt_structural",'
            '"prompt_strategy":"prove_prompt_equational_reasoning",'
            '"confidence":0.2,"reason":"uncertain"}'
        )
        decision = choose_joint_action(
            llm=fake,
            backend="cvc5",
            features=_features(),
            candidate_profiles=["adt_structural", "cvc5_inductive"],
            prompt_strategies=PROMPTS,
        )
        _ok(decision.source == "static_fallback", decision)
        _ok(decision.error is not None, decision)
    finally:
        _restore(old_mode)
        if old_min is None:
            os.environ.pop("SOLVER_ROUTING_LLM_MIN_CONFIDENCE", None)
        else:
            os.environ["SOLVER_ROUTING_LLM_MIN_CONFIDENCE"] = old_min


def test_backend_selector_prompts_are_distinct() -> None:
    old = _with_env("llm")
    try:
        vampire = FakeLLM(
            '{"profile":"struct_induction","prompt_strategy":'
            '"prove_prompt_equational_reasoning","confidence":0.8}'
        )
        cvc5 = FakeLLM(
            '{"profile":"adt_structural","prompt_strategy":'
            '"prove_prompt_equational_reasoning","confidence":0.8}'
        )
        choose_joint_action(
            llm=vampire,
            backend="vampire",
            features=_features(),
            candidate_profiles=["struct_induction"],
            prompt_strategies=PROMPTS,
        )
        choose_joint_action(
            llm=cvc5,
            backend="cvc5",
            features=_features(),
            candidate_profiles=["adt_structural"],
            prompt_strategies=PROMPTS,
        )
        _ok(vampire.messages[0]["content"] != cvc5.messages[0]["content"], "system prompts must differ")
        _ok("Vampire" in vampire.messages[0]["content"], vampire.messages)
        _ok("CVC5" in cvc5.messages[0]["content"], cvc5.messages)
        _ok("--schedule induction" in vampire.messages[0]["content"], vampire.messages)
        _ok("--theory_instantiation all" in vampire.messages[0]["content"], vampire.messages)
        _ok("--dt-stc-ind" in cvc5.messages[0]["content"], cvc5.messages)
        _ok("--int-wf-ind" in cvc5.messages[0]["content"], cvc5.messages)
    finally:
        _restore(old)


def test_relative_pair_history_changes_pair() -> None:
    old = _with_env("relative")
    try:
        decision = choose_joint_action(
            llm=None,
            backend="vampire",
            features=_features(),
            candidate_profiles=["struct_induction", "induction_portfolio"],
            prompt_strategies=PROMPTS,
            history=[
                {
                    "prompt_strategy": "prove_prompt_equational_reasoning",
                    "profile": "struct_induction",
                    "status": "timeout",
                    "proved": False,
                    "utility": None,
                }
            ],
            current_profile="struct_induction",
            current_prompt="prove_prompt_equational_reasoning",
        )
        _ok(
            (decision.prompt_strategy, decision.profile)
            != (
                "prove_prompt_equational_reasoning",
                "struct_induction",
            ),
            decision,
        )
    finally:
        _restore(old)


def main() -> int:
    tests = [
        test_relative_does_not_call_llm,
        test_llm_selects_whitelisted_pair,
        test_invalid_llm_choice_falls_back_to_static,
        test_low_confidence_falls_back_to_static,
        test_backend_selector_prompts_are_distinct,
        test_relative_pair_history_changes_pair,
    ]
    failed = 0
    for fn in tests:
        try:
            fn()
            print(f"ok  {fn.__name__}")
        except Exception as exc:
            failed += 1
            print(f"FAIL {fn.__name__}: {exc}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
