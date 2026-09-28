"""Deterministic Problem Profiler: parse / gate / render."""

from __future__ import annotations

import os
import tempfile
from pathlib import Path
from unittest.mock import patch

from problem_profiler import (
    build_problem_profile,
    build_problem_profile_incremental,
    clear_profiler_caches,
    format_profile_prompt_block,
    gate_profile_for_prompt,
    profile_prompt_block_for_smt,
    profiler_cache_stats,
)
from exp_flags import problem_profiler_enabled

SAMPLE_SMT = """(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Nat) (tail Lst)))))
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Nat) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (xs Lst)) (= (len (cons x xs)) (succ (len xs)))))
; proof goal
(assert (not (forall ((xs Lst)) (= (len (append xs nil)) (len xs)))))
; proof goal end
(check-sat)
"""

GOAL = "(forall ((xs Lst)) (= (len (append xs nil)) (len xs)))"
BASE_LEMMA = "(= (len (append nil nil)) (len nil))"
STEP_LEMMA = (
    "(forall ((x Nat) (xs Lst)) "
    "(=> (= (len (append xs nil)) (len xs)) "
    "(= (len (append (cons x xs) nil)) (len (cons x xs)))))"
)


def test_problem_profiler_flag_default_off() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("PROBLEM_PROFILER", None)
        assert problem_profiler_enabled() is False
    with patch.dict(os.environ, {"PROBLEM_PROFILER": "on"}):
        assert problem_profiler_enabled() is True


def test_build_profile_marks_goal_and_structural_recursion() -> None:
    profile = build_problem_profile(SAMPLE_SMT, problem_id="len_append")
    assert profile.goal_formula_id and profile.goal_formula_id.startswith("G")
    goal = next(f for f in profile.formulas if f.formula_id == profile.goal_formula_id)
    assert goal.role == "goal"
    assert goal.role_source == "proof_goal_marker"
    assert "append" in goal.symbols
    assert "len" in goal.symbols

    kinds = {r.kind for r in profile.recursion_structure}
    funs = {r.function for r in profile.recursion_structure}
    assert "append" in funs
    assert "len" in funs
    assert "structural_recursion" in kinds
    assert "constructor_case_split" in kinds
    append_struct = next(
        r for r in profile.recursion_structure
        if r.function == "append" and r.kind == "structural_recursion"
    )
    assert "cons" in (append_struct.detail or "")
    assert "nil" in (append_struct.detail or "")
    assert set(profile.signature.get("constructors") or []) >= {"nil", "cons", "zero", "succ"}
    dt_ctors = profile.signature.get("datatype_constructors") or {}
    assert set(dt_ctors.get("Lst") or []) >= {"nil", "cons"}

    obs_names = {o.function for o in profile.observer_candidates}
    assert "len" in obs_names
    len_obs = next(o for o in profile.observer_candidates if o.function == "len")
    assert len_obs.evidence_level in ("structural", "heuristic")


def test_gate_injects_when_goal_mentions_symbols() -> None:
    profile = build_problem_profile(SAMPLE_SMT, problem_id="len_append")
    gated = gate_profile_for_prompt(profile)
    # Goal has append+len; expect recursion and/or observer facts.
    assert not gated.is_empty()
    assert any(r.kind == "structural_recursion" for r in gated.recursion)
    block = format_profile_prompt_block(gated)
    assert "PROBLEM STRUCTURE" in block
    assert "structural_recursion" in block
    assert "Identifiers enclosed in backticks" in block
    assert "e.g., `len`" in block
    assert "Related formulas" not in block
    assert "formulas=" not in block
    assert "(= (append" not in block
    # append & len appear in goal but not together in defining axioms → missing_bridge
    assert any(lk.kind == "missing_bridge" for lk in gated.function_links)
    assert "missing_bridge: `append`–`len`" in block or "missing_bridge: `len`–`append`" in block
    assert "`append`" in block
    assert "`len`" in block
    assert ", case_split" in block
    assert "constructor_case_split" not in block  # merged into structural line
    assert "link=theorem-related" not in block
    assert "link=def-only" not in block
    assert "LHS constructor pattern" not in block
    assert "Recursion (constructor cases" in block
    assert "You may consider whether these definitions" not in block


def test_function_link_theorem_related_via_defining_eq() -> None:
    """rev's defining equation mentions append → theorem-related."""
    smt = """(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-fun append (Lst Lst) Lst)
(declare-fun rev (Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst))
  (= (append (cons x y) z) (cons x (append y z)))))
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst))
  (= (rev (cons x y)) (append (rev y) (cons x nil)))))
; proof goal
(assert (not (forall ((x Lst)) (= (rev (rev x)) x))))
; proof goal end
(check-sat)
"""
    profile = build_problem_profile(smt, problem_id="rev")
    gated = gate_profile_for_prompt(profile)
    rev_facts = [r for r in gated.recursion if r.function == "rev"]
    assert rev_facts
    assert any(r.link == "theorem-related" for r in rev_facts)
    assert any("append" in r.link_peers for r in rev_facts if r.link_peers)
    block = format_profile_prompt_block(gated)
    assert "link_with=`append`" in block
    assert "link=theorem-related" not in block
    # Goal only mentions rev — no Function-links pair section required.
    assert "missing_bridge" not in block


def test_gate_empty_when_goal_unrelated() -> None:
    profile = build_problem_profile(SAMPLE_SMT, problem_id="len_append")
    gated = gate_profile_for_prompt(
        profile,
        current_goal="(forall ((n Nat)) (= n n))",
    )
    assert gated.is_empty()
    assert format_profile_prompt_block(gated) == ""


def test_profile_prompt_block_helper() -> None:
    block = profile_prompt_block_for_smt(SAMPLE_SMT, problem_id="x")
    assert "PROBLEM STRUCTURE" in block


def test_incremental_cache_and_library_induction() -> None:
    clear_profiler_caches()
    p1 = build_problem_profile_incremental(
        SAMPLE_SMT, problem_id="t", current_goal=GOAL, cache_ns="taskA",
    )
    assert not p1.induction_attempts
    stats1 = profiler_cache_stats()
    assert stats1["bg_miss"] >= 1

    p2 = build_problem_profile_incremental(
        SAMPLE_SMT, problem_id="t", current_goal=GOAL, cache_ns="taskA",
    )
    stats2 = profiler_cache_stats()
    assert stats2["bg_hit"] >= 1

    lib = [
        {"id": "lib_1", "formula": BASE_LEMMA},
        {"id": "lib_2", "formula": STEP_LEMMA},
    ]
    p3 = build_problem_profile_incremental(
        SAMPLE_SMT,
        problem_id="t",
        current_goal=GOAL,
        library_items=lib,
        cache_ns="taskA",
    )
    assert p3.induction_attempts
    att = p3.induction_attempts[0]
    assert att.induct_var == "xs"
    assert "nil" in att.base_ctors
    assert "cons" in att.step_ctors
    assert att.case_split is True

    gated = gate_profile_for_prompt(p3, current_goal=GOAL)
    block = format_profile_prompt_block(gated)
    assert "Known induction attempts" in block
    assert "base@`nil`" in block
    assert "step@`cons`" in block
    assert "Legend:" in block
    assert "base@`C`" in block
    assert "background for the CURRENT goal" in block
    assert "outer→inner" not in block
    assert "not proved coverage" not in block

    # Growing the library should be incremental (prefix reuse).
    before_incr = profiler_cache_stats()["lib_incr"]
    lib2 = lib + [{"id": "lib_3", "formula": "(forall ((xs Lst)) (= xs xs))"}]
    build_problem_profile_incremental(
        SAMPLE_SMT,
        problem_id="t",
        current_goal=GOAL,
        library_items=lib2,
        cache_ns="taskA",
    )
    assert profiler_cache_stats()["lib_incr"] == before_incr + 1


def test_nested_induction_progressive_list() -> None:
    """Two ADT binders: outer known + inner candidate → indented nest."""
    clear_profiler_caches()
    smt = """(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Nat) (tail Lst)))))
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Nat) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (xs Lst)) (= (len (cons x xs)) (succ (len xs)))))
; proof goal
(assert (not (forall ((xs Lst) (ys Lst))
  (= (len (append xs ys)) (len (append ys xs))))))
; proof goal end
(check-sat)
"""
    goal = (
        "(forall ((xs Lst) (ys Lst)) "
        "(= (len (append xs ys)) (len (append ys xs))))"
    )
    # Base for outer xs only (instantiate xs:=nil, keep ys).
    base_xs = (
        "(forall ((ys Lst)) (= (len (append nil ys)) (len (append ys nil))))"
    )
    p = build_problem_profile_incremental(
        smt,
        problem_id="nest",
        current_goal=goal,
        library_items=[{"id": "lib_1", "formula": base_xs}],
        cache_ns="nestTask",
    )
    assert len(p.induction_attempts) == 2
    outer, inner = p.induction_attempts
    assert outer.induct_var == "xs" and outer.nest_level == 0
    assert outer.status == "known" and "nil" in outer.base_ctors
    assert inner.induct_var == "ys" and inner.nest_level == 1
    assert inner.status == "candidate" and inner.detail == "attempt=none"

    gated = gate_profile_for_prompt(p, current_goal=goal)
    block = format_profile_prompt_block(gated)
    assert "- var=`xs`:`Lst`; base@`nil`" in block
    assert "- nested var=`ys`:`Lst`; attempt=none" in block
    # Progressive indent: nested line has deeper leading spaces.
    lines = [ln for ln in block.splitlines() if "var=`xs`" in ln or "var=`ys`" in ln]
    assert len(lines) == 2
    assert lines[1].index("- nested") > lines[0].index("- var")


def test_create_prompt_injects_when_flag_on() -> None:
    import Mate_new as mate
    from obligation_tree import save_lemma_library

    with tempfile.TemporaryDirectory() as tmp:
        prompts = Path(__file__).resolve().parents[1] / "prompts_ours" / "prove_prompt_equational_reasoning"
        if not prompts.exists():
            return
        save_lemma_library(
            tmp,
            [
                {"id": "lib_1", "formula": BASE_LEMMA},
                {"id": "lib_2", "formula": STEP_LEMMA},
            ],
        )
        with patch.dict(os.environ, {
            "PROBLEM_PROFILER": "on",
            "ANCESTOR_PROMPT": "off",
            "LEMMA_LIBRARY": "on",
        }):
            messages, failed = mate.create_prompt(
                SAMPLE_SMT,
                "prove_prompt_equational_reasoning",
                tmp,
                "template",
                str(prompts.parent),
                depth=0,
                current_formula=GOAL,
            )
        assert "PROBLEM STRUCTURE" in failed
        assert "Known induction attempts" in failed
        assert "base@`nil`" in failed
        assert "PROBLEM STRUCTURE" in messages[1]["content"]
    with patch.dict(os.environ, {"PROBLEM_PROFILER": "off", "ANCESTOR_PROMPT": "off"}):
        with tempfile.TemporaryDirectory() as tmp:
            messages, failed = mate.create_prompt(
                SAMPLE_SMT,
                "prove_prompt_equational_reasoning",
                tmp,
                "template",
                str(prompts.parent),
                depth=0,
            )
        assert "PROBLEM STRUCTURE" not in failed
