"""Deterministic Problem Profiler: parse / gate / render / inject triggers."""

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
from exp_flags import (
    problem_profiler_enabled,
    problem_profiler_min_attempt,
    problem_profiler_trigger,
    should_inject_problem_profiler,
)

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


def test_profiler_trigger_defaults_and_after_useless() -> None:
    with patch.dict(os.environ, {
        "PROBLEM_PROFILER": "on",
        "PROBLEM_PROFILER_MIN_ATTEMPT": "1",
        "PROBLEM_PROFILER_TRIGGER": "always",
    }):
        assert problem_profiler_min_attempt() == 1
        assert problem_profiler_trigger() == "always"
        assert should_inject_problem_profiler({}) is True
        assert should_inject_problem_profiler({"exp_attempts": []}) is True

    with patch.dict(os.environ, {
        "PROBLEM_PROFILER": "on",
        "PROBLEM_PROFILER_MIN_ATTEMPT": "2",
        "PROBLEM_PROFILER_TRIGGER": "after_useless",
    }):
        assert should_inject_problem_profiler({}) is False
        assert should_inject_problem_profiler({"exp_attempts": []}) is False
        assert should_inject_problem_profiler({
            "exp_attempts": [{"kind": "obligation_tree"}],
        }) is False
        assert should_inject_problem_profiler({
            "exp_attempts": [{"kind": "useless"}],
        }) is True
        # attempt index 3 with last useless → min_attempt=2 still ok
        assert should_inject_problem_profiler({
            "exp_attempts": [
                {"kind": "useless"},
                {"kind": "useless"},
            ],
        }) is True


def test_build_profile_marks_goal_and_structural_recursion() -> None:
    profile = build_problem_profile(SAMPLE_SMT, problem_id="len_append")
    assert profile.goal_formula_id and profile.goal_formula_id.startswith("G")
    goal = next(f for f in profile.formulas if f.formula_id == profile.goal_formula_id)
    assert goal.role == "goal"
    assert "append" in goal.symbols
    assert "len" in goal.symbols

    kinds = {r.kind for r in profile.recursion_structure}
    funs = {r.function for r in profile.recursion_structure}
    assert "append" in funs and "len" in funs
    assert "structural_recursion" in kinds
    assert "constructor_case_split" in kinds
    assert set(profile.signature.get("constructors") or []) >= {"nil", "cons", "zero", "succ"}


def test_gate_injects_when_goal_mentions_symbols() -> None:
    profile = build_problem_profile(SAMPLE_SMT, problem_id="len_append")
    gated = gate_profile_for_prompt(profile)
    assert not gated.is_empty()
    assert any(r.kind == "structural_recursion" for r in gated.recursion)
    assert not gated.relations
    assert not gated.function_links
    block = format_profile_prompt_block(gated)
    assert "PROBLEM STRUCTURE" in block
    assert "structural_recursion" in block
    assert "Identifiers enclosed in backticks" in block
    assert "Function links" not in block
    assert "Goal relations" not in block
    assert "missing_bridge" not in block
    assert "constructors=" not in block
    assert "link_with=" not in block
    assert ", case_split" in block
    assert "constructor_case_split" not in block
    # Without library base/step hits, induction section stays silent.
    assert "attempt=none" not in block
    assert "Known induction attempts" not in block


def test_rev_recursion_without_link_notes() -> None:
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
    block = format_profile_prompt_block(gated)
    assert "`rev`" in block
    assert "link_with=" not in block
    assert "Function links" not in block
    assert "attempt=none" not in block


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
    # No library → no known induction rows (attempt=none suppressed).
    assert p1.induction_attempts == []
    assert profiler_cache_stats()["bg_miss"] >= 1

    p2 = build_problem_profile_incremental(
        SAMPLE_SMT, problem_id="t", current_goal=GOAL, cache_ns="taskA",
    )
    assert profiler_cache_stats()["bg_hit"] >= 1

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
    att = p3.induction_attempts[0]
    assert att.induct_var == "xs"
    assert "nil" in att.base_ctors
    assert "cons" in att.step_ctors

    gated = gate_profile_for_prompt(p3, current_goal=GOAL)
    block = format_profile_prompt_block(gated)
    assert "Known induction attempts" not in block
    assert "base@`nil`" not in block
    assert "attempt=none" not in block
    # Recursion / observers may still appear; analysis keeps known hits on profile.
    assert p3.induction_attempts and "nil" in p3.induction_attempts[0].base_ctors

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
    """Outer known base is detected on profile; not injected into the prompt."""
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
    assert len(p.induction_attempts) == 1
    outer = p.induction_attempts[0]
    assert outer.status == "known" and "nil" in outer.base_ctors
    assert outer.induct_var == "xs"

    gated = gate_profile_for_prompt(p, current_goal=goal)
    assert gated.induction_attempts == []
    block = format_profile_prompt_block(gated)
    assert "Known induction attempts" not in block
    assert "base@`nil`" not in block
    assert "attempt=none" not in block


def test_create_prompt_respects_after_useless_trigger() -> None:
    import Mate_new as mate
    from obligation_tree import save_lemma_library

    prompts = Path(__file__).resolve().parents[1] / "prompts_ours" / "prove_prompt_equational_reasoning"
    if not prompts.exists():
        return

    with tempfile.TemporaryDirectory() as tmp:
        save_lemma_library(tmp, [{"id": "lib_1", "formula": BASE_LEMMA}])
        mate.save_failed_lemmas(tmp, "template", {
            "invalid_lemmas": [],
            "soft_rejected_lemmas": [],
            "illformed_lemmas": [],
            "useless_lemma_groups": [],
            "progress_lemmas": [],
            "unproved_lemmas": [],
            "revival_lemmas": [],
            "exp_attempts": [],
        })
        env = {
            "PROBLEM_PROFILER": "on",
            "PROBLEM_PROFILER_MIN_ATTEMPT": "2",
            "PROBLEM_PROFILER_TRIGGER": "after_useless",
            "ANCESTOR_PROMPT": "off",
            "LEMMA_LIBRARY": "on",
        }
        with patch.dict(os.environ, env):
            _messages, failed0 = mate.create_prompt(
                SAMPLE_SMT,
                "prove_prompt_equational_reasoning",
                tmp,
                "template",
                str(prompts.parent),
                depth=0,
                current_formula=GOAL,
            )
        assert "PROBLEM STRUCTURE" not in failed0

        mate.save_failed_lemmas(tmp, "template", {
            "invalid_lemmas": [],
            "soft_rejected_lemmas": [],
            "illformed_lemmas": [],
            "useless_lemma_groups": [],
            "progress_lemmas": [],
            "unproved_lemmas": [],
            "revival_lemmas": [],
            "exp_attempts": [{"kind": "useless"}],
        })
        with patch.dict(os.environ, env):
            _messages, failed1 = mate.create_prompt(
                SAMPLE_SMT,
                "prove_prompt_equational_reasoning",
                tmp,
                "template",
                str(prompts.parent),
                depth=0,
                current_formula=GOAL,
            )
        assert "PROBLEM STRUCTURE" in failed1
        assert "structural_recursion" in failed1 or "recursive_call" in failed1 or "Observer" in failed1


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
            "PROBLEM_PROFILER_MIN_ATTEMPT": "1",
            "PROBLEM_PROFILER_TRIGGER": "always",
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
        assert "Known induction attempts" not in failed
        assert "base@`nil`" not in failed
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


# ---------------------------------------------------------------------------
# Recognition coverage: selector/tester, Int decrease, atomic predicates,
# define-fun-rec, attempt-lemma induction matching.
# ---------------------------------------------------------------------------

SELECTOR_SMT = """(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun alt_mul (Nat Nat) Nat)
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (alt_mul x y)
      (ite (is-S x)
        (ite (is-S y) (S (plus (plus (alt_mul (p x) (p y)) (p x)) (p y))) Z)
        Z))))
; proof goal
(assert (not (forall ((x Nat) (y Nat)) (= (alt_mul x y) (mult x y)))))
; proof goal end
(check-sat)
"""

INT_EVEN_SMT = """(set-logic UFDTLIA)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(declare-fun even (Int) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Int)
(assert (= (even 0) true))
(assert (forall ((n Int)) (=> (>= n 0) (= (even (+ 1 n)) (not (even n))))))
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst))
  (= (append (cons x y) z) (cons x (append y z)))))
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))
; proof goal
(assert (not (forall ((x Lst) (y Lst))
  (= (even (len (append x y))) (even (len (append y x)))))))
; proof goal end
(check-sat)
"""

PREF_SMT = """(set-logic UFDT)
(declare-datatypes ((nat 0) (lst 0))
  (((zero) (s (s0 nat))) ((nil) (cons (cons0 nat) (cons1 lst)))))
(declare-fun pref (lst lst) Bool)
(assert (forall ((x lst)) (pref nil x)))
(assert (forall ((a nat) (x lst)) (not (pref (cons a x) nil))))
(assert (forall ((a nat) (b nat) (x lst) (y lst))
  (= (pref (cons a x) (cons b y)) (and (= a b) (pref x y)))))
; proof goal
(assert (not (forall ((x lst) (y lst)) (=> (pref x y) (pref x (cons zero y))))))
; proof goal end
(check-sat)
"""

DEFINE_FUN_REC_SMT = """(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(define-fun-rec len ((xs Lst)) Int
  (ite ((_ is nil) xs) 0 (+ 1 (len (tail xs)))))
; proof goal
(assert (not (forall ((xs Lst)) (>= (len xs) 0))))
; proof goal end
(check-sat)
"""


def test_selector_tester_style_is_structural() -> None:
    profile = build_problem_profile(SELECTOR_SMT, problem_id="alt_mul")
    assert "p" in (profile.signature.get("selectors") or [])
    kinds = {
        (r.function, r.kind)
        for r in profile.recursion_structure
    }
    assert ("alt_mul", "structural_recursion") in kinds
    assert ("mult", "structural_recursion") in kinds
    assert ("plus", "structural_recursion") in kinds
    assert ("alt_mul", "constructor_case_split") in kinds
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`alt_mul`" in block
    assert "`mult`" in block
    assert "structural_recursion" in block
    assert "missing_bridge" not in block


def test_int_succ_recursion_recognized() -> None:
    profile = build_problem_profile(INT_EVEN_SMT, problem_id="even")
    even = [r for r in profile.recursion_structure if r.function == "even"]
    assert even
    assert even[0].kind == "other_decreasing_recursion"
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`even`" in block
    assert "other_decreasing_recursion" in block


def test_atomic_predicate_ctors_for_case_split() -> None:
    profile = build_problem_profile(PREF_SMT, problem_id="pref")
    pref = [r for r in profile.recursion_structure if r.function == "pref"]
    assert pref
    struct = next(r for r in pref if r.kind == "structural_recursion")
    assert "nil" in struct.detail and "cons" in struct.detail
    assert any(r.kind == "constructor_case_split" for r in pref)


def test_define_fun_rec_parsed_as_structural() -> None:
    profile = build_problem_profile(DEFINE_FUN_REC_SMT, problem_id="lenrec")
    assert any(f.role_source == "define-fun-rec" for f in profile.formulas)
    assert "tail" in (profile.signature.get("selectors") or [])
    len_facts = [r for r in profile.recursion_structure if r.function == "len"]
    assert len_facts
    assert any(r.kind == "structural_recursion" for r in len_facts)
    gated = gate_profile_for_prompt(profile)
    assert "`len`" in format_profile_prompt_block(gated)


def test_attempt_lemmas_feed_induction_matching() -> None:
    from problem_profiler import (
        attempt_lemmas_from_failed_data,
        build_problem_profile_incremental,
        clear_profiler_caches,
    )

    clear_profiler_caches()
    # Base@nil for GOAL already used in library tests; here use attempt_feedback.
    failed = {
        "useless_lemma_groups": [{"lemmas": [BASE_LEMMA]}],
        "unproved_lemmas": [{"lemma": STEP_LEMMA}],
    }
    extras = attempt_lemmas_from_failed_data(failed)
    assert BASE_LEMMA.replace(" ", "") in "".join(extras).replace(" ", "") or extras

    p = build_problem_profile_incremental(
        SAMPLE_SMT,
        problem_id="att",
        current_goal=GOAL,
        attempt_lemmas=extras,
        cache_ns="att_ns",
    )
    att = p.induction_attempts[0]
    assert att.status == "known"
    assert "nil" in att.base_ctors
    assert "cons" in att.step_ctors


def test_int_induction_candidate_when_goal_binds_int() -> None:
    """Int Peano context is recognized, but attempt=none rows are not emitted."""
    smt = """(set-logic UFLIA)
(declare-fun even (Int) Bool)
(assert (= (even 0) true))
(assert (forall ((n Int)) (=> (>= n 0) (= (even (+ 1 n)) (not (even n))))))
; proof goal
(assert (not (forall ((n Int)) (=> (>= n 0) (= (even (+ 1 (+ 1 n))) (even n))))))
; proof goal end
(check-sat)
"""
    profile = build_problem_profile(smt, problem_id="intind")
    assert profile.induction_attempts == []
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`even`" in block
    assert "attempt=none" not in block
    assert "Known induction attempts" not in block


# ---------------------------------------------------------------------------
# Recognition coverage: selector/tester, Int (+ 1 n), atomic predicates,
# define-fun-rec, attempt-lemma induction matching.
# ---------------------------------------------------------------------------

SELECTOR_SMT = """(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun alt_mul (Nat Nat) Nat)
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (alt_mul x y)
      (ite (is-S x)
        (ite (is-S y) (S (plus (plus (alt_mul (p x) (p y)) (p x)) (p y))) Z)
        Z))))
; proof goal
(assert (not (forall ((x Nat) (y Nat)) (= (alt_mul x y) (mult x y)))))
; proof goal end
(check-sat)
"""

INT_EVEN_SMT = """(set-logic UFDTLIA)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(declare-fun even (Int) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Int)
(assert (= (even 0) true))
(assert (forall ((n Int)) (=> (>= n 0) (= (even (+ 1 n)) (not (even n))))))
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst))
  (= (append (cons x y) z) (cons x (append y z)))))
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))
; proof goal
(assert (not (forall ((x Lst) (y Lst))
  (= (even (len (append x y))) (even (len (append y x)))))))
; proof goal end
(check-sat)
"""

PREF_SMT = """(set-logic UFDT)
(declare-datatypes ((nat 0) (lst 0))
  (((zero) (s (s0 nat))) ((nil) (cons (cons0 nat) (cons1 lst)))))
(declare-fun pref (lst lst) Bool)
(assert (forall ((x lst)) (pref nil x)))
(assert (forall ((a nat) (x lst)) (not (pref (cons a x) nil))))
(assert (forall ((a nat) (b nat) (x lst) (y lst))
  (= (pref (cons a x) (cons b y)) (and (= a b) (pref x y)))))
; proof goal
(assert (not (forall ((x lst) (y lst)) (=> (pref x y) (pref x (cons zero y))))))
; proof goal end
(check-sat)
"""

DEFINE_FUN_REC_SMT = """(set-logic ALL)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(define-fun-rec add ((x Nat) (y Nat)) Nat
  (ite ((_ is succ) x) (succ (add (pred x) y)) y))
; proof goal
(assert (not (forall ((x Nat)) (= (add x zero) x))))
; proof goal end
(check-sat)
"""


def test_selector_tester_recognized_as_structural() -> None:
    profile = build_problem_profile(SELECTOR_SMT, problem_id="alt_mul")
    assert "p" in (profile.signature.get("selectors") or [])
    kinds = {
        (r.function, r.kind): r
        for r in profile.recursion_structure
    }
    assert ("alt_mul", "structural_recursion") in kinds
    assert ("mult", "structural_recursion") in kinds
    assert ("plus", "structural_recursion") in kinds
    assert ("alt_mul", "constructor_case_split") in kinds
    detail = kinds[("alt_mul", "structural_recursion")].detail
    assert "S" in detail and "Z" in detail
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`alt_mul`" in block
    assert "`mult`" in block
    assert "structural_recursion" in block
    assert "Function links" not in block


def test_int_plus_one_recognized_as_decreasing() -> None:
    profile = build_problem_profile(INT_EVEN_SMT, problem_id="even")
    even_facts = [r for r in profile.recursion_structure if r.function == "even"]
    assert even_facts
    assert even_facts[0].kind == "other_decreasing_recursion"
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`even`" in block
    assert "other_decreasing_recursion" in block


def test_atomic_predicate_ctors_include_nil() -> None:
    profile = build_problem_profile(PREF_SMT, problem_id="pref")
    pref = [
        r for r in profile.recursion_structure
        if r.function == "pref" and r.kind == "structural_recursion"
    ]
    assert pref
    assert "nil" in pref[0].detail and "cons" in pref[0].detail
    splits = [
        r for r in profile.recursion_structure
        if r.function == "pref" and r.kind == "constructor_case_split"
    ]
    assert splits


def test_define_fun_rec_parsed_as_structural() -> None:
    profile = build_problem_profile(DEFINE_FUN_REC_SMT, problem_id="add")
    assert any(
        f.role_source == "define-fun-rec" for f in profile.formulas
    )
    add_facts = [r for r in profile.recursion_structure if r.function == "add"]
    assert add_facts
    assert add_facts[0].kind == "structural_recursion"
    gated = gate_profile_for_prompt(profile)
    assert "`add`" in format_profile_prompt_block(gated)


def test_attempt_lemmas_feed_induction_matching() -> None:
    from problem_profiler import (
        attempt_lemmas_from_failed_data,
        build_problem_profile_incremental,
        clear_profiler_caches,
    )

    clear_profiler_caches()
    base = (
        "(= (len (append nil nil)) (len nil))"
    )
    failed = {
        "useless_lemma_groups": [{"lemmas": [base]}],
        "unproved_lemmas": [],
    }
    extras = attempt_lemmas_from_failed_data(failed)
    assert extras == [base] or any("len" in x for x in extras)

    p = build_problem_profile_incremental(
        SAMPLE_SMT,
        problem_id="t",
        current_goal=GOAL,
        attempt_lemmas=extras,
        cache_ns="attempt_ind",
    )
    att = p.induction_attempts[0]
    assert att.status == "known"
    assert "nil" in att.base_ctors


def test_int_binder_not_emitted_without_known_match() -> None:
    """Int recursion context alone does not inject attempt=none rows."""
    smt = """(set-logic UFLIA)
(declare-fun even (Int) Bool)
(assert (= (even 0) true))
(assert (forall ((n Int)) (=> (>= n 0) (= (even (+ 1 n)) (not (even n))))))
; proof goal
(assert (not (forall ((n Int)) (= (even (+ 1 (+ 1 n))) (even n)))))
; proof goal end
(check-sat)
"""
    profile = build_problem_profile(smt, problem_id="int_ind")
    assert profile.induction_attempts == []
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`even`" in block
    assert "attempt=none" not in block
    assert "Known induction attempts" not in block


def test_qsort_non_structural_recursive_call_with_filter_bridge() -> None:
    smt = Path(
        "benchmarks/preprocessed/autoproof/standard/sort_QSortCount/template.smt2"
    ).read_text(encoding="utf-8")
    profile = build_problem_profile(smt, problem_id="qsort")
    qsort = [r for r in profile.recursion_structure if r.function == "qsort"]
    assert qsort and qsort[0].kind == "recursive_call"
    assert "filter" in (qsort[0].bridge_peers or [])
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`qsort`: recursive_call" in block
    assert "not on constructor selectors" in block
    assert "via `filter`" in block
    assert "attempt=none" not in block


def test_bubsort_let_expanded_bridge_via_bubble() -> None:
    smt = Path(
        "benchmarks/preprocessed/autoproof/standard/sort_BubSortCount/template.smt2"
    ).read_text(encoding="utf-8")
    profile = build_problem_profile(smt, problem_id="bubsort")
    bub = [r for r in profile.recursion_structure if r.function == "bubsort"]
    assert bub and bub[0].kind == "recursive_call"
    assert "bubble" in (bub[0].bridge_peers or [])
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`bubsort`: recursive_call" in block
    assert "via `bubble`" in block


def test_count_int_list_to_int_is_observer() -> None:
    smt = """(set-logic UFDTLIA)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-fun count (Int Lst) Int)
(assert (forall ((x Int)) (= (count x nil) 0)))
(assert (forall ((x Int) (y Int) (z Lst))
  (= (count x (cons y z)) (ite (= x y) (+ 1 (count x z)) (count x z)))))
; proof goal
(assert (not (forall ((x Int) (l Lst)) (= (count x l) (count x l)))))
; proof goal end
(check-sat)
"""
    profile = build_problem_profile(smt, problem_id="count")
    obs = [o for o in profile.observer_candidates if o.function == "count"]
    assert obs
    assert obs[0].evidence_level == "structural"
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "`count`" in block
    assert "`Int`, `Lst` -> `Int`" in block or "`Int`, `Lst` -> `Int`" in block.replace(
        " ", ""
    ) or "Int" in block and "Lst" in block


def test_list_goal_int_element_binder_not_induction_candidate() -> None:
    """Int quantifiers that are only list elements must not become induction rows."""
    smt = Path(
        "benchmarks/preprocessed/autoproof/standard/sort_QSortCount/template.smt2"
    ).read_text(encoding="utf-8")
    profile = build_problem_profile(smt, problem_id="qsort_int")
    assert not any(a.induct_sort == "Int" for a in profile.induction_attempts)
    gated = gate_profile_for_prompt(profile)
    block = format_profile_prompt_block(gated)
    assert "var=`x`:`Int`" not in block
