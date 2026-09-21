#!/usr/bin/env python3
"""P0 feedback fixes: difficulty parse, goal/axiom roles, Vampire errors, rates.

Run from repo root:

    python3 tests/test_feedback_p0.py
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import cvc5_runner
from cvc5_runner import (
    CvcResult,
    classify_difficulty_term,
    compute_progress_score,
    derive_repair_hints,
    extract_proof_goal_term,
    hard_axioms_from_difficulty,
    parse_cvc_difficulty,
    parse_cvc_instantiations,
    parse_cvc_stats,
    rarely_instantiated_axioms,
)
from solver_relative_metrics import is_relative_gain, pct_label
from vampire_runner import classify_status


def _ok(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


NESTED_PLUS = (
    "(forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m))))"
)
GOAL = "(not (forall ((x Z) (y Z)) (= (plus2 x y) (plus2 y x))))"
NEGATED_AXIOM = "(not (forall ((n Nat)) (= (plus n n) n)))"
AXIOM = "(forall ((n Nat)) (= (plus zero n) n))"


def test_parse_nested_difficulty() -> None:
    text = f"unknown\n(\n({NESTED_PLUS} 10)\n({GOAL} 3)\n)\n"
    items = parse_cvc_difficulty(text)
    scores = {term: score for term, score in items}
    _ok(scores.get(NESTED_PLUS) == 10, f"nested plus/succ score: {items}")
    _ok(scores.get(GOAL) == 3, f"negated forall goal: {items}")


def test_parse_named_assertion() -> None:
    named = "(! (forall ((n Nat)) (= n n)) :named plus_id)"
    text = f"unknown\n(({named} 7))\n"
    items = parse_cvc_difficulty(text)
    _ok(len(items) == 1 and items[0][1] == 7, f"named assertion: {items}")
    _ok(classify_difficulty_term(items[0][0]) == "axiom", items[0][0])


def test_parse_named_symbol_difficulty() -> None:
    from cvc5_runner import attributed_candidate_ids, expand_named_difficulty

    text = "unknown\n(\n(C1 756)\n((forall ((n Nat)) (= n n)) 3)\n)\n"
    items = parse_cvc_difficulty(text)
    scores = {term: score for term, score in items}
    _ok(scores.get("C1") == 756, items)
    _ok(any("forall" in t for t in scores), items)
    mapping = {"C1": "(forall ((x Nat)) (= (plus x zero) x))"}
    expanded = expand_named_difficulty(items, mapping)
    _ok(any("plus x zero" in t for t, _s in expanded), expanded)
    ids = attributed_candidate_ids(items, mapping)
    _ok(ids == ["C1"], ids)


def test_extract_proof_goal_block() -> None:
    smt = """(set-logic UFDT)
(assert (forall ((n Nat)) (= (plus zero n) n)))
; proof goal
(assert (not (forall ((x Z) (y Z)) (= (plus2 x y) (plus2 y x)))))
; proof goal end
(check-sat)
"""
    got = extract_proof_goal_term(smt)
    _ok(got is not None and "plus2" in got, f"proof-goal extract: {got}")
    _ok(classify_difficulty_term(got) == "goal", got)


def test_goal_diff_ignores_front_negated_axiom() -> None:
    base = CvcResult(
        status="timeout",
        elapsed=3.0,
        difficulty=[(NEGATED_AXIOM, 20), (AXIOM, 10), (GOAL, 8)],
        goal_term=GOAL,
    )
    cand = CvcResult(
        status="timeout",
        elapsed=3.0,
        difficulty=[(NEGATED_AXIOM, 20), (AXIOM, 10), (GOAL, 2)],
        goal_term=GOAL,
    )
    _score, signals = compute_progress_score(base, cand)
    _ok(
        any("goal_difficulty_drop" in s and "8->2" in s for s in signals),
        f"should track proof-goal 8→2, got {signals}",
    )
    hints = derive_repair_hints(base)
    hard = hints[0].get("hard_axioms") or []
    fragments = hints[0].get("goal_fragments") or []
    _ok(any("plus2" in g for g in fragments), f"goal_fragments: {fragments}")
    _ok(
        not any("plus2" in ax for ax in hard),
        f"proof goal must not be listed as hard_axioms: {hard}",
    )
    via_helper = hard_axioms_from_difficulty(base.difficulty, base.goal_term)
    _ok(via_helper == hard, f"helper must match derive: {via_helper} vs {hard}")


def test_hard_axioms_not_raw_score_topk() -> None:
    """Prompt hard_axioms must skip the proof goal even if it ranks first."""
    other_ax = "(forall ((n Nat)) (= (plus (succ n) n) (succ n)))"
    difficulty = [(GOAL, 99), (NEGATED_AXIOM, 80), (AXIOM, 10), (other_ax, 5)]
    hard = hard_axioms_from_difficulty(difficulty, GOAL, limit=4)
    _ok(GOAL not in hard, f"proof goal leaked into hard_axioms: {hard}")
    _ok(all("plus2" not in ax for ax in hard), f"goal fragment in hard_axioms: {hard}")
    _ok(AXIOM in hard, f"real axiom missing: {hard}")
    _ok(NEGATED_AXIOM in hard, f"negated axiom should stay an axiom: {hard}")


def test_hard_axioms_rank_by_difficulty_and_keep_scores() -> None:
    """Hard axioms stay difficulty-ordered; scores stay available for the prompt."""
    from cvc5_runner import hard_axiom_entries_from_difficulty
    from lemma_gates import format_attempt_feedback_for_prompt

    goal = "(forall ((t Tree)) (= (mirror (mirror t)) t))"
    mirror_ax = (
        "(forall ((a Tree) (b Tree)) "
        "(= (mirror (Node a b)) (Node (mirror b) (mirror a))))"
    )
    rotate_ax = (
        "(forall ((x Nat) (y Lst)) "
        "(= (rotate (succ x) y) "
        "(rotate x (append y (cons (head y) nil)))))"
    )
    difficulty = [
        (rotate_ax, 90),
        (mirror_ax, 50),
        ("(forall ((x Nat)) (= (plus x zero) x))", 40),
        ("(forall ((x Nat)) (= (plus zero x) x))", 30),
        ("(forall ((x Nat)) (= (succ (pred x)) x))", 20),
    ]
    entries = hard_axiom_entries_from_difficulty(difficulty, goal, limit=4)
    ordered = [t for t, _s in entries]
    _ok(
        ordered[0] == rotate_ax,
        f"highest difficulty should rank first: {ordered}",
    )
    _ok(mirror_ax in ordered, f"lower-d axiom still listed: {ordered}")
    scores = {t: s for t, s in entries}
    _ok(scores.get(rotate_ax) == 90, f"rotate score missing: {scores}")
    hints = derive_repair_hints(
        CvcResult(status="timeout", elapsed=1.0, difficulty=difficulty, goal_term=goal)
    )
    _ok(hints and hints[0].get("hard_axiom_scores"), f"scores not on hint: {hints}")
    txt = format_attempt_feedback_for_prompt({"repair_hints": hints}, backend="cvc5")
    _ok("d=90" in txt and "d=50" in txt, f"prompt should show d= scores: {txt}")
    _ok(txt.index("d=90") < txt.index("d=50"), f"difficulty order in prompt: {txt}")
    _ok("not proof necessity" in txt, f"neutral difficulty explain missing: {txt}")
    _ok("help prove the CURRENT goal" in txt, f"useful-lemma HD hint missing: {txt}")
    _ok("share symbols" not in txt, f"symbol-sharing wording should be gone: {txt}")


def test_axiom_disappear_from_complete_dump_is_drop() -> None:
    """Unlisted in a non-empty dump is official difficulty 0, so a drop is real."""
    base = CvcResult(
        status="timeout",
        elapsed=3.0,
        difficulty=[(NESTED_PLUS, 10), (GOAL, 1)],
        goal_term=GOAL,
    )
    cand = CvcResult(
        status="timeout",
        elapsed=3.0,
        difficulty=[(GOAL, 1)],
        goal_term=GOAL,
    )
    _score, signals = compute_progress_score(base, cand)
    _ok(
        any("axiom_difficulty_drop" in s for s in signals),
        f"complete dump: leaving the list is 0: {signals}",
    )


def test_missing_dump_does_not_count_axiom_disappear() -> None:
    base = CvcResult(
        status="timeout",
        elapsed=3.0,
        difficulty=[(NESTED_PLUS, 10), (GOAL, 1)],
        goal_term=GOAL,
    )
    cand = CvcResult(
        status="timeout",
        elapsed=3.0,
        difficulty=[],
        goal_term=GOAL,
    )
    _score, signals = compute_progress_score(base, cand)
    _ok(
        not any("axiom_difficulty_drop" in s for s in signals),
        f"empty dump is missing, not all-zero: {signals}",
    )


def test_parse_cvc_difficulty_keeps_full_dump() -> None:
    entries = "\n".join(f"((P {i}) {20 - i})" for i in range(15))
    items = parse_cvc_difficulty("unknown\n(\n" + entries + "\n)\n")
    _ok(len(items) == 15, f"must not cap at 12: {len(items)}")


def test_vampire_user_error() -> None:
    snippet = (
        "User error: SMTLIB2 parse error in file goal.smt2, line 12, column 3:\n"
        "unexpected token: )\n"
    )
    _ok(
        classify_status("", snippet, 1, False) == "error",
        "User error: must be classified as error",
    )
    _ok(
        classify_status("% SZS status Error for goal\n", "", 1, False) == "error",
        "SZS Error must be classified as error",
    )
    # "user:" is not a sufficient condition (Vampire prints "User error:").
    status = classify_status(
        "Proof not found\nuser: lemma_foo is unused\n",
        "",
        0,
        False,
    )
    _ok(status != "error", f"'user:' substring must not force error, got {status}")


def test_relative_gain_rate_vs_count() -> None:
    _ok(is_relative_gain(0.9, 0.4, kind="rate"), "0.4/s → 0.9/s is a rate gain")
    _ok(
        not is_relative_gain(101, 100, kind="count"),
        "count 100→101 non-rare is not a gain",
    )
    _ok(pct_label(0.9, 0.4, kind="rate") == 125, "rate percent uses max(ref, ε)")


def test_stat_keys_not_double_counted() -> None:
    _ok(
        not hasattr(cvc5_runner, "STAT_KEY_PATTERNS"),
        "dead overlapping STAT_KEY_PATTERNS must be gone",
    )
    text = (
        "QUANTIFIERS_INST_E_MATCHING : 10\n"
        "QUANTIFIERS_INST_E_MATCHING_SIMPLE : 5\n"
        "QUANTIFIERS_SKOLEMIZE : 2\n"
    )
    stats = parse_cvc_stats(text)
    _ok(stats["QUANTIFIERS_INST_E_MATCHING"] == 10, stats)
    _ok(stats["QUANTIFIERS_INST_E_MATCHING_SIMPLE"] == 5, stats)
    _ok(stats["INST_TOTAL"] == 15, f"INST_TOTAL double-count? {stats}")
    _ok("SKOLEMIZE" not in stats, stats)
    _ok(stats["QUANTIFIERS_SKOLEMIZE"] == 2, stats)


def test_parse_cvc_instantiations_qid_and_formula() -> None:
    axiom = "(forall ((n Nat)) (= (plus zero n) n))"
    text = f"(num-instantiations plus.zero 7)\n(num-instantiations {axiom} 2)\n"
    items = parse_cvc_instantiations(text)
    by_term = {t: n for t, n in items}
    _ok(by_term.get("plus.zero") == 7, items)
    _ok(any(t.startswith("(") and n == 2 for t, n in items), items)
    _ok(
        rarely_instantiated_axioms([axiom], [("plus.zero", 7)]) == [],
        "qid-only must not mark the axiom rare",
    )


def main() -> int:
    tests = [
        test_parse_nested_difficulty,
        test_parse_named_assertion,
        test_parse_named_symbol_difficulty,
        test_extract_proof_goal_block,
        test_goal_diff_ignores_front_negated_axiom,
        test_hard_axioms_not_raw_score_topk,
        test_hard_axioms_rank_by_difficulty_and_keep_scores,
        test_axiom_disappear_from_complete_dump_is_drop,
        test_missing_dump_does_not_count_axiom_disappear,
        test_parse_cvc_difficulty_keeps_full_dump,
        test_vampire_user_error,
        test_relative_gain_rate_vs_count,
        test_stat_keys_not_double_counted,
        test_parse_cvc_instantiations_qid_and_formula,
    ]
    failed = 0
    for fn in tests:
        try:
            fn()
            print(f"ok  {fn.__name__}")
        except Exception as e:
            failed += 1
            print(f"FAIL {fn.__name__}: {e}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
