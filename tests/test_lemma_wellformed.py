#!/usr/bin/env python3
"""Well-formedness gate: parse_error / type_error before portfolio prove."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")
os.environ["LEMMA_WELLFORMED_CHECK"] = "on"
os.environ["LEMMA_FILTER_DROP"] = "on"

from cvc5_runner import (  # noqa: E402
    check_lemma_wellformed,
    classify_cvc_wellformed_message,
)
from lemma_gates import (  # noqa: E402
    ILLFORMED_SCREEN_GATES,
    apply_static_lemma_screen,
    format_screen_retry_user,
    reserved_binder_names,
    screen_lemmas_wellformed,
)
import Mate_new as mate  # noqa: E402

QSORT_SMT = (ROOT / "benchmarks/preprocessed/autoproof/standard/sort_QSortCount/template.smt2").read_text(
    encoding="utf-8"
)
RELAXED_SMT = (
    ROOT / "benchmarks/preprocessed/autoproof/standard/relaxedprefix_correct/template.smt2"
).read_text(encoding="utf-8")

PLUS_LEMMA = (
    "(forall ((x Int) (l1 list) (l2 list)) "
    "(= (count x (append l1 l2)) (plus (count x l1) (count x l2))))"
)
ARITH_LEMMA = (
    "(forall ((x Int) (a list) (b list)) "
    "(= (count x a) (+ (count x a) (count x b))))"
)
AS_LEMMA = "(forall ((as list) (b list)) (= as b))"
OK_LEMMA = "(forall ((x Int) (xs list)) (= (count x xs) (count x xs)))"


def fail(msg: str) -> None:
    raise AssertionError(msg)


def test_classify_type_vs_parse() -> None:
    kind, _ = classify_cvc_wellformed_message(
        '(error "Parse Error: f.smt2:1.1: expecting an arithmetic subterm")'
    )
    assert kind == "type_error", kind
    kind, _ = classify_cvc_wellformed_message(
        "(error \"Parse Error: f.smt2:1.1: Symbol 'plus' not declared as a variable\")"
    )
    assert kind == "parse_error", kind


def test_reserved_binder() -> None:
    assert reserved_binder_names(AS_LEMMA) == ["as"]
    assert reserved_binder_names(OK_LEMMA) == []


def test_cvc5_wellformed_on_audit_cases() -> None:
    r = check_lemma_wellformed(PLUS_LEMMA, QSORT_SMT)
    assert not r.ok and r.kind == "parse_error", r
    r = check_lemma_wellformed(ARITH_LEMMA, QSORT_SMT)
    assert not r.ok and r.kind == "type_error", r
    r = check_lemma_wellformed(AS_LEMMA, RELAXED_SMT)
    assert not r.ok and r.kind == "parse_error", r
    r = check_lemma_wellformed(OK_LEMMA, QSORT_SMT)
    assert r.ok, r


def test_screen_drops_illformed_not_as_invalid_gate() -> None:
    kept, dropped = screen_lemmas_wellformed(
        [PLUS_LEMMA, ARITH_LEMMA, OK_LEMMA], QSORT_SMT
    )
    assert kept == [OK_LEMMA], kept
    gates = {g for _l, _r, g in dropped}
    assert gates <= ILLFORMED_SCREEN_GATES, gates
    assert "parse_error" in gates and "type_error" in gates


def test_static_screen_includes_wellformed() -> None:
    kept, dropped = apply_static_lemma_screen(
        [PLUS_LEMMA, OK_LEMMA],
        original_forall="(forall ((xs list)) false)",
        smt=QSORT_SMT,
        invalid_records=[],
        same_as_goal=lambda a, b: False,
    )
    assert OK_LEMMA in kept
    assert any(g in ILLFORMED_SCREEN_GATES for _l, _r, g in dropped)
    text = format_screen_retry_user(dropped)
    assert "parse_error" in text or "plus" in text.lower()


def test_illformed_not_written_as_invalid() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        mate.add_illformed_lemma(tmp, "template", PLUS_LEMMA, "Symbol 'plus' not declared", kind="parse_error")
        data = mate.load_failed_lemmas(tmp, "template")
        assert data.get("invalid_lemmas") in ([], None) or data["invalid_lemmas"] == []
        assert data["illformed_lemmas"]
        assert data["illformed_lemmas"][0]["kind"] == "parse_error"


def main() -> None:
    test_classify_type_vs_parse()
    test_reserved_binder()
    test_cvc5_wellformed_on_audit_cases()
    test_screen_drops_illformed_not_as_invalid_gate()
    test_static_screen_includes_wellformed()
    test_illformed_not_written_as_invalid()
    print("PASS test_lemma_wellformed")


if __name__ == "__main__":
    main()
