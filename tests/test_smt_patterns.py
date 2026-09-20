"""Tests for CVC ``:pattern`` helpers and gating (any strategy mode)."""

from __future__ import annotations

import os

from smt_patterns import (
    equality_lhs,
    format_assert_line,
    has_directed_equality,
    infer_trigger_pattern,
    pattern_trigger_reasons,
    should_add_cvc_patterns,
    strip_bang_attrs,
    v2_pattern_features,
    v2_should_add_cvc_patterns,
)
from obligation_tree import inject_library_axioms
from exp_flags import apply_cvc_patterns_cli, cvc_patterns_enabled


def _ok(cond: bool, msg: str = "") -> None:
    assert cond, msg


def test_infer_pattern_on_directed_eq() -> None:
    f = "(forall ((x Bin) (y Bin)) (= (plus (s x) y) (s (plus x y))))"
    _ok(has_directed_equality(f), "directed")
    _ok(equality_lhs(f) == "(plus (s x) y)", equality_lhs(f))
    _ok(infer_trigger_pattern(f) == "((plus (s x) y))", infer_trigger_pattern(f))
    line = format_assert_line(f, add_pattern=True)
    _ok(line.startswith("(assert (! "), line)
    _ok(":pattern ((plus (s x) y))" in line, line)
    bare = format_assert_line(f, add_pattern=False)
    _ok(bare == f"(assert {f})", bare)
    named = format_assert_line(f, named="C1")
    _ok(":named C1" in named and f in named, named)
    both = format_assert_line(f, add_pattern=True, named="C1")
    _ok(":named C1" in both and ":pattern ((plus (s x) y))" in both, both)


def test_pattern_skips_var_eq_and_implications() -> None:
    _ok(not has_directed_equality("(forall ((x Nat)) (= x x))"))
    f = "(forall ((x Nat)) (=> (P x) (= (f x) (g x))))"
    _ok(has_directed_equality(f), f)
    _ok(infer_trigger_pattern(f) == "((f x))", infer_trigger_pattern(f))


def test_strip_bang_attrs() -> None:
    raw = "(! (forall ((x Nat)) (= (f x) x)) :pattern ((f x)))"
    _ok(strip_bang_attrs(raw) == "(forall ((x Nat)) (= (f x) x))", strip_bang_attrs(raw))


def test_inject_library_with_patterns() -> None:
    smt = """(set-logic ALL)
; proof goal
(assert (not true))
; proof goal end
"""
    formula = "(forall ((x Nat)) (= (plus x zero) x))"
    out = inject_library_axioms(
        smt,
        [{"id": "lib_1", "formula": formula}],
        add_patterns=True,
    )
    _ok("(assert (! (forall ((x Nat)) (= (plus x zero) x)) :pattern ((plus x zero)))" in out, out)
    bare = inject_library_axioms(
        smt,
        [{"id": "lib_1", "formula": formula}],
        add_patterns=False,
    )
    _ok(f"(assert {formula})" in bare, bare)
    _ok(":pattern" not in bare, bare)


def _rare_inst_failed() -> dict:
    return {
        "repair_hints": [{
            "kind": "high_difficulty_assertions",
            "rarely_instantiated": ["(forall ((x Nat)) true)"],
        }],
    }


def test_pattern_gate_requires_flag() -> None:
    eq = "(forall ((x Nat)) (= (f x) x))"
    failed = _rare_inst_failed()
    prev = os.environ.pop("CVC_PATTERNS", None)
    try:
        _ok(not cvc_patterns_enabled())
        _ok(not should_add_cvc_patterns(failed_data=failed, formulas=[eq]))
        # Feedback 6-way is deprecated: enabled=True still does not open.
        _ok(
            not should_add_cvc_patterns(
                failed_data=failed, formulas=[eq], enabled=True,
            )
        )
        _ok(
            not v2_should_add_cvc_patterns(
                strategy_mode="default",
                failed_data=failed,
                formulas=[eq],
                enabled=True,
            )
        )
        apply_cvc_patterns_cli("on")
        _ok(cvc_patterns_enabled())
        _ok(not should_add_cvc_patterns(failed_data=failed, formulas=[eq]))
        apply_cvc_patterns_cli("off")
        _ok(not should_add_cvc_patterns(failed_data=failed, formulas=[eq]))
        _ok(
            not should_add_cvc_patterns(
                failed_data={**failed, "cvc_patterns": True},
                formulas=[eq],
            )
        )
    finally:
        if prev is None:
            os.environ.pop("CVC_PATTERNS", None)
        else:
            os.environ["CVC_PATTERNS"] = prev


def test_pattern_feature_gates() -> None:
    eq = "(forall ((x Nat)) (= (f x) x))"
    rare = _rare_inst_failed()
    # usefulness timeout is logged, but does not open 6-way ±pattern
    _ok(
        not should_add_cvc_patterns(
            failed_data={"useless_lemma_groups": [{"lemmas": [eq], "status": "timeout"}]},
            formulas=[eq],
            enabled=True,
        )
    )
    feats_to = v2_pattern_features(
        {"useless_lemma_groups": [{"lemmas": [eq], "status": "timeout"}]}
    )
    _ok(feats_to["useful_timeout"] and not feats_to["trigger"], feats_to)
    # need_rewrite / rewrite_scarce do not open
    _ok(
        not should_add_cvc_patterns(
            failed_data={"repair_hints": [{"kind": "need_rewrite"}]},
            formulas=[eq],
            enabled=True,
        )
    )
    # rare_inst + directed eq + flag still does not open (deprecated 6-way)
    _ok(
        not should_add_cvc_patterns(
            failed_data=rare,
            formulas=[eq],
            enabled=True,
        )
    )
    _ok(
        not should_add_cvc_patterns(
            failed_data=rare,
            formulas=[eq],
            enabled=False,
        )
    )
    # low em/conj alone does NOT open (would prefer successes on full706)
    _ok(
        not should_add_cvc_patterns(
            failed_data={
                "baseline_diag": {
                    "stats": {
                        "QUANTIFIERS_INST_E_MATCHING": 10,
                        "INST_TOTAL": 10,
                        "CONJ_TOTAL": 10,
                        "QUANTIFIERS_SKOLEMIZE": 0,
                    }
                },
            },
            formulas=[eq],
            enabled=True,
        )
    )
    # rare_inst but no directed equality
    _ok(
        not should_add_cvc_patterns(
            failed_data=rare,
            formulas=["(forall ((x Nat)) true)"],
            enabled=True,
        )
    )
    # explosion ignored (always off in features)
    feats = v2_pattern_features(
        {
            **rare,
            "progress_routing_signals": ["search_explosion(+50%)"],
        }
    )
    _ok(feats["rare_inst"] and feats["trigger"], feats)
    _ok(feats["search_explosion"] is False, feats)
    _ok(pattern_trigger_reasons(rare) == ["rare_inst"])
    _ok(pattern_trigger_reasons(
        {"useless_lemma_groups": [{"status": "timeout"}]}
    ) == [])


def main() -> None:
    test_infer_pattern_on_directed_eq()
    test_pattern_skips_var_eq_and_implications()
    test_strip_bang_attrs()
    test_inject_library_with_patterns()
    test_pattern_gate_requires_flag()
    test_pattern_feature_gates()
    print("ok")


if __name__ == "__main__":
    main()
