"""CVC sat / get-model → invalid reason text."""

from __future__ import annotations

import tempfile
from pathlib import Path
from unittest.mock import patch

from cvc5_runner import (
    format_counterexample_reason,
    parse_cvc_model,
    prepare_smt_for_get_model,
    run_cvc_counterexample,
    smt_negate_proof_goal_assert,
    counterexample_reason_for_smt,
)


def _ok(cond: bool, msg: object = "") -> None:
    assert cond, msg


def test_parse_and_format_model() -> None:
    text = """sat
(
(define-fun p ((_arg_1 nat)) Bool false)
)
"""
    model = parse_cvc_model(text)
    _ok(model is not None and "define-fun p" in model, model)
    reason = format_counterexample_reason(model)
    _ok(reason.startswith("Counterexample:"), reason)
    _ok(format_counterexample_reason(None) == "solver:sat")


def test_prepare_and_negate_goal() -> None:
    smt = """(set-logic ALL)
; proof goal
(assert (forall ((x Int)) (= x x)))
; proof goal end
(check-sat)
"""
    neg = smt_negate_proof_goal_assert(smt)
    _ok("(assert (not (forall" in neg.replace("\n", " "), neg)
    prep = prepare_smt_for_get_model(neg)
    _ok("produce-models" in prep, prep)
    _ok("(get-model)" in prep, prep)


def test_live_cvc_counterexample_on_refuted_goal() -> None:
    smt = """(set-logic ALL)
(declare-datatypes ((nat 0)) (((zero) (s (pred nat)))))
(declare-fun p (nat) Bool)
; proof goal
(assert (not (forall ((x nat)) (p x))))
; proof goal end
(check-sat)
"""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "g.smt2"
        path.write_text(smt, encoding="utf-8")
        result = run_cvc_counterexample(path, timeout=3)
        _ok(result.status == "sat", result.status)
        _ok(bool(result.model_text), result.stdout[:200])
        reason = counterexample_reason_for_smt(path, fallback="solver:sat")
        _ok(reason.startswith("Counterexample:"), reason)


def test_validity_unsat_keeps_simple_reason() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    lemma = "(forall ((x Int)) false)"
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        valid = base / "template_valid_1.smt2"
        valid.write_text(
            "(set-logic ALL)\n; proof goal\n"
            f"(assert {lemma})\n; proof goal end\n(check-sat)\n",
            encoding="utf-8",
        )
        with patch(
            "Mate_new.verify_single_lemma",
            return_value=(valid, CvcResult(proved=True, status="unsat")),
        ), patch("Mate_new.counterexample_reason_for_smt") as cex:
            kept = mate.validate_lemmas_parallel([valid], [lemma], tmp, "template")
        cex.assert_not_called()
        _ok(kept == [], kept)
        inv = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        _ok(len(inv) == 1, inv)
        _ok(inv[0]["reason"] == "contradicts axioms (cvc=unsat)", inv[0]["reason"])


def test_cvc_sat_abort_stores_cex_reason() -> None:
    import Mate_new as mate
    from cvc5_runner import CvcResult

    goal = """(set-logic ALL)
(declare-fun P (Int) Bool)
; proof goal
(assert (not (forall ((x Int)) (P x))))
; proof goal end
(check-sat)
"""
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "template.smt2").write_text(goal, encoding="utf-8")
        sat = CvcResult(status="sat", proved=False, elapsed=0.05)
        with patch.dict(
            __import__("os").environ,
            {"SUBGOAL_SAT_ABORT": "on", "SOLVER_ROUTING": "off", "LEMMA_LIBRARY": "off"},
        ), patch("Mate_new.run_cvc_routed", return_value=sat), patch(
            "Mate_new.counterexample_reason_for_smt",
            return_value="Counterexample: (define-fun P () Bool false)",
        ), patch("Mate_new.generate_lemmas_with_llm") as gen:
            ok = mate.prove_run(tmp, "template", depth=1)
        _ok(ok is False)
        gen.assert_not_called()
        outcome = mate.load_failed_lemmas(tmp, "template")["node_outcome"]
        _ok(outcome.get("kind") == "invalid", outcome)
        _ok("Counterexample" in outcome.get("reason", ""), outcome)


def main() -> int:
    test_parse_and_format_model()
    test_prepare_and_negate_goal()
    test_live_cvc_counterexample_on_refuted_goal()
    test_validity_unsat_keeps_simple_reason()
    test_cvc_sat_abort_stores_cex_reason()
    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
