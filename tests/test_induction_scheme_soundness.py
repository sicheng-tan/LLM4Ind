#!/usr/bin/env python3
"""No-LLM scheme soundness / generation tests against benchmark templates.

Focus: wrong obligations must not validate; validated schemes must match the
goal matrix; unvalidated schemes must never pending-close the parent.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from induction_scheme.dispatch import finalize_after_attempt, run_scheme_round
from induction_scheme.generate import generate_scheme
from induction_scheme.types import SchemeAttempt, SchemeObligation, SchemeRoundResult
from problem_profiler.induction_attempts import _split_forall, _subst_free
from smt_patterns import normalize_lemma_formula, sexpr_head_args

BENCH = ROOT / "benchmarks" / "preprocessed"


def _read(*parts: str) -> str:
    return (BENCH.joinpath(*parts)).read_text(encoding="utf-8")


def _peel_forall(formula: str) -> str:
    h, a = sexpr_head_args(formula) if formula.startswith("(") else (None, [])
    if h == "forall" and a:
        return a[-1]
    return formula


def test_int_add_assoc_no_bare_P_or_N() -> None:
    """Z.P/N take a Nat — base must be (P _b0)/(N _b0), never bare P/N.

    Bare constructors previously validated and could have falsely closed.
    """
    smt = _read("autoproof", "standard", "int_add_assoc", "template.smt2")
    att = generate_scheme(smt, goal_name="int_add_assoc")
    assert not att.skipped
    assert att.induct_var == "x" and att.induct_sort == "Z"
    assert att.validated, att.validate_errors
    kinds = {(o.kind, o.ctor) for o in att.obligations}
    assert kinds == {("base", "P"), ("base", "N")}
    for o in att.obligations:
        assert o.inst_term.startswith("("), o.inst_term
        assert o.ctor in o.inst_term
        assert f"({o.ctor} " in o.formula or f"({o.ctor}\n" in o.formula
        # Must not substitute the bare constructor constant.
        assert f"(plus2 {o.ctor} " not in o.formula


def test_crafted_even_implication_goal_validates() -> None:
    smt = _read("ind-ben", "nat", "crafted_even", "0", "template.smt2")
    att = generate_scheme(smt, goal_name="crafted_even0")
    assert att.induct_sort == "nat"
    assert att.validated, att.validate_errors
    base = next(o for o in att.obligations if o.kind == "base")
    step = next(o for o in att.obligations if o.kind == "step")
    assert base.ctor == "zero"
    assert step.ctor == "s"
    assert "(=>" in step.formula
    # Base keeps the full implication matrix, not only the consequent.
    assert "even zero" in base.formula
    assert "even y" in base.formula


def test_crafted_assorted9_pref_goal_validates() -> None:
    smt = _read("ind-ben", "list", "crafted_assorted", "9", "template.smt2")
    att = generate_scheme(smt, goal_name="assorted9")
    assert att.induct_sort == "lst"
    assert att.validated, att.validate_errors
    assert {o.ctor for o in att.obligations} >= {"nil", "cons"}


def test_bin_plus_assoc_step_ih_and_coverage() -> None:
    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")
    att = generate_scheme(smt, goal_name="bin_plus_assoc")
    assert att.validated, att.validate_errors
    assert att.induct_var == "x"
    ctors = {o.ctor for o in att.obligations}
    assert ctors == {"One", "ZeroAnd", "OneAnd"}
    for o in att.obligations:
        if o.kind == "step":
            body = _peel_forall(o.formula)
            h, a = sexpr_head_args(body)
            assert h == "=>"
            assert "_ih" in a[0]
            assert o.ctor in a[-1]


def test_tree_flatten2_leaf_node_from_benchmark() -> None:
    smt = _read("autoproof", "standard", "tree_Flatten2", "template.smt2")
    att = generate_scheme(smt, goal_name="tree_Flatten2")
    assert att.induct_var == "p" and att.induct_sort == "Tree"
    assert att.validated, att.validate_errors
    assert {o.ctor for o in att.obligations} == {"Nil", "Node"}
    step = next(o for o in att.obligations if o.ctor == "Node")
    # Two recursive Tree positions → and of IHs.
    assert "(and " in step.formula


def test_rotate_snoc_scheme_shape() -> None:
    smt = _read("autoproof", "standard", "rotate_snoc", "template.smt2")
    att = generate_scheme(smt, goal_name="rotate_snoc")
    assert att.induct_var == "xs" and att.induct_sort == "list"
    assert att.validated, att.validate_errors
    assert {o.kind for o in att.obligations} == {"base", "step"}


def test_base_body_equals_matrix_subst() -> None:
    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")
    att = generate_scheme(smt, goal_name="bin")
    from problem_profiler import build_problem_profile

    profile = build_problem_profile(smt)
    goal = next(f.raw for f in profile.formulas if f.role == "goal")
    binders, matrix = _split_forall(goal)
    for o in att.obligations:
        if o.kind != "base":
            continue
        expected = _subst_free(matrix, {att.induct_var: o.inst_term})
        got = _peel_forall(o.formula)
        assert normalize_lemma_formula(got) == normalize_lemma_formula(expected)


def test_unvalidated_scheme_never_pending_close() -> None:
    att = SchemeAttempt(
        goal_name="bad",
        induct_var="x",
        induct_sort="Lst",
        validated=False,
        validate_errors=["subst_mismatch:base_nil"],
        obligations=[
            SchemeObligation(
                obl_id="base_nil", kind="base", ctor="nil",
                formula="(= 1 1)", induct_var="x", induct_sort="Lst",
                status="proved",
            ),
        ],
    )
    # Force close_parent=True as if a buggy caller asked — finalize must refuse.
    rr = SchemeRoundResult(attempt=att, close_parent=True)
    data = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=False)
    assert "scheme_pending_close" not in data
    assert att.all_proved() is False


def test_bare_ctor_rejected_by_validation() -> None:
    """Hand-crafted bare P obligation must fail validate (Z.P needs Nat arg)."""
    smt = _read("autoproof", "standard", "int_add_assoc", "template.smt2")
    att = generate_scheme(smt, goal_name="int_add_assoc")
    assert att.validated
    # Corrupt one obligation to the old buggy shape.
    bad = att.obligations[0]
    bad.formula = (
        "(forall ((y Z) (z Z)) "
        "(= (plus2 P (plus2 y z)) (plus2 (plus2 P y) z)))"
    )
    bad.inst_term = "P"
    from induction_scheme.generate import validate_scheme
    from problem_profiler import build_problem_profile
    from problem_profiler.induction_attempts import _split_forall

    profile = build_problem_profile(smt)
    goal = next(f.raw for f in profile.formulas if f.role == "goal")
    binders, matrix = _split_forall(goal)
    ok, errs = validate_scheme(
        att.obligations,
        binders=binders,
        matrix=matrix,
        var=att.induct_var,
        sort=att.induct_sort,
        profile=profile,
    )
    assert ok is False
    assert any("bare_ctor" in e or "subst_mismatch" in e for e in errs)


def test_incomplete_ctors_not_validated() -> None:
    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")
    att = generate_scheme(smt, goal_name="bin")
    # Drop OneAnd step.
    att.obligations = [o for o in att.obligations if o.ctor != "OneAnd"]
    from induction_scheme.generate import validate_scheme
    from problem_profiler import build_problem_profile
    from problem_profiler.induction_attempts import _split_forall

    profile = build_problem_profile(smt)
    goal = next(f.raw for f in profile.formulas if f.role == "goal")
    binders, matrix = _split_forall(goal)
    ok, errs = validate_scheme(
        att.obligations,
        binders=binders,
        matrix=matrix,
        var=att.induct_var,
        sort=att.induct_sort,
        profile=profile,
    )
    assert ok is False
    assert any("incomplete_ctors" in e for e in errs)


def test_validated_mock_prove_can_pending_close_usefulness_blocks() -> None:
    """Validated + all proved + gate ok → pending close; usefulness suppresses it."""
    smt = _read("ind-ben", "nat", "crafted_even", "0", "template.smt2")
    import tempfile
    from pathlib import Path

    def always_unsat(path, timeout, profiles):
        return MagicMock(proved=True, status="unsat", elapsed=0.01)

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "on"}):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="even0",
                work_dir=Path(tmp),
                prove_fn=always_unsat,
                do_prove=True,
                nest_budget=0,
                max_depth=3,
            )
    assert rr.attempt.validated
    assert rr.attempt.goal_gate_status == "proved"
    assert rr.close_parent is True
    data = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=False)
    assert data.get("scheme_pending_close", {}).get("reason") == "short_prove"

    data2 = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=True)
    assert "scheme_pending_close" not in data2


def test_list_return_skips_no_induct() -> None:
    smt = _read("autoproof", "standard", "list_return_1", "template.smt2")
    att = generate_scheme(smt, goal_name="list_return_1")
    assert att.skipped
    assert not att.obligations


def test_goal_gate_timeout_allows_prove_but_not_close() -> None:
    """Gate timeout → still short-prove obligations; no pending close."""
    from induction_scheme.ledger import format_scheme_prompt_block, save_scheme_attempt
    import tempfile
    from pathlib import Path

    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")
    proved_ids = []

    def prove_fn(path, timeout, profiles):
        name = Path(path).name
        if "goal_gate" in name:
            return MagicMock(proved=False, status="timeout", elapsed=10.0)
        proved_ids.append(name)
        return MagicMock(proved=True, status="unsat", elapsed=0.05)

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "on"}):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="bin",
                work_dir=Path(tmp),
                prove_fn=prove_fn,
                do_prove=True,
                nest_budget=0,
                max_depth=3,
            )
    assert rr.attempt.goal_gate_status == "timeout"
    assert not rr.attempt.gate_blocks_scheme()
    assert not rr.attempt.goal_gate_ok()
    assert rr.close_parent is False
    assert proved_ids, "obligation prove should run after gate timeout"
    data = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=False)
    assert "scheme_pending_close" not in data
    data = save_scheme_attempt(data, rr.attempt)
    # Prompt shows proved facts only (mock proves all obligations).
    block = format_scheme_prompt_block(data)
    assert "INDUCTION SCHEME" in block
    assert "Proved structural" in block


def test_goal_gate_failed_blocks_scheme() -> None:
    """Gate sat/failed → no obligation prove, no nest, no prompt."""
    from induction_scheme.ledger import format_scheme_prompt_block, save_scheme_attempt
    import tempfile
    from pathlib import Path

    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")

    def prove_fn(path, timeout, profiles):
        name = Path(path).name
        if "goal_gate" in name:
            return MagicMock(proved=False, status="sat", elapsed=0.1)
        raise AssertionError(f"obligation prove should not run after gate fail: {name}")

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "on"}):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="bin",
                work_dir=Path(tmp),
                prove_fn=prove_fn,
                do_prove=True,
                nest_budget=1,
                max_depth=3,
            )
    assert rr.attempt.goal_gate_status == "failed"
    assert rr.attempt.gate_blocks_scheme()
    assert rr.close_parent is False
    assert rr.nest_children == []
    data = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=False)
    assert "scheme_pending_close" not in data
    data = save_scheme_attempt(data, rr.attempt)
    assert format_scheme_prompt_block(data) == ""


def test_scheme_only_gate_fail_returns_open() -> None:
    """scheme-only child with hard-failed gate → open, not proved."""
    from induction_scheme.mate_glue import run_scheme_only_node
    import tempfile
    from pathlib import Path

    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")
    outcomes = []

    def prove_fn(path, timeout, profiles):
        name = Path(path).name
        if "goal_gate" in name:
            return MagicMock(proved=False, status="sat", elapsed=0.1)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    store = {}

    def load_failed():
        return dict(store)

    def save_failed(d):
        store.clear()
        store.update(d)

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "on", "INDUCTION_SCHEME": "on"}):
        with tempfile.TemporaryDirectory() as tmp:
            ok = run_scheme_only_node(
                smt_content=smt,
                goal_name="bin_sch",
                work_dir=Path(tmp),
                depth=1,
                max_depth=3,
                nest_budget=0,
                skip_initial=True,
                current_goal=None,
                load_failed=load_failed,
                save_failed=save_failed,
                set_outcome=lambda **kw: outcomes.append(kw),
                child_prove_fn=lambda *a, **k: False,
                prove_fn=prove_fn,
            )
    assert ok is False
    assert outcomes and outcomes[-1].get("kind") == "open"
    assert "scheme_goal_gate_" in str(outcomes[-1].get("reason") or "")


def test_goal_gate_off_allows_close_without_g() -> None:
    import tempfile
    from pathlib import Path

    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")

    def prove_fn(path, timeout, profiles):
        return MagicMock(proved=True, status="unsat", elapsed=0.05)

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "off"}):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="bin",
                work_dir=Path(tmp),
                prove_fn=prove_fn,
                do_prove=True,
                nest_budget=0,
                max_depth=3,
            )
    assert rr.attempt.goal_gate_status == "off"
    assert rr.close_parent is True
    data = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=False)
    assert data.get("scheme_pending_close", {}).get("reason") == "short_prove"


def test_write_goal_gate_smt_keeps_original_goal() -> None:
    from induction_scheme.prove import write_goal_gate_smt
    import tempfile
    from pathlib import Path

    smt = _read("autoproof", "standard", "bin_plus_assoc", "template.smt2")
    att = generate_scheme(smt, goal_name="bin")
    with tempfile.TemporaryDirectory() as tmp:
        dest = Path(tmp) / "gate.smt2"
        assert write_goal_gate_smt(smt, att.obligations, dest)
        text = dest.read_text()
    assert "induction scheme goal-gate axioms" in text
    assert "(assert (not" in text  # original G
    for o in att.obligations:
        assert f"(assert {o.formula})" in text


def test_goal_gate_flag_default_on() -> None:
    from exp_flags import induction_scheme_goal_gate_enabled
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("INDUCTION_SCHEME_GOAL_GATE", None)
        assert induction_scheme_goal_gate_enabled() is True
    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "off"}):
        assert induction_scheme_goal_gate_enabled() is False


def main() -> int:
    tests = [v for k, v in globals().items() if k.startswith("test_") and callable(v)]
    failed = 0
    for fn in tests:
        try:
            fn()
            print(f"ok  {fn.__name__}")
        except Exception as exc:
            failed += 1
            print(f"FAIL {fn.__name__}: {exc}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
