#!/usr/bin/env python3
"""InductionScheme v1: generate / validate / dispatch / profiler replace."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

os.environ.setdefault("OPENAI_API_KEY", "unit-test-placeholder")
os.environ.setdefault("MODEL_TYPE", "gpt-4o")

from exp_flags import (
    induction_scheme_enabled,
    induction_scheme_mode,
    induction_scheme_trigger,
    should_run_induction_scheme,
)
from induction_scheme import (
    NEST,
    generate_scheme,
    scheme_formulas_for_usefulness,
)
from induction_scheme.dispatch import (
    finalize_after_attempt,
    frontier_backup_prove,
    run_scheme_round,
)
from induction_scheme.ledger import format_scheme_prompt_block, save_scheme_attempt
from induction_scheme.types import SchemeAttempt, SchemeObligation, SchemeRoundResult
from problem_profiler import (
    build_problem_profile,
    format_profile_prompt_block,
    gate_profile_for_prompt,
)

FIXTURES = ROOT / "tests" / "fixtures" / "induction_scheme"


def _load(name: str) -> str:
    return (FIXTURES / name).read_text(encoding="utf-8")


def test_flags_default_off() -> None:
    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("INDUCTION_SCHEME", None)
        os.environ.pop("INDUCTION_SCHEME_MODE", None)
        os.environ.pop("INDUCTION_SCHEME_TRIGGER", None)
        assert induction_scheme_enabled() is False
        assert induction_scheme_mode() == "structural"
        assert induction_scheme_trigger() == "after_useless"
        assert should_run_induction_scheme({}) is False

    with patch.dict(os.environ, {
        "INDUCTION_SCHEME": "on",
        "INDUCTION_SCHEME_TRIGGER": "after_useless",
    }):
        assert induction_scheme_enabled() is True
        assert should_run_induction_scheme({}) is False
        assert should_run_induction_scheme({
            "exp_attempts": [{"kind": "useless"}],
        }) is True
        assert should_run_induction_scheme({}, scheme_only=True) is True

    with patch.dict(os.environ, {
        "INDUCTION_SCHEME": "on",
        "INDUCTION_SCHEME_TRIGGER": "always",
    }):
        assert should_run_induction_scheme({}) is True


def test_generate_list_len_app() -> None:
    smt = _load("list_len_app.smt2")
    att = generate_scheme(smt, goal_name="list_len", mode="structural")
    assert not att.skipped, att.skip_reason
    assert att.induct_var == "xs"
    assert att.induct_sort == "Lst"
    assert att.validated, att.validate_errors
    kinds = {(o.kind, o.ctor) for o in att.obligations}
    assert ("base", "nil") in kinds
    assert ("step", "cons") in kinds
    step = next(o for o in att.obligations if o.kind == "step")
    assert "=>" in step.formula
    # Explicit IH appears in the step body.
    assert "_ih" in step.formula or "xs" in step.formula


def test_generate_bin_one_var() -> None:
    smt = _load("bin_plus_assoc.smt2")
    att = generate_scheme(smt, goal_name="bin", mode="structural")
    assert not att.skipped, att.skip_reason
    assert att.induct_sort == "Bin"
    assert att.induct_var in ("x", "y", "z")
    # MAX_VARS=1 → one induct var only.
    ctors = {o.ctor for o in att.obligations}
    assert "One" in ctors
    assert "ZeroAnd" in ctors or "OneAnd" in ctors
    assert att.validated, att.validate_errors


def test_generate_nat_even() -> None:
    smt = _load("nat_even.smt2")
    att = generate_scheme(smt, goal_name="nat_even", mode="structural")
    assert not att.skipped, att.skip_reason
    assert att.induct_sort == "nat"
    kinds = {(o.kind, o.ctor) for o in att.obligations}
    assert ("base", "zero") in kinds
    assert ("step", "s") in kinds


def test_generate_tree_prefers_tree_not_list_acc() -> None:
    smt = _load("tree_flatten2.smt2")
    att = generate_scheme(smt, goal_name="flatten2", mode="structural")
    assert not att.skipped, att.skip_reason
    assert att.induct_var == "p"
    assert att.induct_sort == "Tree"
    ctors = {o.ctor for o in att.obligations}
    assert "Leaf" in ctors
    assert "Node" in ctors
    # No accumulator generalization in v1.
    assert all("nil" not in (o.obl_id or "") for o in att.obligations)


def test_prefer_list_over_nat_guard() -> None:
    """Conclusion-side list beats Nat that only appears in an antecedent guard."""
    smt = """
(set-logic ALL)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-datatypes ((Lst 0)) (((nil) (cons (head Nat) (tail Lst)))))
(declare-fun even (Nat) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(assert (= (even zero) true))
(assert (forall ((n Nat)) (= (even (succ n)) (not (even n)))))
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Nat) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (xs Lst)) (= (len (cons x xs)) (succ (len xs)))))
; proof goal
(assert (not (forall ((n Nat) (xs Lst))
  (=> (even n) (= (len (append xs nil)) (len xs))))))
; proof goal end
(check-sat)
"""
    att = generate_scheme(smt, goal_name="guard", mode="structural")
    assert not att.skipped, att.skip_reason
    assert att.induct_var == "xs"
    assert att.induct_sort == "Lst"


def test_prefer_append_rec_arg_over_param_binder_order() -> None:
    """Recursive arg of append wins even if the parameter binder is listed first."""
    smt = """
(set-logic ALL)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-datatypes ((Lst 0)) (((nil) (cons (head Nat) (tail Lst)))))
(declare-fun append (Lst Lst) Lst)
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Nat) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
; proof goal — ys binder first, but append recurses on xs
(assert (not (forall ((ys Lst) (xs Lst))
  (= (append xs ys) (append xs (append ys nil))))))
; proof goal end
(check-sat)
"""
    att = generate_scheme(smt, goal_name="recpos", mode="structural")
    assert not att.skipped, att.skip_reason
    assert att.induct_var == "xs", (att.induct_var, att.induct_sort)
    assert att.induct_sort == "Lst"


def test_skip_no_adt() -> None:
    smt = _load("no_adt.smt2")
    att = generate_scheme(smt, goal_name="noadt", mode="structural")
    assert att.skipped
    assert att.obligations == []


def test_skip_heap_nonstructural() -> None:
    smt = _load("heap_skip.smt2")
    att = generate_scheme(smt, goal_name="heap", mode="structural")
    # No structural recursion evidence on Heap → do not hard-split constructors.
    assert att.skipped or att.induct_sort != "Heap"
    if att.skipped:
        assert att.obligations == []



def test_scheme_not_in_usefulness_c() -> None:
    smt = _load("list_len_app.smt2")
    att = generate_scheme(smt, goal_name="list_len", mode="structural")
    assert scheme_formulas_for_usefulness(att) == []


def test_profiler_replaces_known_induction() -> None:
    smt = _load("list_len_app.smt2")
    profile = build_problem_profile(smt, problem_id="list")
    gated = gate_profile_for_prompt(profile)
    for flag in ("on", "off"):
        with patch.dict(os.environ, {"INDUCTION_SCHEME": flag}):
            block = format_profile_prompt_block(gated)
            assert "Known induction attempts" not in block
            assert "attempt=none" not in block

    failed = {"scheme_attempts": []}
    att = generate_scheme(smt, goal_name="list_len")
    for o in att.obligations:
        o.status = "failed"
        o.prove_status = "timeout"
    failed = save_scheme_attempt(failed, att)
    with patch.dict(os.environ, {"INDUCTION_SCHEME": "on"}):
        # Nothing proved → no prompt block (avoid steering toward timeouts).
        assert format_scheme_prompt_block(failed) == ""

    for o in att.obligations:
        if o.kind == "base":
            o.status = "proved"
            o.prove_status = "unsat"
    failed = save_scheme_attempt(failed, att)
    with patch.dict(os.environ, {"INDUCTION_SCHEME": "on"}):
        diag = format_scheme_prompt_block(failed)
        assert "INDUCTION SCHEME" in diag
        assert "Proved structural" in diag
        assert "timeout" not in diag.lower() or "timeout" not in diag
        assert att.induct_var in diag


def test_scheme_prompt_includes_measure_prelude_smt() -> None:
    """When μ uses __scheme_*, the prompt shows the solver-side prelude SMT."""
    from induction_scheme.types import SchemeAttempt, SchemeObligation

    prelude = (
        "(declare-fun __scheme_nat_to_int (Nat) Int)\n"
        "(assert (= (__scheme_nat_to_int Z) 0))\n"
    )
    formula = (
        "(forall ((x Lst)) (= (__scheme_nat_to_int (len (append x nil))) "
        "(__scheme_nat_to_int (len x))))"
    )
    att = SchemeAttempt(
        goal_name="nat_len",
        induct_var="xs",
        induct_sort="Lst",
        measure_fun="len",
        measure_prelude=prelude,
        bridge_primary=True,
        validated=True,
        obligations=[
            SchemeObligation(
                obl_id="mu_hom",
                kind="measure",
                ctor="mu_hom_base",
                formula=formula,
                induct_var="xs",
                induct_sort="Lst",
                status="proved",
            ),
        ],
    )
    data = save_scheme_attempt({}, att)
    block = format_scheme_prompt_block(data, goal_name="nat_len")
    assert "Scheme measure prelude (definition in SMT axioms):" in block
    assert "(declare-fun __scheme_nat_to_int (Nat) Int)" in block
    assert formula in block


def test_scheme_prompt_flag_off_suppresses_block() -> None:
    from induction_scheme.mate_glue import scheme_prompt_suffix

    smt = _load("list_len_app.smt2")
    att = generate_scheme(smt, goal_name="list_len")
    for o in att.obligations:
        if o.kind == "base":
            o.status = "proved"
    failed = save_scheme_attempt({}, att)
    with patch.dict(os.environ, {"INDUCTION_SCHEME": "on", "INDUCTION_SCHEME_PROMPT": "on"}):
        assert "INDUCTION SCHEME" in scheme_prompt_suffix(failed)
    with patch.dict(os.environ, {"INDUCTION_SCHEME": "on", "INDUCTION_SCHEME_PROMPT": "off"}):
        assert scheme_prompt_suffix(failed) == ""


def test_dispatch_close_after_attempt_not_midway() -> None:
    """All proved → pending close only after finalize(usefulness=False)."""
    att = SchemeAttempt(
        goal_name="g",
        induct_var="xs",
        induct_sort="Lst",
        validated=True,
        obligations=[
            SchemeObligation(
                obl_id="base_nil", kind="base", ctor="nil",
                formula="(= 1 1)", induct_var="xs", induct_sort="Lst",
                validated=True, status="proved",
            ),
            SchemeObligation(
                obl_id="step_cons", kind="step", ctor="cons",
                formula="(forall ((x Nat) (xs Lst)) true)",
                induct_var="xs", induct_sort="Lst",
                validated=True, status="proved",
            ),
        ],
    )
    att.goal_gate_status = "proved"
    rr = SchemeRoundResult(attempt=att, close_parent=True)
    data: dict = {}
    # Mid-attempt usefulness still running: finalize with usefulness True → no close.
    data = finalize_after_attempt(rr, failed_data=data, usefulness_succeeded=True)
    assert "scheme_pending_close" not in data
    # After attempt ends without usefulness success → pending close.
    data = finalize_after_attempt(rr, failed_data={}, usefulness_succeeded=False)
    assert data.get("scheme_pending_close", {}).get("reason") == "short_prove"


def test_nest_vs_frontier_and_backup() -> None:
    att = SchemeAttempt(
        goal_name="g",
        induct_var="xs",
        induct_sort="Lst",
        validated=True,
        nest_budget=NEST,
        obligations=[
            SchemeObligation(
                obl_id="base_nil", kind="base", ctor="nil",
                formula="(= 1 1)", induct_var="xs", induct_sort="Lst",
                validated=True, status="proved",
            ),
            SchemeObligation(
                obl_id="step_cons", kind="step", ctor="cons",
                formula="(forall ((x Nat)) false)",
                induct_var="xs", induct_sort="Lst",
                validated=True, status="failed",
            ),
        ],
    )
    # Nest budget 0 → frontier.
    from induction_scheme.prove import mark_frontier
    mark_frontier(att, ["step_cons"])
    assert "step_cons" in att.frontier_ids
    assert att.obligations[1].no_nest

    # Backup without success child → no-op.
    assert frontier_backup_prove(
        att,
        smt_content="(set-logic ALL)\n; proof goal\n(assert (not true))\n; proof goal end\n",
        work_dir=Path(tempfile.mkdtemp()),
        goal_name="g",
        had_success_child=False,
        prove_fn=lambda *a, **k: MagicMock(proved=True, status="unsat", elapsed=0.1),
    ) is False
    assert att.backup_ran is False

    # With success child + mock unsat → close.
    att.obligations[1].status = "frontier"
    att.goal_gate_status = "proved"
    closed = frontier_backup_prove(
        att,
        smt_content=(
            "(set-logic ALL)\n; proof goal\n(assert (not true))\n"
            "; proof goal end\n(check-sat)\n"
        ),
        work_dir=Path(tempfile.mkdtemp()),
        goal_name="g",
        had_success_child=True,
        prove_fn=lambda *a, **k: MagicMock(proved=True, status="unsat", elapsed=0.1),
    )
    assert closed is True
    assert att.close_reason == "frontier"
    assert att.backup_ran is True


def test_nest_dispatch_when_budget_allows() -> None:
    smt = _load("list_len_app.smt2")

    def _mock_prove(path, timeout, profiles):
        # Gate must pass first; then fail obligations so nest is considered.
        if "goal_gate" in str(path):
            return MagicMock(proved=True, status="unsat", elapsed=0.05)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    with patch.dict(
        os.environ,
        {"INDUCTION_SCHEME_GOAL_GATE": "on", "INDUCTION_SCHEME_NEST": "on"},
    ):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="list_len",
                work_dir=Path(tmp),
                mode="structural",
                depth=0,
                nest_budget=1,
                max_depth=3,
                prove_fn=_mock_prove,
                do_prove=True,
            )
    assert rr.attempt.validated
    assert rr.attempt.goal_gate_status == "proved"
    assert rr.close_parent is False
    assert rr.nest_children, "expected nest children when budget allows"
    assert all(c.skip_initial for c in rr.nest_children)


def test_mid_depth_can_still_nest_for_next_var() -> None:
    """depth=1 with max_depth=3 may nest again (xs→ys→zs chain)."""
    smt = _load("list_len_app.smt2")

    def _mock_prove(path, timeout, profiles):
        if "goal_gate" in str(path):
            return MagicMock(proved=True, status="unsat", elapsed=0.05)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    with patch.dict(
        os.environ,
        {"INDUCTION_SCHEME_GOAL_GATE": "on", "INDUCTION_SCHEME_NEST": "on"},
    ):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="list_len",
                work_dir=Path(tmp),
                mode="structural",
                depth=1,
                nest_budget=1,  # soft enable; must not be a one-hop fuse
                max_depth=3,
                prove_fn=_mock_prove,
                do_prove=True,
            )
    assert rr.nest_children, "mid-depth node should still nest while depth remains"
    data = finalize_after_attempt(
        rr, failed_data={}, usefulness_succeeded=False,
    )
    dispatch = data.get("scheme_dispatch") or {}
    assert dispatch.get("action") == "nest"
    # Child keeps nest enabled; further stop is depth=2 → cannot nest to 3.
    assert dispatch.get("nest_budget") == 1


def test_depth_cap_marks_frontier() -> None:
    smt = _load("list_len_app.smt2")

    def _mock_prove(path, timeout, profiles):
        if "goal_gate" in str(path):
            return MagicMock(proved=True, status="unsat", elapsed=0.05)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    with tempfile.TemporaryDirectory() as tmp:
        rr = run_scheme_round(
            smt_content=smt,
            goal_name="list_len",
            work_dir=Path(tmp),
            depth=2,
            nest_budget=1,
            max_depth=3,  # depth+1 == max → cannot nest
            prove_fn=_mock_prove,
            do_prove=True,
        )
    assert not rr.nest_children
    assert rr.attempt.frontier_ids


def test_measure_len_append_emits_r1_on_append() -> None:
    """append : Lst×Lst→Lst is a μ-domain helper → R1 bases/step (no filter descent)."""
    smt = _load("measure_len_append.smt2")
    att = generate_scheme(smt, goal_name="len_app", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "len"
    ctors = {o.ctor for o in att.obligations}
    assert "mu_hom_base" in ctors
    assert "mu_hom_step" in ctors
    assert "wf" not in ctors
    assert not any(c.startswith("semantic_") for c in ctors)


def test_structural_still_preferred_in_both_on_len_append() -> None:
    smt = _load("measure_len_append.smt2")
    att = generate_scheme(smt, goal_name="len_app", mode="both")
    assert not att.skipped
    assert att.validated
    assert all(o.kind in ("base", "step") for o in att.obligations)
    assert not att.measure_fun


def test_measure_bubsort_picks_size() -> None:
    smt = _load("measure_bubsort_len.smt2")
    att_m = generate_scheme(smt, goal_name="bub", mode="measure")
    assert not att_m.skipped, att_m.skip_reason
    assert att_m.measure_fun == "size"
    assert att_m.induct_var == "x"
    assert att_m.bridge_primary
    ctors = {o.ctor for o in att_m.obligations}
    assert "nonneg" in ctors
    assert "wf" not in ctors
    assert any("bubble" in c for c in ctors)
    assert not any(c.startswith("semantic_") for c in ctors)

    att_s = generate_scheme(smt, goal_name="bub", mode="structural")
    # Structural still available via isort/insert2 on x.
    assert not att_s.skipped
    assert any(o.kind == "step" for o in att_s.obligations)


def test_measure_qsort_partition() -> None:
    smt = _load("measure_qsort_partition.smt2")
    att = generate_scheme(smt, goal_name="qsort", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.validated, att.validate_errors
    assert att.measure_fun == "size"
    assert att.induct_var == "xs"
    assert att.bridge_primary
    ctors = {o.ctor for o in att.obligations}
    assert "wf" not in ctors
    assert any("filter" in c for c in ctors)
    filt = next(o for o in att.obligations if "filter" in o.ctor)
    assert "(<= (size (filter" in filt.formula or "(<= (size (filterlt" in filt.formula


def test_both_runs_all_viable_axes() -> None:
    """both: soft/hard-nonblock axes all short-prove; nest unions unproved."""
    smt = _load("measure_bubsort_len.smt2")

    def prove_fn(path, timeout, profiles):
        # Everything "proves" so we can inspect merged ledger.
        return MagicMock(proved=True, status="unsat", elapsed=0.05)

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "on"}):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="bub",
                work_dir=Path(tmp),
                mode="both",
                prove_fn=prove_fn,
                do_prove=True,
                nest_budget=0,
                max_depth=3,
            )
    # Structural is ledger primary; measure obligations folded in.
    assert any(o.kind in ("base", "step") for o in rr.attempt.obligations)
    assert any("bubble" in o.ctor or o.kind == "measure" for o in rr.attempt.obligations)
    assert rr.side_attempts, "measure axis should be retained as side"
    assert rr.attempt.measure_fun == "size"


def test_both_struct_hard_fail_still_runs_measure() -> None:
    smt = _load("measure_bubsort_len.smt2")

    def prove_fn(path, timeout, profiles):
        name = str(path)
        if "struct" in name and "goal_gate" in name:
            return MagicMock(proved=False, status="sat", elapsed=0.1)
        return MagicMock(proved=True, status="unsat", elapsed=0.05)

    with patch.dict(os.environ, {"INDUCTION_SCHEME_GOAL_GATE": "on"}):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="bub",
                work_dir=Path(tmp),
                mode="both",
                prove_fn=prove_fn,
                do_prove=True,
                nest_budget=0,
                max_depth=3,
            )
    assert rr.attempt.measure_fun == "size"
    assert rr.attempt.bridge_primary
    assert any("bubble" in o.ctor for o in rr.attempt.obligations)


def test_both_rc_orders_measure_first() -> None:
    from induction_scheme.generate import generate_scheme_candidates

    smt = _load("measure_bubsort_len.smt2")
    cands = generate_scheme_candidates(smt, goal_name="bub", mode="both")
    assert len(cands) >= 2
    assert cands[0].measure_fun == "size"
    assert cands[0].bridge_primary
    assert all(o.kind == "measure" for o in cands[0].obligations)
    assert any(o.kind in ("base", "step") for o in cands[1].obligations)


def test_measure_rejects_ssort_minimum_name() -> None:
    """Int-typed min/max helpers must not be chosen as μ."""
    from induction_scheme.generate import select_measure_fun
    from problem_profiler import build_problem_profile

    smt = Path("benchmarks/preprocessed/autoproof/standard/sort_SSortIsSort/template.smt2").read_text()
    prof = build_problem_profile(smt, problem_id="ssort")
    mu = select_measure_fun(prof, "list")
    assert mu != "ssort_minimum"


def test_synthesize_list_len_on_real_qsort() -> None:
    """No length in SMT → internal __scheme_list_len + filter descent."""
    path = Path("benchmarks/preprocessed/autoproof/standard/sort_QSortIsSort/template.smt2")
    if not path.exists():
        return
    smt = path.read_text(encoding="utf-8")
    att = generate_scheme(smt, goal_name="qsort", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "__scheme_list_len"
    assert "__scheme_list_len" in att.measure_prelude
    assert att.bridge_primary
    assert any("filter" in o.ctor for o in att.obligations)


def test_synthesize_adt_size_binary_tree_not_list_len() -> None:
    """Trees must not be misread as lists; size sums both recursive children."""
    from induction_scheme.bridges import _list_nil_cons, pick_or_synthesize_measure
    from problem_profiler import build_problem_profile

    smt = """
(set-logic UFDT)
(declare-datatypes ((T 0)) (((leaf) (node (l T) (r T)))))
(declare-fun mirror (T) T)
(assert (forall ((x T)) (= (mirror (mirror x)) x)))
(assert (not (forall ((x T)) (= (mirror (mirror x)) x))))
(check-sat)
"""
    prof = build_problem_profile(smt, problem_id="tree")
    assert _list_nil_cons(prof, "T") is None
    mu, ret, prelude = pick_or_synthesize_measure(prof, "T")
    assert mu == "__scheme_adt_size"
    assert ret == "Int"
    assert "(__scheme_adt_size __a0)" in prelude and "(__scheme_adt_size __a1)" in prelude
    assert "(+ 1 (__scheme_adt_size __a0)" in prelude


def test_scheme_measure_prelude_upgrades_ufdt_logic() -> None:
    """Short-prove working copy must not leave Int μ under bare UFDT."""
    from induction_scheme.prove import _smt_with_measure_prelude
    from induction_scheme.types import SchemeAttempt

    smt = "(set-logic UFDT)\n; proof goal\n(assert (not true))\n; proof goal end\n"
    prelude = "(declare-fun __scheme_list_len (list) Int)\n"
    att = SchemeAttempt(goal_name="g", measure_prelude=prelude)
    out = _smt_with_measure_prelude(smt, att)
    assert "(set-logic UFDTLIA)" in out
    assert "(declare-fun __scheme_list_len (list) Int)" in out
    assert out.index("(set-logic UFDTLIA)") < out.index("__scheme_list_len")


def test_synthesize_list_len_snoc_recursive_first() -> None:
    """Snoc with recursive first arg is still a single-spine list."""
    from induction_scheme.bridges import _list_nil_cons, pick_or_synthesize_measure
    from problem_profiler import build_problem_profile

    smt = """
(set-logic UFDT)
(declare-datatypes ((MySeq 0)) (((empty) (snoc (front MySeq) (x Int)))))
(assert (not (forall ((s MySeq)) (= s s))))
(check-sat)
"""
    prof = build_problem_profile(smt, problem_id="snoc")
    pair = _list_nil_cons(prof, "MySeq")
    assert pair is not None
    assert pair[0] == "empty" and pair[1] == "snoc"
    mu, _, prelude = pick_or_synthesize_measure(prof, "MySeq")
    assert mu == "__scheme_list_len"
    assert "(+ 1 (__scheme_list_len __a0))" in prelude


def test_descent_name_covers_remove_prefix() -> None:
    from induction_scheme.bridges import _is_descent_name

    assert _is_descent_name("filter")
    assert _is_descent_name("filter_gt")
    assert _is_descent_name("remove1")
    assert _is_descent_name("butlast")
    assert not _is_descent_name("append")
    assert not _is_descent_name("qsort")


def test_qsort_emits_descent_not_isort_templates() -> None:
    path = Path("benchmarks/preprocessed/autoproof/standard/sort_QSortIsSort/template.smt2")
    if not path.exists():
        return
    att = generate_scheme(path.read_text(encoding="utf-8"), goal_name="qsort", mode="measure")
    assert not att.skipped, att.skip_reason
    ctors = {o.ctor for o in att.obligations}
    assert any("descent_filter" in c for c in ctors)
    assert not any(c.startswith("semantic_") for c in ctors)


def test_heap_r1_r2_bridges_goal10_12_13() -> None:
    from induction_scheme.generate import generate_scheme as gen

    base = Path("benchmarks/preprocessed/dtt/dtt-leon")
    for name in ("heap-goal10", "heap-goal12", "heap-goal13"):
        smt = (base / name / "template.smt2").read_text(encoding="utf-8")
        att = gen(smt, goal_name=name, mode="measure")
        assert not att.skipped, f"{name}: {att.skip_reason}"
        assert att.validated, f"{name}: {att.validate_errors}"
        assert att.measure_fun == "hsize"
        assert att.bridge_primary
        ctors = {o.ctor for o in att.obligations}
        assert "mu_hom_base" in ctors, f"{name}: {ctors}"
        assert "mu_hom_step" in ctors, f"{name}: {ctors}"
        assert "mu_lt" in ctors, f"{name}: {ctors}"
        # Predicate preserve only when a Bool guard on μ-sort appears in the goal.
        from induction_scheme.bridges import _goal_symbols, _mu_guard_preds
        from problem_profiler import build_problem_profile
        prof = build_problem_profile(smt)
        if _mu_guard_preds(prof, "Heap"):
            assert "mu_prop_preserve" in ctors, f"{name}: {ctors}"
        # No benchmark-named semantic templates.
        assert not any(c.startswith("heap_") for c in ctors), ctors
        assert not any(c.startswith("semantic_") for c in ctors), ctors


def test_measure_obligations_do_not_nest() -> None:
    """Unproved measure bridges are frontier; structural may still nest."""
    smt = _load("measure_qsort_partition.smt2")

    def _mock_prove(path, timeout, profiles):
        if "goal_gate" in str(path):
            return MagicMock(proved=True, status="unsat", elapsed=0.05)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    with patch.dict(
        os.environ,
        {"INDUCTION_SCHEME_GOAL_GATE": "on", "INDUCTION_SCHEME_NEST": "on"},
    ):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="qsort",
                work_dir=Path(tmp),
                mode="both",
                depth=0,
                nest_budget=1,
                max_depth=3,
                prove_fn=_mock_prove,
                do_prove=True,
            )
    assert rr.nest_children, "structural base/step should nest"
    assert all(c.kind in ("base", "step") for c in rr.nest_children)
    meas = [o for o in rr.attempt.obligations if o.kind == "measure"]
    assert meas, "measure axis should be folded into ledger"
    assert all(
        o.status in ("frontier", "proved", "invalid") or o.no_nest
        for o in meas
        if o.status != "proved"
    )


def test_cross_sort_blocks_same_sort_nest() -> None:
    """Default cross_sort: Bin→Bin (and Lst→Lst) obligations stay frontier."""
    from exp_flags import induction_scheme_nest_policy

    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("INDUCTION_SCHEME_NEST", None)
        assert induction_scheme_nest_policy() == "cross_sort"

    smt = _load("bin_plus_assoc.smt2")

    def _mock_prove(path, timeout, profiles):
        if "goal_gate" in str(path):
            return MagicMock(proved=True, status="unsat", elapsed=0.05)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    with patch.dict(
        os.environ,
        {"INDUCTION_SCHEME_GOAL_GATE": "on", "INDUCTION_SCHEME_NEST": "cross_sort"},
    ):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="bin_plus",
                work_dir=Path(tmp),
                mode="structural",
                depth=0,
                nest_budget=1,
                max_depth=3,
                prove_fn=_mock_prove,
                do_prove=True,
            )
    assert rr.attempt.induct_sort == "Bin"
    assert not rr.nest_children, "same-sort Bin nest must be blocked"
    failed = [
        o for o in rr.attempt.obligations
        if o.status not in ("proved", "invalid")
    ]
    assert failed
    assert all(o.status == "frontier" or o.no_nest for o in failed)


def test_cross_sort_allows_queue_to_lst() -> None:
    """cross_sort keeps amortize Queue→Lst structural nest."""
    from induction_scheme.generate import peek_structural_induct_sort

    smt_path = (
        ROOT / "benchmarks" / "preprocessed" / "dtt" / "dtt-leon"
        / "amortize-queue-goal7" / "template.smt2"
    )
    smt = smt_path.read_text(encoding="utf-8")

    def _mock_prove(path, timeout, profiles):
        if "goal_gate" in str(path):
            return MagicMock(proved=True, status="unsat", elapsed=0.05)
        return MagicMock(proved=False, status="timeout", elapsed=1.0)

    with patch.dict(
        os.environ,
        {"INDUCTION_SCHEME_GOAL_GATE": "on", "INDUCTION_SCHEME_NEST": "cross_sort"},
    ):
        with tempfile.TemporaryDirectory() as tmp:
            rr = run_scheme_round(
                smt_content=smt,
                goal_name="amortize-queue-goal7",
                work_dir=Path(tmp),
                mode="structural",
                depth=0,
                nest_budget=1,
                max_depth=3,
                prove_fn=_mock_prove,
                do_prove=True,
            )
    assert rr.attempt.induct_sort == "Queue"
    assert rr.nest_children, "Queue→Lst nest must remain"
    for c in rr.nest_children:
        child_sort = peek_structural_induct_sort(
            smt, c.formula or "", goal_name=c.obl_id,
        )
        assert child_sort == "Lst"


def test_library_prompt_filters_current_scheme_only() -> None:
    """Prompt library hides α-dup of current scheme block; keeps other pins."""
    from induction_scheme.ledger import (
        filter_library_excluding_current_scheme,
        save_scheme_attempt,
    )
    from induction_scheme.mate_glue import library_for_prompt
    from smt_patterns import normalize_lemma_formula

    smt = _load("measure_len_append.smt2")
    att = generate_scheme(smt, goal_name="len_app", mode="measure")
    assert not att.skipped
    for o in att.obligations:
        if o.ctor != "nonneg":
            o.status = "proved"
    data = save_scheme_attempt({}, att)
    scheme_forms = [
        normalize_lemma_formula(o.formula)
        for o in att.obligations
        if o.status == "proved" and o.ctor != "nonneg"
    ]
    assert scheme_forms
    other = "(forall ((z Lst)) (= z z))"
    library = [
        {"id": "lib_1", "formula": att.obligations[1].formula, "origin": "scheme:len_app:x"},
        {"id": "lib_2", "formula": other, "origin": "scheme:ancestor:y"},
        {"id": "lib_3", "formula": other.replace("z", "w"), "origin": "llm"},  # α of other? maybe not
    ]
    # Use a clearly distinct ancestor pin
    library[1] = {
        "id": "lib_2",
        "formula": "(forall ((n Nat)) (= n n))",
        "origin": "scheme:other_goal:m1",
    }
    with patch.dict(os.environ, {"INDUCTION_SCHEME": "on", "INDUCTION_SCHEME_PROMPT": "on"}):
        filtered = library_for_prompt(library, data, goal_name="len_app")
    ids = {item["id"] for item in filtered}
    assert "lib_1" not in ids
    assert "lib_2" in ids
    # nonneg not in scheme prompt block → if only in library, would stay;
    # filtering is by scheme prompt formulas only.


def test_harvest_scheme_proved_stores_measure_prelude() -> None:
    """Scheme pins that use __scheme_* must carry measure_prelude into the library."""
    from induction_scheme.ledger import harvest_scheme_proved_to_library
    from obligation_tree import inject_library_axioms, load_lemma_library

    prelude = (
        "(declare-fun __scheme_nat_to_int (Nat) Int)\n"
        "(assert (= (__scheme_nat_to_int zero) 0))\n"
    )
    formula = "(forall ((x Lst)) (>= (__scheme_nat_to_int (len x)) 0))"
    plain = "(forall ((n Nat)) (= n n))"
    att = SchemeAttempt(
        goal_name="template",
        induct_var="xs",
        induct_sort="Lst",
        validated=True,
        measure_prelude=prelude,
        obligations=[
            SchemeObligation(
                obl_id="measure_nonneg",
                kind="measure",
                ctor="nonneg",
                formula=formula,
                induct_var="xs",
                induct_sort="Lst",
                status="proved",
            ),
            SchemeObligation(
                obl_id="base_nil",
                kind="base",
                ctor="nil",
                formula=plain,
                induct_var="xs",
                induct_sort="Lst",
                status="proved",
            ),
            SchemeObligation(
                obl_id="wf",
                kind="measure",
                ctor="wf",
                formula="(=> true true)",
                induct_var="xs",
                induct_sort="Lst",
                status="proved",
            ),
        ],
    )
    smt = """(set-logic ALL)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
; proof goal
(assert (not true))
; proof goal end
"""
    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"LEMMA_LIBRARY": "on"}):
            n = harvest_scheme_proved_to_library(att, tmp, depth=1)
            assert n == 2  # nonneg + base; wf skipped
            items = load_lemma_library(tmp)
            by_f = {i["formula"]: i for i in items}
            assert formula in by_f
            assert by_f[formula].get("prelude", "").strip().startswith(
                "(declare-fun __scheme_nat_to_int"
            )
            assert plain in by_f
            assert not str(by_f[plain].get("prelude") or "").strip()
            out = inject_library_axioms(smt, items)
            assert "(declare-fun __scheme_nat_to_int (Nat) Int)" in out
            assert formula in out or "(__scheme_nat_to_int (len x))" in out


def test_scheme_sat_marks_invalid_and_harvests() -> None:
    """Short-prove sat ⇒ obligation invalid ⇒ written to invalid_lemmas."""
    from induction_scheme.ledger import harvest_scheme_refuted_to_invalid
    from induction_scheme.prove import prove_obligations
    import Mate_new as mate

    att = SchemeAttempt(
        goal_name="template",
        induct_var="xs",
        induct_sort="Lst",
        validated=True,
        obligations=[
            SchemeObligation(
                obl_id="m1",
                kind="measure",
                ctor="bogus",
                formula="(= 0 1)",
                induct_var="xs",
                induct_sort="Lst",
            ),
            SchemeObligation(
                obl_id="m2",
                kind="measure",
                ctor="ok",
                formula="(= 1 1)",
                induct_var="xs",
                induct_sort="Lst",
            ),
        ],
    )

    def prove_fn(path, timeout, profiles):
        name = str(path)
        if "m1" in name:
            return MagicMock(proved=False, status="sat", elapsed=0.01)
        return MagicMock(proved=True, status="unsat", elapsed=0.01)

    with tempfile.TemporaryDirectory() as tmp:
        prove_obligations(
            att,
            smt_content=(
                "(set-logic ALL)\n; proof goal\n(assert true)\n"
                "; proof goal end\n(check-sat)\n"
            ),
            work_dir=Path(tmp),
            goal_name="template",
            prove_fn=prove_fn,
        )
        by_id = {o.obl_id: o for o in att.obligations}
        assert by_id["m1"].status == "invalid"
        assert by_id["m1"].prove_status == "sat"
        assert by_id["m2"].status == "proved"

        n = harvest_scheme_refuted_to_invalid(att, tmp, goal_name="template")
        assert n == 1
        inv = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert len(inv) == 1
        assert inv[0]["lemma"] == "(= 0 1)"
        assert inv[0]["reason"].startswith("scheme_refuted:")

        # Dedup: second harvest does not grow the store.
        harvest_scheme_refuted_to_invalid(att, tmp, goal_name="template")
        inv2 = mate.load_failed_lemmas(tmp, "template")["invalid_lemmas"]
        assert len(inv2) == 1


def main() -> int:
    tests = [
        test_flags_default_off,
        test_generate_list_len_app,
        test_generate_bin_one_var,
        test_generate_nat_even,
        test_generate_tree_prefers_tree_not_list_acc,
        test_prefer_list_over_nat_guard,
        test_prefer_append_rec_arg_over_param_binder_order,
        test_skip_no_adt,
        test_skip_heap_nonstructural,
        test_scheme_not_in_usefulness_c,
        test_profiler_replaces_known_induction,
        test_scheme_prompt_flag_off_suppresses_block,
        test_scheme_prompt_includes_measure_prelude_smt,
        test_dispatch_close_after_attempt_not_midway,
        test_nest_vs_frontier_and_backup,
        test_nest_dispatch_when_budget_allows,
        test_mid_depth_can_still_nest_for_next_var,
        test_depth_cap_marks_frontier,
        test_measure_len_append_emits_r1_on_append,
        test_structural_still_preferred_in_both_on_len_append,
        test_measure_bubsort_picks_size,
        test_measure_qsort_partition,
        test_both_runs_all_viable_axes,
        test_both_struct_hard_fail_still_runs_measure,
        test_both_rc_orders_measure_first,
        test_measure_rejects_ssort_minimum_name,
        test_synthesize_list_len_on_real_qsort,
        test_synthesize_adt_size_binary_tree_not_list_len,
        test_scheme_measure_prelude_upgrades_ufdt_logic,
        test_synthesize_list_len_snoc_recursive_first,
        test_descent_name_covers_remove_prefix,
        test_qsort_emits_descent_not_isort_templates,
        test_heap_r1_r2_bridges_goal10_12_13,
        test_measure_obligations_do_not_nest,
        test_cross_sort_blocks_same_sort_nest,
        test_cross_sort_allows_queue_to_lst,
        test_library_prompt_filters_current_scheme_only,
        test_harvest_scheme_proved_stores_measure_prelude,
        test_scheme_sat_marks_invalid_and_harvests,
    ]
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
