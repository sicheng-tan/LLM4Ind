"""Minimal regression suite for scheme prelude + extensibility.

Maps to the local checklist (A prelude pollution / B list_len·nat→int·descent·
cross_sort·μ-name). Prefer fixtures; real benchmarks are skipped if absent so
CI stays offline-friendly. Run::

    pytest tests/test_scheme_mini_suite.py tests/test_induction_scheme.py \\
           tests/test_obligation_tree.py -k 'prelude or scheme or list_len or cross_sort or ssort' -q
"""

from __future__ import annotations

import os
import tempfile
from pathlib import Path
from unittest.mock import patch

import pytest

from induction_scheme.bridges import _is_descent_name, _list_nil_cons, pick_or_synthesize_measure
from induction_scheme.generate import generate_scheme, select_measure_fun
from induction_scheme.ledger import harvest_scheme_proved_to_library
from induction_scheme.types import SchemeAttempt, SchemeObligation
from obligation_tree import inject_library_axioms, load_lemma_library, scheme_helpers_in_text
from problem_profiler import build_problem_profile

_FIX = Path(__file__).resolve().parent / "fixtures" / "induction_scheme"
_BENCH = Path(__file__).resolve().parents[1] / "benchmarks" / "preprocessed"


def _load_fix(name: str) -> str:
    return (_FIX / name).read_text(encoding="utf-8")


def _bench(*parts: str) -> Path:
    return _BENCH.joinpath(*parts) / "template.smt2"


def _require_bench(*parts: str) -> Path:
    path = _bench(*parts)
    if not path.exists():
        pytest.skip(f"missing benchmark {path}")
    return path


def _mark_measure_proved(att: SchemeAttempt) -> None:
    for obl in att.obligations:
        if obl.ctor == "wf":
            continue
        obl.status = "proved"


# ---------------------------------------------------------------------------
# A. Prelude pollution regression
# ---------------------------------------------------------------------------


def test_A_fixture_nat_len_harvest_injects_prelude() -> None:
    """measure_nat_len: Nat μ → harvest pins carry prelude → inject declares helper."""
    smt = _load_fix("measure_nat_len.smt2")
    att = generate_scheme(smt, goal_name="nat_len", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "len"
    assert "__scheme_nat_to_int" in att.measure_prelude
    assert any("__scheme_nat_to_int" in o.formula for o in att.obligations)
    _mark_measure_proved(att)

    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"LEMMA_LIBRARY": "on"}):
            n = harvest_scheme_proved_to_library(att, tmp, depth=0)
            assert n >= 1
            items = load_lemma_library(tmp)
            helper_rows = [
                i for i in items
                if "__scheme_nat_to_int" in str(i.get("formula") or "")
            ]
            assert helper_rows
            assert all(
                "(declare-fun __scheme_nat_to_int" in str(i.get("prelude") or "")
                for i in helper_rows
            )
            plain_rows = [
                i for i in items
                if "__scheme_" not in str(i.get("formula") or "")
            ]
            assert all(not str(i.get("prelude") or "").strip() for i in plain_rows)

            out = inject_library_axioms(smt, items)
            assert "(declare-fun __scheme_nat_to_int" in out
            # Unrelated / plain content must not be the only mention of the helper.
            assert scheme_helpers_in_text(
                "(forall ((n Nat)) (= n n))"
            ) == []


def test_A_inject_skips_polluted_pin_keeps_unrelated_clean() -> None:
    """Old bug shape: pin with __scheme_* but no prelude must not poison siblings."""
    smt = _load_fix("measure_nat_len.smt2")
    polluted = {
        "id": "lib_bad",
        "formula": "(forall ((xs Lst)) (>= (__scheme_nat_to_int (len xs)) 0))",
    }
    unrelated = {
        "id": "lib_ok",
        "formula": "(forall ((n Nat)) (= n n))",
    }
    out = inject_library_axioms(smt, [polluted, unrelated])
    assert "; lib_bad" not in out
    assert "; lib_ok" in out
    assert "(declare-fun __scheme_nat_to_int" not in out
    assert "(forall ((n Nat)) (= n n))" in out


def test_A_heap_goal1_nat_hsize_prelude_roundtrip() -> None:
    path = _require_bench("vmcai15-dt", "leon", "heap-goal1")
    smt = path.read_text(encoding="utf-8")
    att = generate_scheme(smt, goal_name="heap-goal1", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "hsize"
    assert "__scheme_nat_to_int" in att.measure_prelude
    _mark_measure_proved(att)
    with tempfile.TemporaryDirectory() as tmp:
        with patch.dict(os.environ, {"LEMMA_LIBRARY": "on"}):
            harvest_scheme_proved_to_library(att, tmp, depth=0)
            out = inject_library_axioms(smt, load_lemma_library(tmp))
    assert "(declare-fun __scheme_nat_to_int" in out
    assert out.count("(declare-fun __scheme_nat_to_int") == 1


def test_A_nmsort_uses_real_length_not_list_len_synth() -> None:
    path = _require_bench("autoproof", "standard", "sort_NMSortTDIsSort")
    smt = path.read_text(encoding="utf-8")
    att = generate_scheme(smt, goal_name="nmsort", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun in ("length", "len")
    assert att.measure_fun != "__scheme_list_len"
    assert "__scheme_nat_to_int" in att.measure_prelude
    assert "__scheme_list_len" not in att.measure_prelude


# ---------------------------------------------------------------------------
# B1 / B2. list_len vs nat→int vs Int μ
# ---------------------------------------------------------------------------


def test_B1_qsort_synthesizes_list_len() -> None:
    path = _require_bench("autoproof", "standard", "sort_QSortIsSort")
    att = generate_scheme(path.read_text(encoding="utf-8"), goal_name="qsort", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "__scheme_list_len"
    assert any("filter" in o.ctor for o in att.obligations)


def test_B1_bubsort_count_list_len_and_bubble_descent() -> None:
    path = _require_bench("autoproof", "standard", "sort_BubSortCount")
    att = generate_scheme(path.read_text(encoding="utf-8"), goal_name="bub", mode="measure")
    assert not att.skipped, att.skip_reason
    # Prefer real size-like ``count`` when present; else synthesized list_len.
    assert att.measure_fun in ("count", "__scheme_list_len", "size", "length", "len")
    assert any("bubble" in o.ctor for o in att.obligations)


def test_B1_fixture_bubsort_int_size_no_nat_to_int() -> None:
    """Int-valued size must not insert __scheme_nat_to_int (B2 negative)."""
    att = generate_scheme(_load_fix("measure_bubsort_len.smt2"), goal_name="bub", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "size"
    assert not (att.measure_prelude or "").strip()
    assert "__scheme_nat_to_int" not in "".join(o.formula for o in att.obligations)


def test_B1_nil_cons_rename_still_list_spine() -> None:
    smt = """
(set-logic UFDT)
(declare-datatypes ((Seq 0)) (((Nil) (Cons (hd Int) (tl Seq)))))
(assert (not (forall ((s Seq)) (= s s))))
(check-sat)
"""
    prof = build_problem_profile(smt, problem_id="nil_cons")
    assert _list_nil_cons(prof, "Seq") is not None
    mu, _, prelude = pick_or_synthesize_measure(prof, "Seq")
    assert mu == "__scheme_list_len"
    assert "__scheme_list_len" in prelude


def test_B1_int_len_fixture_no_synth_list_len() -> None:
    """Existing Int len (measure_len_append) must prefer real μ, not synth."""
    att = generate_scheme(_load_fix("measure_len_append.smt2"), goal_name="len_app", mode="measure")
    assert not att.skipped, att.skip_reason
    assert att.measure_fun == "len"
    assert att.measure_fun != "__scheme_list_len"
    assert not (att.measure_prelude or "").strip()


# ---------------------------------------------------------------------------
# B3. Descent name heuristics
# ---------------------------------------------------------------------------


def test_B3_descent_prefixes_and_blocklist() -> None:
    """Name table remains available as fallback; blocklist still excludes growers."""
    assert _is_descent_name("filter")
    assert _is_descent_name("filterlt")
    assert _is_descent_name("filter_my")
    assert not _is_descent_name("my_filter")  # infix — needs RC/signature peer path
    assert _is_descent_name("remove1")
    assert _is_descent_name("butlast")
    assert not _is_descent_name("append")
    assert not _is_descent_name("qsort")
    assert not _is_descent_name("merge")


def test_B3_signature_descent_for_renamed_filter() -> None:
    """Same-sort transformer peer needs no filter* name (RC/signature path)."""
    from induction_scheme.bridges import _descent_for_peer, _is_descent_name

    assert not _is_descent_name("my_filter")
    smt = """
(set-logic ALL)
(declare-datatypes ((list 0)) (((nil) (cons (head Int) (tail list)))))
(declare-fun my_filter (Int list) list)
(declare-fun size (list) Int)
(assert (= (size nil) 0))
(assert (not false))
(check-sat)
"""
    prof = build_problem_profile(smt)
    fun_sorts = dict(prof.signature.get("fun_sorts") or {})
    fun_sorts["my_filter"] = {"input_sorts": ["Int", "list"], "return_sort": "list"}
    obls = _descent_for_peer(
        prof,
        peer="my_filter",
        induct_var="xs",
        induct_sort="list",
        measure_fun="size",
        use_nat_to_int=False,
        fun_sorts=fun_sorts,
    )
    assert any("my_filter" in o.ctor for o in obls), [o.ctor for o in obls]
    assert all("append" not in o.ctor for o in obls)


def test_B2_defn_shape_prefers_card_over_name() -> None:
    """Size-shaped ``card`` beats a non-size unary Int fun without size name."""
    smt = """
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-fun card (Lst) Int)
(declare-fun junk (Lst) Int)
(assert (= (card nil) 0))
(assert (forall ((x Int) (xs Lst)) (= (card (cons x xs)) (+ 1 (card xs)))))
(assert (= (junk nil) 0))
(assert (forall ((x Int) (xs Lst)) (= (junk (cons x xs)) (junk xs))))
(assert (not (forall ((xs Lst)) (>= (card xs) 0))))
(check-sat)
"""
    assert select_measure_fun(build_problem_profile(smt), "Lst") == "card"


def test_B3_product_unwrap_without_pair_name() -> None:
    """τ→σ with selector σ→τ yields descent (not only symbols named Pair/bubble)."""
    from induction_scheme.bridges import _descent_for_peer, _selectors_to_sort

    smt = """
(set-logic ALL)
(declare-datatypes ((list 0) (Wrap 0)) (
  ((nil) (cons (head Int) (tail list)))
  ((mk (flag Bool) (payload list)))
))
(declare-fun step (list) Wrap)
(declare-fun size (list) Int)
(assert (= (size nil) 0))
(assert (not false))
(check-sat)
"""
    prof = build_problem_profile(smt)
    assert "payload" in _selectors_to_sort(prof, "Wrap", "list")
    fun_sorts = dict(prof.signature.get("fun_sorts") or {})
    fun_sorts.setdefault("step", {"input_sorts": ["list"], "return_sort": "Wrap"})
    obls = _descent_for_peer(
        prof,
        peer="step",
        induct_var="xs",
        induct_sort="list",
        measure_fun="size",
        use_nat_to_int=False,
        fun_sorts=fun_sorts,
    )
    assert any("payload" in o.ctor for o in obls), [o.ctor for o in obls]


def test_B3_qsort_fixture_filter_not_isort_templates() -> None:
    att = generate_scheme(_load_fix("measure_qsort_partition.smt2"), goal_name="qsort", mode="measure")
    assert not att.skipped, att.skip_reason
    ctors = {o.ctor for o in att.obligations}
    assert any("filter" in c for c in ctors)
    assert not any(c.startswith("semantic_") for c in ctors)


# ---------------------------------------------------------------------------
# B4 / B5. Bin shape + μ-name rejection
# (cross_sort nest: see test_cross_sort_* in test_induction_scheme.py)
# ---------------------------------------------------------------------------


def test_B5_ssort_rejects_minimum_as_measure() -> None:
    path = _require_bench("autoproof", "standard", "sort_SSortIsSort")
    prof = build_problem_profile(path.read_text(encoding="utf-8"), problem_id="ssort")
    sorts = list(prof.signature.get("datatypes") or [])
    list_sorts = [s for s in sorts if "list" in s.lower() or s in ("list", "Lst", "lst")]
    assert list_sorts or sorts
    target = list_sorts[0] if list_sorts else sorts[0]
    mu = select_measure_fun(prof, target)
    assert mu != "ssort_minimum"
    assert mu is None or "minimum" not in mu.lower()


def test_B4_bin_distrib_not_list_len() -> None:
    """Bin is multi-arm: adt_size (or skip), never false list_len spine."""
    path = _require_bench("autoproof", "standard", "bin_distrib")
    smt = path.read_text(encoding="utf-8")
    prof = build_problem_profile(smt, problem_id="bin")
    assert _list_nil_cons(prof, "Bin") is None
    mu, _, prelude = pick_or_synthesize_measure(prof, "Bin")
    assert mu == "__scheme_adt_size"
    assert "__scheme_list_len" not in prelude
