#!/usr/bin/env python3
"""Correctness and effectiveness tests for SMT-LIB2 ADT tester rewrite.

Run from repo root:

    python3 tests/test_adt_tester_rewrite.py

This script:
1. Unit-tests the rewriter on nested testers and boolean uses.
2. Rewrites all AutoProofBM standard/ templates and checks no shorthand remains.
3. Checks CVC5 status agreement (original vs rewritten) — semantic correctness.
4. Checks Vampire parse: original fails, rewritten is accepted — input fix.
5. Runs Vampire --schedule induction on rewritten files to measure effectiveness.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from smt_adt_tester_rewrite import (  # noqa: E402
    count_shorthand_testers,
    remaining_shorthand_testers,
    rewrite_smtlib_testers,
)

STANDARD = ROOT / "benchmarks/preprocessed/autoproof/standard"
VAMPIRE = os.getenv("VAMPIRE_BINARY", str(ROOT / "vampire/vampire"))
CVC5 = os.getenv("CVC5_BINARY", str(ROOT / "cvc/cvc5-Linux-x86_64-static/bin/cvc5"))

# Effectiveness timeout per rewritten problem (Vampire induction portfolio).
VAMPIRE_TIMEOUT_S = int(os.getenv("TEST_VAMPIRE_TIMEOUT", "20"))
CVC5_TIMEOUT_MS = int(os.getenv("TEST_CVC5_TIMEOUT_MS", "8000"))
MAX_WORKERS = int(os.getenv("TEST_MAX_WORKERS", "8"))


def templates() -> list:
    return sorted(STANDARD.glob("*/template.smt2"))


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    raise AssertionError(msg)


def test_unit_rewrite() -> None:
    src = """
; comment (is-S x) should stay
(assert (forall ((x Nat) (y Nat))
  (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert (= (eqA x y) (ite (is-Y x) (is-Y y) (not (is-Y y)))))
(assert (ite (is-S (p x)) a b))
(assert ((_ is S) z))
"""
    out, n = rewrite_smtlib_testers(src)
    if n != 5:
        fail(f"unit rewrite count expected 5, got {n}\n{out}")
    leftover = remaining_shorthand_testers(out)
    if leftover:
        fail(f"unit leftover testers: {leftover}")
    if "(is-S x) should stay" not in out:
        fail("comment was rewritten")
    if "((_ is S) x)" not in out:
        fail("missing rewrite of (is-S x)")
    if "((_ is S) (p x))" not in out:
        fail("missing nested rewrite of (is-S (p x))")
    if "((_ is Y) x)" not in out or "((_ is Y) y)" not in out:
        fail("missing boolean tester rewrite")
    # already indexed form must remain
    if out.count("((_ is S) z)") != 1:
        fail(f"indexed tester mishandled:\n{out}")
    print("PASS unit rewrite")


def test_rewrite_all_standard() -> None:
    files = templates()
    if len(files) != 119:
        fail(f"expected 119 standard templates, got {len(files)}")
    total = 0
    for p in files:
        text = p.read_text(encoding="utf-8")
        n0 = count_shorthand_testers(text)
        if n0 == 0:
            fail(f"{p} has no shorthand testers")
        out, n = rewrite_smtlib_testers(text)
        if n != n0:
            fail(f"{p}: rewrite count {n} != scan count {n0}")
        leftover = remaining_shorthand_testers(out)
        if leftover:
            fail(f"{p}: leftover {leftover}")
        total += n
    print(f"PASS rewrite all standard/ templates ({total} testers in 119 files)")


def _cvc5_status(smt_text: str, timeout_ms: int) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False, encoding="utf-8") as f:
        f.write(smt_text)
        path = f.name
    try:
        proc = subprocess.run(
            [CVC5, "--lang=smt2", f"--tlimit={timeout_ms}", path],
            capture_output=True,
            text=True,
            timeout=timeout_ms / 1000.0 + 8,
        )
        stdout = (proc.stdout or "").strip()
        combined = (stdout + "\n" + (proc.stderr or "")).lower()
        lines = [ln.strip() for ln in stdout.splitlines() if ln.strip()]
        last = lines[-1] if lines else ""
        if last == "unsat":
            return "unsat"
        if last == "sat":
            return "sat"
        if last == "unknown" or "interrupted by timeout" in combined:
            return "unknown"
        if proc.returncode != 0:
            return "unknown"
        return last or "unknown"
    except subprocess.TimeoutExpired:
        return "unknown"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


_DEFINITIONAL_QUERIES = [
    # Nat / successor (nat_acc_plus_same)
    """(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))
(assert (not (forall ((x Nat)) (= (is-S x) ((_ is S) x)))))
(check-sat)
""",
    """(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))
(assert (not (forall ((x Nat)) (= (is-Z x) ((_ is Z) x)))))
(check-sat)
""",
    # Bin testers (bin_plus)
    """(set-logic UFDT)
(declare-datatypes ((Bin 0)) (((One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(assert (not (forall ((x Bin)) (= (is-OneAnd x) ((_ is OneAnd) x)))))
(check-sat)
""",
    """(set-logic UFDT)
(declare-datatypes ((Bin 0)) (((One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(assert (not (forall ((x Bin)) (= (is-ZeroAnd x) ((_ is ZeroAnd) x)))))
(check-sat)
""",
    """(set-logic UFDT)
(declare-datatypes ((Bin 0)) (((One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(assert (not (forall ((x Bin)) (= (is-One x) ((_ is One) x)))))
(check-sat)
""",
    # list testers (list_return_1)
    """(set-logic UFDT)
(declare-sort sk_a 0)
(declare-datatypes ((list 0)) (((nil) (cons (head sk_a) (tail list)))))
(assert (not (forall ((x list)) (= (is-cons x) ((_ is cons) x)))))
(check-sat)
""",
    """(set-logic UFDT)
(declare-sort sk_b 0)
(declare-datatypes ((list2 0)) (((nil2) (cons2 (head2 sk_b) (tail2 list2)))))
(assert (not (forall ((x list2)) (= (is-cons2 x) ((_ is cons2) x)))))
(check-sat)
""",
    # regexp (regexp_RecAtom)
    """(set-logic UFDT)
(declare-datatypes ((A 0)) (((X) (Y))))
(assert (not (forall ((x A)) (= (is-Y x) ((_ is Y) x)))))
(check-sat)
""",
    """(set-logic UFDT)
(declare-datatypes ((A 0)) (((X) (Y))))
(declare-datatypes ((R 0))
  (((Nil) (Eps) (Atom (Atom_0 A)) (Plus (Plus_0 R) (Plus_1 R))
    (Seq (Seq_0 R) (Seq_1 R)) (Star (Star_0 R)))))
(assert (not (forall ((x R)) (= (is-Nil x) ((_ is Nil) x)))))
(check-sat)
""",
    """(set-logic UFDT)
(declare-datatypes ((A 0)) (((X) (Y))))
(declare-datatypes ((R 0))
  (((Nil) (Eps) (Atom (Atom_0 A)) (Plus (Plus_0 R) (Plus_1 R))
    (Seq (Seq_0 R) (Seq_1 R)) (Star (Star_0 R)))))
(assert (not (forall ((x R)) (and
  (= (is-Eps x) ((_ is Eps) x))
  (= (is-Star x) ((_ is Star) x))
  (= (is-Seq x) ((_ is Seq) x))
  (= (is-Plus x) ((_ is Plus) x))
  (= (is-Atom x) ((_ is Atom) x))))))
(check-sat)
""",
    # nested argument still equivalent
    """(set-logic UFDT)
(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))
(assert (not (forall ((x Nat)) (= (is-S (p (S x))) ((_ is S) (p (S x)))))))
(check-sat)
""",
]


def test_definitional_equivalence() -> None:
    """SMT-LIB2: (is-C x) is sugar for ((_ is C) x). cvc5 must prove they coincide."""
    bad = []
    for i, q in enumerate(_DEFINITIONAL_QUERIES):
        st = _cvc5_status(q, 4000)
        if st != "unsat":
            bad.append((i, st, q.splitlines()[2][:80]))
    if bad:
        fail(f"definitional equivalence not unsat: {bad}")
    print(f"PASS definitional equivalence ({len(_DEFINITIONAL_QUERIES)} cvc5 queries, all unsat)")


def test_cvc5_file_no_sat_mismatch() -> None:
    """Sample full files: rewrite must not flip sat/unsat (timeouts count as unknown)."""
    sample = [
        STANDARD / "list_return_1/template.smt2",
        STANDARD / "nat_acc_plus_same/template.smt2",
        STANDARD / "bin_s/template.smt2",
        STANDARD / "regexp_RecAtom/template.smt2",
        STANDARD / "int_add_ident_right/template.smt2",
        STANDARD / "tree_Flatten3/template.smt2",
    ]
    mismatches = []
    for p in sample:
        orig = p.read_text(encoding="utf-8")
        rw, _ = rewrite_smtlib_testers(orig)
        s0 = _cvc5_status(orig, 6000)
        s1 = _cvc5_status(rw, 6000)
        if {s0, s1} == {"sat", "unsat"}:
            mismatches.append((p.parent.name, s0, s1))
    if mismatches:
        fail(f"sat/unsat mismatch after rewrite: {mismatches}")
    print(f"PASS cvc5 sample-file check ({len(sample)} files, no sat/unsat flip)")


def _vampire_raw(path: Path, timeout_s: int, rewrite: bool) -> tuple:
    """Run Vampire. If rewrite=False, disable runner rewrite via env in-process.

    Returns (status, snippet).
    """
    env = os.environ.copy()
    env["VAMPIRE_REWRITE_TESTERS"] = "on" if rewrite else "off"
    cmd = [
        VAMPIRE,
        "-t", f"{timeout_s}s",
        "--mode", "vampire" if timeout_s <= 3 else "portfolio",
        "--input_syntax", "smtlib2",
        "--output_mode", "vampire",
        "--proof", "off",
        "--statistics", "none",
    ]
    if timeout_s > 3:
        cmd[cmd.index("--mode") + 1] = "portfolio"
        cmd.extend(["--schedule", "induction"])
    cmd.append(str(path))
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout_s + 8,
            env=env,
            cwd=str(ROOT),
        )
        text = proc.stdout + "\n" + proc.stderr
    except subprocess.TimeoutExpired as e:
        text = (e.stdout or "") + "\n" + (e.stderr or "")
        return "timeout", (text[-400:] if text else "TimeoutExpired")
    low = text.lower()
    if "unrecognized term identifier" in low or "user error" in low:
        return "parse_error", text.strip().splitlines()[-1] if text.strip() else "user error"
    if "refutation found" in low or "termination reason: refutation" in low or "unsatisfiable" in low:
        return "unsat", "refutation"
    if "satisfiable" in low and "unsatisfiable" not in low:
        return "sat", "sat"
    if "time limit" in low or "termination reason: time limit" in low:
        return "timeout", "time limit"
    if "incomplete" in low or "refutation not found" in low:
        return "incomplete", "incomplete"
    return "unknown", text.strip().splitlines()[-1][:200] if text.strip() else "empty"


def test_vampire_parse_gate() -> None:
    """Original shorthand is rejected; rewritten indexed testers are accepted."""
    sample = [
        STANDARD / "bin_plus/template.smt2",
        STANDARD / "nat_acc_plus_same/template.smt2",
        STANDARD / "list_return_1/template.smt2",
        STANDARD / "regexp_RecAtom/template.smt2",
        STANDARD / "int_mul_comm/template.smt2",
        STANDARD / "sort_QSortIsSort/template.smt2",
    ]
    for p in sample:
        st0, sn0 = _vampire_raw(p, 2, rewrite=False)
        if st0 != "parse_error":
            fail(f"expected parse_error on original {p.name}, got {st0}: {sn0}")
        text = p.read_text(encoding="utf-8")
        rw, _ = rewrite_smtlib_testers(text)
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False, encoding="utf-8") as f:
            f.write(rw)
            tmp = Path(f.name)
        try:
            st1, sn1 = _vampire_raw(tmp, 2, rewrite=False)
        finally:
            tmp.unlink(missing_ok=True)
        if st1 == "parse_error":
            fail(f"rewritten {p.name} still parse_error: {sn1}")
    print(f"PASS vampire parse gate on {len(sample)} representative files")


def test_vampire_effectiveness() -> None:
    files = templates()
    proved = []
    parse_ok_not_proved = []
    parse_fail = []
    errors = []

    def one(p: Path):
        orig = p.read_text(encoding="utf-8")
        rw, _ = rewrite_smtlib_testers(orig)
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False, encoding="utf-8") as f:
            f.write(rw)
            tmp = Path(f.name)
        try:
            st, sn = _vampire_raw(tmp, VAMPIRE_TIMEOUT_S, rewrite=False)
        finally:
            tmp.unlink(missing_ok=True)
        return p, st, sn

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
        futs = [ex.submit(one, p) for p in files]
        done = 0
        for fut in as_completed(futs):
            p, st, sn = fut.result()
            done += 1
            if done % 20 == 0 or done == len(files):
                print(f"  vampire effectiveness {done}/{len(files)} ...")
            rel = str(p.parent.relative_to(STANDARD.parent))
            if st == "unsat":
                proved.append(rel)
            elif st == "parse_error":
                parse_fail.append((rel, sn))
            elif st in ("timeout", "incomplete", "unknown"):
                parse_ok_not_proved.append(rel)
            else:
                errors.append((rel, st, sn))

    print(f"Vampire induction {VAMPIRE_TIMEOUT_S}s on rewritten standard/:")
    print(f"  proved (unsat): {len(proved)}")
    print(f"  accepted but not proved: {len(parse_ok_not_proved)}")
    print(f"  parse_error: {len(parse_fail)}")
    print(f"  other: {len(errors)}")
    if proved:
        print("  proved tasks:")
        for name in sorted(proved):
            print(f"    {name}")
    if parse_fail:
        fail(f"rewritten files still parse_error: {parse_fail[:5]}")
    if errors:
        fail(f"vampire other errors: {errors[:5]}")
    if len(proved) == 0:
        fail("rewrite accepted by Vampire but proved 0 tasks; expected at least nat_acc_plus_same")
    print(
        f"PASS vampire effectiveness: {len(proved)}/{len(files)} proved, "
        f"{len(parse_ok_not_proved)} searchable, 0 parse errors"
    )


def test_runner_integration() -> None:
    """vampire_runner.run_vampire should auto-rewrite and prove a simple task."""
    os.environ["VAMPIRE_REWRITE_TESTERS"] = "on"
    from vampire_runner import run_vampire

    p = STANDARD / "nat_acc_plus_same/template.smt2"
    res = run_vampire(p, timeout=20, collect_stats=False)
    if not res.proved:
        fail(f"run_vampire on rewritten nat_acc_plus_same failed: status={res.status} err={res.error}")
    # original path must still exist (rewrite is temporary)
    if not p.exists():
        fail("original template was deleted")
    print("PASS runner integration (nat_acc_plus_same unsat via auto-rewrite)")


def main() -> int:
    print(f"ROOT={ROOT}")
    print(f"VAMPIRE={VAMPIRE}")
    print(f"CVC5={CVC5}")
    test_unit_rewrite()
    test_rewrite_all_standard()
    test_definitional_equivalence()
    test_cvc5_file_no_sat_mismatch()
    test_vampire_parse_gate()
    test_runner_integration()
    test_vampire_effectiveness()
    print("ALL TESTS PASSED")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AssertionError:
        sys.exit(1)
