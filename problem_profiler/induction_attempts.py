"""Conservative detection of known induction attempts vs the current goal."""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Set, Tuple

from smt_patterns import normalize_lemma_formula, sexpr_head_args

from .types import FormulaRecord, InductionAttempt, ProblemProfile

_INT_SORTS = frozenset({"Int"})
_INT_BASE = "0"
_INT_STEP = "(+ 1 _)"


def analyze_induction_attempts(profile: ProblemProfile) -> List[InductionAttempt]:
    """Find strict base@ctor / step@ctor fragments for the current goal matrix.

    Only *known* hits are returned. Empty ``attempt=none`` placeholders are not
    emitted: literal α-matching against the library almost never fires, so those
    rows were constant prompt noise.

    ``Int`` binders are considered only when a goal-related Int-decreasing
    function actually takes that binder as an argument in the goal matrix
    (avoids treating list-element ``Int`` quantifiers as induction variables).
    """
    goal = _goal_raw(profile)
    if not goal:
        return []
    binders, matrix = _split_forall(goal)
    if not matrix:
        return []
    datatypes: Set[str] = set(profile.signature.get("datatypes") or [])
    ctor_arities: Dict[str, List[str]] = dict(
        profile.signature.get("constructor_arities") or {}
    )
    dt_ctors: Dict[str, List[str]] = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    if not ctor_arities:
        for c in profile.signature.get("constructors") or []:
            ctor_arities.setdefault(str(c), [])

    axioms = [
        rec for rec in profile.formulas
        if rec.role != "goal" and rec.raw
    ]
    int_ok_vars = _int_binders_used_by_int_recursion(profile, binders, matrix)
    inductive_binders = [
        (v, s) for v, s in binders
        if s in datatypes or (s in _INT_SORTS and v in int_ok_vars)
    ]
    if not inductive_binders:
        return []

    attempts: List[InductionAttempt] = []
    for nest_level, (var, sort) in enumerate(inductive_binders):
        if sort in _INT_SORTS:
            att = _analyze_int_binder(
                binders, matrix, var, sort, nest_level, axioms,
            )
            if att.base_ctors or att.step_ctors:
                attempts.append(att)
            continue

        allowed = set(dt_ctors.get(sort) or [])
        if not allowed:
            allowed = set(ctor_arities.keys())
        ctors_for_sort = {
            c: ctor_arities.get(c, [])
            for c in allowed
            if c in ctor_arities or c in allowed
        }
        for c in allowed:
            ctors_for_sort.setdefault(c, ctor_arities.get(c, []))
        bases: List[str] = []
        steps: List[str] = []
        src: List[str] = []

        for ctor, arg_sorts in sorted(ctors_for_sort.items()):
            if not arg_sorts:
                inst = _instantiate_goal(binders, matrix, var, ctor)
                hit = _find_matching_axiom(inst, axioms)
                if hit:
                    bases.append(ctor)
                    src.append(hit.formula_id)
                continue
            if sort not in arg_sorts:
                continue
            step_f = _make_step_formula(binders, matrix, var, sort, ctor, arg_sorts)
            if not step_f:
                continue
            hit = _find_matching_axiom(step_f, axioms)
            if hit:
                steps.append(ctor)
                src.append(hit.formula_id)

        if not (bases or steps):
            continue
        covered = sorted(set(bases) | set(steps))
        case_split = len(covered) >= 2
        detail_parts = []
        if bases:
            detail_parts.append("base@" + ",".join(bases))
        if steps:
            detail_parts.append("step@" + ",".join(steps))
        detail_parts.append(
            "case_split=" + ("yes" if case_split else "no")
            + (f" ({','.join(covered)})" if covered else "")
        )
        attempts.append(InductionAttempt(
            induct_var=var,
            induct_sort=sort,
            base_ctors=bases,
            step_ctors=steps,
            case_split=case_split,
            source_formula_ids=sorted(set(src)),
            evidence_level="structural",
            detail="; ".join(detail_parts),
            nest_level=nest_level,
            status="known",
        ))

    return attempts


def _int_binders_used_by_int_recursion(
    profile: ProblemProfile,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
) -> Set[str]:
    """Int vars that appear as args of a goal-related Int-style recursive function."""
    int_vars = {v for v, s in binders if s in _INT_SORTS}
    if not int_vars:
        return set()
    goal_syms = set()
    for rec in profile.formulas:
        if rec.formula_id == profile.goal_formula_id or rec.role == "goal":
            goal_syms = set(rec.symbols)
            break
    int_rec_funs: Set[str] = set()
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    for fact in profile.recursion_structure:
        funs = [f for f in fact.function.split("/") if f]
        if not any(f in goal_syms for f in funs):
            continue
        if fact.kind not in ("other_decreasing_recursion", "recursive_call"):
            # structural on ADT is not Int Peano context by itself
            if "(+ 1" not in (fact.detail or "") and fact.kind != "other_decreasing_recursion":
                continue
        for f in funs:
            meta = fun_sorts.get(f) or {}
            inputs = [str(s) for s in (meta.get("input_sorts") or [])]
            if "Int" in inputs or fact.kind == "other_decreasing_recursion":
                int_rec_funs.add(f)
    # Fallback: axioms with (f (+ 1 …
    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        for sym in goal_syms:
            if sym in rec.symbols and f"({sym} (+ 1" in rec.raw:
                int_rec_funs.add(sym)
    if not int_rec_funs:
        return set()
    used: Set[str] = set()
    for fun in int_rec_funs:
        used |= _vars_used_as_args(matrix, fun, int_vars)
    return used


def _vars_used_as_args(expr: str, fun: str, candidates: Set[str]) -> Set[str]:
    hit: Set[str] = set()

    def walk(text: str) -> None:
        text = (text or "").strip()
        if not text.startswith("("):
            return
        head, args = sexpr_head_args(text)
        if head == fun:
            for a in args:
                a = (a or "").strip()
                if a in candidates:
                    hit.add(a)
        for a in args:
            walk(a)

    walk(expr)
    return hit


def _arg_positions_of_var(expr: str, fun: str, var: str) -> Set[int]:
    """0-based argument indices where ``fun`` is applied directly to ``var``."""
    hit: Set[int] = set()

    def walk(text: str) -> None:
        text = (text or "").strip()
        if not text.startswith("("):
            return
        head, args = sexpr_head_args(text)
        if head == fun:
            for i, a in enumerate(args):
                if (a or "").strip() == var:
                    hit.add(i)
        for a in args:
            walk(a)

    walk(expr)
    return hit


def _analyze_int_binder(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
    nest_level: int,
    axioms: Sequence[FormulaRecord],
) -> InductionAttempt:
    bases: List[str] = []
    steps: List[str] = []
    src: List[str] = []

    inst0 = _instantiate_goal(binders, matrix, var, _INT_BASE)
    hit0 = _find_matching_axiom(inst0, axioms)
    if hit0:
        bases.append(_INT_BASE)
        src.append(hit0.formula_id)

    step_f = _make_int_step_formula(binders, matrix, var)
    if step_f:
        hit_s = _find_matching_axiom(step_f, axioms)
        if hit_s:
            steps.append(_INT_STEP)
            src.append(hit_s.formula_id)

    covered = sorted(set(bases) | set(steps))
    if bases or steps:
        detail_parts = []
        if bases:
            detail_parts.append("base@" + ",".join(bases))
        if steps:
            detail_parts.append("step@" + ",".join(steps))
        detail_parts.append(
            "case_split=" + ("yes" if len(covered) >= 2 else "no")
            + (f" ({','.join(covered)})" if covered else "")
        )
        return InductionAttempt(
            induct_var=var,
            induct_sort=sort,
            base_ctors=bases,
            step_ctors=steps,
            case_split=len(covered) >= 2,
            source_formula_ids=sorted(set(src)),
            evidence_level="structural",
            detail="; ".join(detail_parts),
            nest_level=nest_level,
            status="known",
        )
    return InductionAttempt(
        induct_var=var,
        induct_sort=sort,
        base_ctors=[],
        step_ctors=[],
        case_split=False,
        source_formula_ids=[],
        evidence_level="heuristic",
        detail="attempt=none",
        nest_level=nest_level,
        status="candidate",
    )


def _make_int_step_formula(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
) -> Optional[str]:
    """Build ``(forall (…n:Int…) (=> P[n] P[(+ 1 n)]))``."""
    ih = matrix
    concl = _subst_free(matrix, {var: f"(+ 1 {var})"})
    body = f"(=> {ih} {concl})"
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in binders)
    return normalize_lemma_formula(f"(forall ({parts}) {body})")


def _goal_raw(profile: ProblemProfile) -> Optional[str]:
    gid = profile.goal_formula_id
    for rec in profile.formulas:
        if rec.formula_id == gid or rec.role == "goal":
            return rec.raw
    return None


def _split_forall(formula: str) -> Tuple[List[Tuple[str, str]], str]:
    text = normalize_lemma_formula(formula or "")
    head, args = sexpr_head_args(text)
    if head != "forall" or len(args) < 2:
        return [], text
    binders: List[Tuple[str, str]] = []
    blob = args[0].strip()
    inner = blob[1:-1].strip() if blob.startswith("(") and blob.endswith(")") else blob
    from smt_patterns import read_sexpr
    j = 0
    while True:
        tok, j = read_sexpr(inner, j)
        if tok is None:
            break
        th, ta = sexpr_head_args(tok) if tok.startswith("(") else (tok, [])
        if th and ta:
            binders.append((th.strip(), ta[0].strip()))
        elif th:
            binders.append((th.strip(), ""))
    return binders, args[-1].strip()


def _subst_free(expr: str, mapping: Dict[str, str]) -> str:
    text = (expr or "").strip()
    if not text:
        return text
    if not text.startswith("("):
        return mapping.get(text, text)
    head, args = sexpr_head_args(text)
    if head is None:
        return text
    if head in ("forall", "exists") and args:
        binders_blob = args[0]
        bound: Set[str] = set()
        inner = binders_blob.strip()
        if inner.startswith("(") and inner.endswith(")"):
            inner = inner[1:-1].strip()
        from smt_patterns import read_sexpr
        j = 0
        while True:
            tok, j = read_sexpr(inner, j)
            if tok is None:
                break
            th, _ta = sexpr_head_args(tok) if tok.startswith("(") else (tok, [])
            if th:
                bound.add(th.strip())
        child_map = {k: v for k, v in mapping.items() if k not in bound}
        new_args = [binders_blob] + [_subst_free(a, child_map) for a in args[1:]]
        return "(" + " ".join([head] + new_args) + ")"
    return "(" + " ".join([head] + [_subst_free(a, mapping) for a in args]) + ")"


def _rewrap_forall(
    binders: Sequence[Tuple[str, str]],
    skip_var: str,
    matrix: str,
) -> str:
    kept = [(v, s) for v, s in binders if v != skip_var]
    if not kept:
        return matrix
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in kept)
    return f"(forall ({parts}) {matrix})"


def _instantiate_goal(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    term: str,
) -> str:
    body = _subst_free(matrix, {var: term})
    return normalize_lemma_formula(_rewrap_forall(binders, var, body))


def _make_step_formula(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
    ctor: str,
    arg_sorts: Sequence[str],
) -> Optional[str]:
    """Build ``(forall (new…) (=> P[t] P[c(…)]))`` with fresh binder names."""
    used = {v for v, _ in binders}
    fresh_args: List[str] = []
    fresh_binders: List[Tuple[str, str]] = []
    tail_var: Optional[str] = None
    for i, asort in enumerate(arg_sorts):
        name = f"_ih{i}"
        n = 0
        while name in used:
            n += 1
            name = f"_ih{i}_{n}"
        used.add(name)
        fresh_args.append(name)
        fresh_binders.append((name, asort))
        if asort == sort and tail_var is None:
            tail_var = name
    if tail_var is None:
        for name, asort in reversed(list(zip(fresh_args, arg_sorts))):
            if asort == sort:
                tail_var = name
                break
    if tail_var is None:
        return None
    ctor_term = f"({ctor} {' '.join(fresh_args)})" if fresh_args else ctor
    ih = _subst_free(matrix, {var: tail_var})
    concl = _subst_free(matrix, {var: ctor_term})
    body = f"(=> {ih} {concl})"
    outer = [(v, s) for v, s in binders if v != var] + fresh_binders
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in outer)
    return normalize_lemma_formula(f"(forall ({parts}) {body})")


def _formulas_match(left: str, right: str) -> bool:
    a = normalize_lemma_formula(left)
    b = normalize_lemma_formula(right)
    if not a or not b:
        return False
    if a == b:
        return True
    try:
        from obligation_tree import lemmas_equivalent
        return lemmas_equivalent(a, b)
    except Exception:
        return False


def _find_matching_axiom(
    target: str,
    axioms: Sequence[FormulaRecord],
) -> Optional[FormulaRecord]:
    for rec in axioms:
        if _formulas_match(rec.raw, target):
            return rec
        th, ta = sexpr_head_args(rec.raw)
        if th == "forall" and len(ta) >= 2 and _formulas_match(ta[-1], target):
            return rec
    return None
