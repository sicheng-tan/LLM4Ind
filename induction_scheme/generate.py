"""Generate and structurally validate induction-scheme obligations."""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Set, Tuple

from smt_patterns import normalize_lemma_formula, sexpr_head_args

from problem_profiler import build_problem_profile
from problem_profiler.induction_attempts import (
    _int_binders_used_by_int_recursion,
    _arg_positions_of_var,
    _split_forall,
    _subst_free,
    _vars_used_as_args,
)
from problem_profiler.analyze import structural_rec_arg_positions
from problem_profiler.types import ProblemProfile

from .constants import MAX_VARS
from .types import SchemeAttempt, SchemeObligation

_INT_SORTS = frozenset({"Int"})
_INT_BASE = "0"
_INT_STEP = "(+ 1 _)"
_MEASURE_RETURN_SORTS = frozenset({"Int", "Nat", "nat", "Natural"})
_MEASURE_NAME_BONUS = (
    "zlength", "length", "len", "lentree", "hsize", "size", "sizeof",
    "height", "depth", "weight", "rank",
)
# Reject Int-typed functions that are not size-like (e.g. ssort_minimum).
_MEASURE_NAME_BLOCK_SUBSTR = ("minimum", "maximum")


def generate_scheme(
    smt_text: str,
    *,
    goal_name: str = "",
    mode: str = "structural",
    depth: int = 0,
    nest_budget: int = 1,
    current_goal: Optional[str] = None,
) -> SchemeAttempt:
    """Build ≤1 scheme attempt (see ``generate_scheme_candidates`` for both).

    ``mode=both`` returns the *first* ordered candidate without proving; the
    prove path in ``run_scheme_round`` may pick the other if its goal-gate wins.
    """
    cands = generate_scheme_candidates(
        smt_text,
        goal_name=goal_name,
        mode=mode,
        depth=depth,
        nest_budget=nest_budget,
        current_goal=current_goal,
    )
    if cands:
        return cands[0]
    # Skipped placeholder with combined reasons.
    attempt = SchemeAttempt(
        goal_name=goal_name or "",
        mode=(mode or "structural").strip().lower() or "structural",
        depth=depth,
        nest_budget=nest_budget,
        skipped=True,
        skip_reason="no_scheme_candidate",
    )
    return attempt


def generate_scheme_candidates(
    smt_text: str,
    *,
    goal_name: str = "",
    mode: str = "structural",
    depth: int = 0,
    nest_budget: int = 1,
    current_goal: Optional[str] = None,
) -> List[SchemeAttempt]:
    """Return validated structural and/or measure candidates.

    For ``both``, both axes are included when each validates (RC goals order
    measure first). Dispatch short-proves all viable axes and merges
    nest/harvest — it does not pick a single winner by gate alone.
    """
    mode_l = (mode or "structural").strip().lower()
    if mode_l not in ("structural", "measure", "both"):
        return []

    profile = build_problem_profile(smt_text, problem_id=goal_name or "scheme")
    if current_goal:
        goal_raw = normalize_lemma_formula(current_goal)
    else:
        goal_raw = _goal_raw(profile)
    if not goal_raw:
        return []
    binders, matrix = _split_forall(goal_raw)
    if not matrix:
        return []

    def _struct() -> Optional[SchemeAttempt]:
        att = _fill_structural_attempt(
            SchemeAttempt(
                goal_name=goal_name or "",
                mode=mode_l if mode_l != "both" else "structural",
                depth=depth,
                nest_budget=nest_budget,
            ),
            profile,
            binders,
            matrix,
        )
        if att.skipped or not att.validated:
            return None
        return att

    def _meas() -> Optional[SchemeAttempt]:
        att = _fill_measure_attempt(
            SchemeAttempt(
                goal_name=goal_name or "",
                mode=mode_l if mode_l != "both" else "measure",
                depth=depth,
                nest_budget=nest_budget,
            ),
            profile,
            binders,
            matrix,
            smt_text=smt_text,
        )
        if att.skipped or not att.validated:
            return None
        return att

    if mode_l == "structural":
        s = _struct()
        return [s] if s else []
    if mode_l == "measure":
        m = _meas()
        return [m] if m else []

    # both
    s = _struct()
    m = _meas()
    rc_first = _goal_has_recursive_call(profile)
    ordered: List[SchemeAttempt] = []
    if rc_first:
        if m:
            ordered.append(m)
        if s:
            ordered.append(s)
    else:
        if s:
            ordered.append(s)
        if m:
            ordered.append(m)
    return ordered


def _goal_has_recursive_call(profile: ProblemProfile) -> bool:
    goal_syms: Set[str] = set()
    for rec in profile.formulas:
        if rec.formula_id == profile.goal_formula_id or rec.role == "goal":
            goal_syms = set(rec.symbols or [])
            break
    if not goal_syms:
        return False
    for fact in profile.recursion_structure:
        if fact.kind != "recursive_call":
            continue
        if any(p in goal_syms for p in fact.function.split("/") if p):
            return True
    return False


def _fill_structural_attempt(
    attempt: SchemeAttempt,
    profile: ProblemProfile,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
) -> SchemeAttempt:
    choice = select_induct_var(profile, binders, matrix)
    if choice is None:
        attempt.skipped = True
        attempt.skip_reason = "no_induct_var"
        return attempt

    var, sort = choice
    attempt.induct_var = var
    attempt.induct_sort = sort

    if sort in _INT_SORTS:
        obligations = _generate_int(binders, matrix, var, sort)
    else:
        obligations = _generate_adt(profile, binders, matrix, var, sort)

    if not obligations:
        attempt.skipped = True
        attempt.skip_reason = "empty_obligations"
        return attempt

    ok, errors = validate_scheme(
        obligations, binders=binders, matrix=matrix, var=var, sort=sort,
        profile=profile,
    )
    attempt.obligations = obligations
    attempt.validated = ok
    attempt.validate_errors = errors
    for obl in obligations:
        obl.validated = ok and not obl.validate_errors
    return attempt


def _fill_measure_attempt(
    attempt: SchemeAttempt,
    profile: ProblemProfile,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    *,
    smt_text: str = "",
) -> SchemeAttempt:
    del smt_text
    from .bridges import (
        generate_bridge_obligations,
        pick_or_synthesize_measure,
    )

    choice = select_induct_var_for_measure(profile, binders, matrix)
    prelude = ""
    ret = "Int"
    if choice is None:
        # No existing μ: try structural induct var + synthesize list length.
        struct = select_induct_var(profile, binders, matrix)
        if struct is None:
            attempt.skipped = True
            attempt.skip_reason = "no_measure_induct_var"
            return attempt
        var, sort = struct
        if sort in _INT_SORTS:
            attempt.skipped = True
            attempt.skip_reason = "no_measure_induct_var"
            return attempt
        mu, ret, prelude = pick_or_synthesize_measure(profile, sort)
        if not mu:
            attempt.skipped = True
            attempt.skip_reason = "no_measure_fun"
            return attempt
    else:
        var, sort, mu = choice
        fun_sorts = dict(profile.signature.get("fun_sorts") or {})
        ret = str((fun_sorts.get(mu) or {}).get("return_sort") or "Int")
        if ret != "Int":
            prelude = _nat_to_int_prelude(profile, ret) or ""
            if not prelude:
                # Fall back to synthesized Int length when Nat→Int unavailable.
                mu2, ret2, prelude2 = pick_or_synthesize_measure(profile, sort)
                if mu2 and ret2 == "Int":
                    mu, ret, prelude = mu2, ret2, prelude2
                else:
                    attempt.skipped = True
                    attempt.skip_reason = f"no_nat_to_int:{ret}"
                    return attempt

    attempt.induct_var = var
    attempt.induct_sort = sort
    attempt.measure_fun = mu
    attempt.measure_ret_sort = ret
    attempt.measure_prelude = prelude
    if attempt.mode not in ("measure", "both"):
        attempt.mode = "measure"

    use_nat = bool(prelude) and "__scheme_nat_to_int" in prelude
    bridges = generate_bridge_obligations(
        profile,
        binders=binders,
        matrix=matrix,
        induct_var=var,
        induct_sort=sort,
        measure_fun=mu,
        measure_ret_sort=ret,
        use_nat_to_int=use_nat,
    )

    if not bridges:
        # No concrete descent/semantic bridges → skip measure.
        # Abstract WF (∀y. μ(y)<μ(x)⇒P[y])⇒P[x] was tried earlier and did not
        # help bottleneck goals (heap/qsort/bub); it is intentionally not emitted.
        attempt.skipped = True
        attempt.skip_reason = "no_measure_bridges"
        return attempt

    nonneg = _generate_measure_nonneg(
        var, sort, mu, use_nat_to_int=use_nat,
    )
    obligations = ([nonneg] if nonneg else []) + bridges
    attempt.bridge_primary = True

    if not obligations:
        attempt.skipped = True
        attempt.skip_reason = "empty_measure_obligations"
        return attempt

    ok, errors = validate_scheme(
        obligations, binders=binders, matrix=matrix, var=var, sort=sort,
        profile=profile,
    )
    attempt.obligations = obligations
    attempt.validated = ok
    attempt.validate_errors = errors
    for obl in obligations:
        obl.validated = ok and not obl.validate_errors
    return attempt


def select_measure_fun(profile: ProblemProfile, sort: str) -> Optional[str]:
    """Pick μ : ``sort`` → Int/Nat (prefer length/size-like; reject min/max)."""
    if not sort:
        return None
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    candidates: List[Tuple[int, str]] = []

    def consider(name: str) -> None:
        meta = fun_sorts.get(name) or {}
        inputs = [str(s) for s in (meta.get("input_sorts") or [])]
        ret = str(meta.get("return_sort") or "")
        if ret not in _MEASURE_RETURN_SORTS:
            return
        if sort not in inputs:
            return
        low = name.lower()
        if any(b in low for b in _MEASURE_NAME_BLOCK_SUBSTR):
            return
        # Prefer unary size-like; require a name bonus hit OR unary observer.
        score = 0
        bonus = False
        for i, token in enumerate(_MEASURE_NAME_BONUS):
            if token in low:
                score += 30 - i
                bonus = True
                break
        if not bonus and len(inputs) != 1:
            return
        if not bonus:
            score += 1  # weak unary fallback
        if len(inputs) == 1:
            score += 5
        if ret == "Int":
            score += 4  # prefer native Int over Nat→Int
        for obs in profile.observer_candidates:
            if obs.function == name:
                score += 3
                break
        candidates.append((score, name))

    for obs in profile.observer_candidates:
        consider(obs.function)
    for name in fun_sorts:
        consider(name)

    if not candidates:
        return None
    candidates.sort(key=lambda t: (-t[0], t[1]))
    return candidates[0][1]


def select_induct_var_for_measure(
    profile: ProblemProfile,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
) -> Optional[Tuple[str, str, str]]:
    """Return ``(var, sort, measure_fun)`` for an *existing* size-like symbol.

    Prefer the structural induct var when it admits a measure; else any ADT
    binder with a measure. Callers may synthesize ``__scheme_list_len`` when
    this returns None (see ``_fill_measure_attempt``).
    """
    datatypes: Set[str] = set(profile.signature.get("datatypes") or [])
    struct_choice = select_induct_var(profile, binders, matrix)
    if struct_choice is not None:
        var, sort = struct_choice
        if sort not in _INT_SORTS:
            mu = select_measure_fun(profile, sort)
            if mu:
                return (var, sort, mu)

    scored: List[Tuple[int, str, str, str]] = []
    rec_positions = structural_rec_arg_positions(profile)
    struct_funs = _structural_funs(profile)
    conclusion = _matrix_conclusion(matrix)
    for idx, (var, sort) in enumerate(binders):
        if sort not in datatypes:
            continue
        mu = select_measure_fun(profile, sort)
        if not mu:
            continue
        sc, _, _ = _adt_induct_score(
            var,
            sort,
            matrix=matrix,
            conclusion=conclusion,
            struct_funs=struct_funs,
            rec_positions=rec_positions,
            binder_index=idx,
        )
        scored.append((sc, var, sort, mu))
    if not scored:
        return None
    scored.sort(key=lambda t: (-t[0], t[1]))
    _, var, sort, mu = scored[0]
    return (var, sort, mu)


def _nat_zero_succ(
    profile: ProblemProfile, nat_sort: str,
) -> Optional[Tuple[str, str]]:
    """Return ``(zero_ctor, succ_ctor)`` for a Peano-like datatype."""
    dt_ctors = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    arities = {
        str(k): list(v or [])
        for k, v in (profile.signature.get("constructor_arities") or {}).items()
    }
    ctors = list(dt_ctors.get(nat_sort) or [])
    if not ctors:
        return None
    zeros = [c for c in ctors if not arities.get(c)]
    succs = [
        c for c in ctors
        if arities.get(c) == [nat_sort]
    ]
    if len(zeros) == 1 and len(succs) == 1:
        return zeros[0], succs[0]
    # Name heuristics
    for z, s in (("Z", "S"), ("zero", "succ"), ("O", "S"), ("Zero", "Succ")):
        if z in ctors and s in ctors:
            return z, s
    return None


def _nat_to_int_prelude(profile: ProblemProfile, nat_sort: str) -> Optional[str]:
    pair = _nat_zero_succ(profile, nat_sort)
    if pair is None:
        return None
    zero, succ = pair
    fun = "__scheme_nat_to_int"
    return (
        f"; induction scheme Nat→Int for measure comparisons\n"
        f"(declare-fun {fun} ({nat_sort}) Int)\n"
        f"(assert (= ({fun} {zero}) 0))\n"
        f"(assert (forall ((__n {nat_sort})) "
        f"(= ({fun} ({succ} __n)) (+ 1 ({fun} __n)))))\n"
    )


def _measure_term(measure_fun: str, arg: str, *, use_nat_to_int: bool) -> str:
    raw = f"({measure_fun} {arg})"
    if use_nat_to_int:
        return f"(__scheme_nat_to_int {raw})"
    return raw


def _generate_measure_nonneg(
    var: str,
    sort: str,
    measure_fun: str,
    *,
    use_nat_to_int: bool = False,
) -> Optional[SchemeObligation]:
    """Optional μ≥0 side obligation (cheap; often short-proves).

    Historical note: an abstract WF obligation
    ``(∀y. μ(y)<μ(x)⇒P[y]) ⇒ P[x]`` used to be generated alongside this
    (see git history / ``_generate_measure``). It was dropped — CVC almost
    never discharges it on bottleneck goals, and concrete bridges replace it.
    """
    mu_x = _measure_term(measure_fun, var, use_nat_to_int=use_nat_to_int)
    nonneg = normalize_lemma_formula(
        f"(forall (({var} {sort})) (>= {mu_x} 0))"
    )
    return SchemeObligation(
        obl_id="measure_nonneg",
        kind="measure",
        ctor="nonneg",
        formula=nonneg,
        induct_var=var,
        induct_sort=sort,
        inst_term=var,
    )


def _generate_measure(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
    measure_fun: str,
    *,
    ret_sort: str = "Int",
    use_nat_to_int: bool = False,
) -> List[SchemeObligation]:
    """Retired: abstract WF + nonneg. Kept as a no-op stub for import traces.

    Prefer ``_generate_measure_nonneg`` + ``generate_bridge_obligations``.
    """
    del binders, matrix, ret_sort
    obl = _generate_measure_nonneg(
        var, sort, measure_fun, use_nat_to_int=use_nat_to_int,
    )
    return [obl] if obl else []


def _matrix_conclusion(matrix: str) -> str:
    """Peel a top-level implication; prefer consequent for induct-var scoring."""
    if not matrix or not matrix.startswith("("):
        return matrix
    head, args = sexpr_head_args(matrix)
    if head == "=>" and len(args) >= 2:
        return args[-1]
    return matrix


def _adt_induct_score(
    var: str,
    sort: str,
    *,
    matrix: str,
    conclusion: str,
    struct_funs: Set[str],
    rec_positions: Dict[str, Set[int]],
    binder_index: int,
) -> Tuple[int, int, int]:
    """Higher is better. Tie-break: earlier binder (smaller index).

    Priority among structural ADT candidates:
    1. Occupies a **defining recursive argument position** of a structural fun
       in the goal **conclusion** (not only antecedent / parameter slots).
    2. Same, counted over the full matrix.
    3. Soft: any structural-fun argument occurrence (legacy coverage).
    """
    del sort  # sort kept for call-site symmetry; positions dominate type heuristics
    rec_conc = 0
    param_conc = 0
    rec_all = 0
    param_all = 0
    any_all = 0
    for fun in struct_funs:
        rpos = rec_positions.get(fun) or set()
        for i in _arg_positions_of_var(conclusion, fun, var):
            if i in rpos:
                rec_conc += 1
            else:
                param_conc += 1
        for i in _arg_positions_of_var(matrix, fun, var):
            if i in rpos:
                rec_all += 1
            else:
                param_all += 1
        if var in _vars_used_as_args(matrix, fun, {var}):
            any_all += 1

    # Strong preference: conclusion recursive slots; parameters get little credit.
    score = (
        20 * rec_conc
        + 4 * rec_all
        + 1 * any_all
        - 3 * param_conc
        - 1 * param_all
    )
    return (score, -binder_index, binder_index)


def _best_adt_induct_var(
    candidates: Sequence[Tuple[str, str]],
    matrix: str,
    struct_funs: Set[str],
    rec_positions: Dict[str, Set[int]],
) -> Tuple[str, str]:
    conclusion = _matrix_conclusion(matrix)
    ranked = sorted(
        enumerate(candidates),
        key=lambda it: _adt_induct_score(
            it[1][0],
            it[1][1],
            matrix=matrix,
            conclusion=conclusion,
            struct_funs=struct_funs,
            rec_positions=rec_positions,
            binder_index=it[0],
        ),
        reverse=True,
    )
    return ranked[0][1]


def select_induct_var(
    profile: ProblemProfile,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
) -> Optional[Tuple[str, str]]:
    """Prefer structural-recursion ADT args; else Peano Int; skip non-structural.

    Among several ADT binders, prefer those that occupy **recursive argument
    positions** (from defining equations) of structural functions in the
    goal conclusion — e.g. ``xs`` in ``(append xs ys)``, not parameter ``ys``.
    """
    datatypes: Set[str] = set(profile.signature.get("datatypes") or [])
    struct_funs = _structural_funs(profile)
    nonstruct_funs = _nonstructural_funs(profile)
    goal_syms = _goal_symbols(profile)
    rec_positions = structural_rec_arg_positions(profile)

    # ADT binders used by structural recursion in the goal matrix.
    adt_struct: List[Tuple[str, str]] = []
    adt_nonstruct_only: Set[str] = set()
    for var, sort in binders:
        if sort not in datatypes:
            continue
        used_by_struct = False
        used_by_nonstruct = False
        for fun in struct_funs:
            if var in _vars_used_as_args(matrix, fun, {var}):
                used_by_struct = True
                break
        for fun in nonstruct_funs:
            if var in _vars_used_as_args(matrix, fun, {var}):
                used_by_nonstruct = True
                break
        if used_by_struct:
            adt_struct.append((var, sort))
        elif used_by_nonstruct and not used_by_struct:
            adt_nonstruct_only.add(var)

    if adt_struct:
        return _best_adt_induct_var(adt_struct, matrix, struct_funs, rec_positions)

    # Fallback: ADT binder of a sort that has structural defs overall, even if
    # the binder is not literally an arg of that fun head (e.g. goal uses the
    # function on a compound term). Prefer binders whose sort appears in
    # structural fun input sorts.
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    struct_input_sorts: Set[str] = set()
    for fun in struct_funs:
        meta = fun_sorts.get(fun) or {}
        for s in meta.get("input_sorts") or []:
            struct_input_sorts.add(str(s))

    adt_fallback: List[Tuple[str, str]] = []
    for var, sort in binders:
        if sort not in datatypes:
            continue
        if var in adt_nonstruct_only and sort not in struct_input_sorts:
            continue
        # Skip sorts that only have non-structural recursion among goal-related
        # functions and never appear as structural inputs.
        if sort not in struct_input_sorts and _sort_is_nonstructural_only(
            profile, sort, goal_syms
        ):
            continue
        if sort in struct_input_sorts or struct_funs:
            adt_fallback.append((var, sort))

    if adt_fallback:
        preferred = [(v, s) for v, s in adt_fallback if s in struct_input_sorts]
        pool = preferred or list(adt_fallback)
        return _best_adt_induct_var(pool, matrix, struct_funs, rec_positions)

    # Int Peano when goal-related Int recursion uses the binder.
    int_ok = _int_binders_used_by_int_recursion(profile, binders, matrix)
    for var, sort in binders:
        if sort in _INT_SORTS and var in int_ok:
            return (var, sort)

    return None


def validate_scheme(
    obligations: Sequence[SchemeObligation],
    *,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
    profile: Optional[ProblemProfile] = None,
) -> Tuple[bool, List[str]]:
    """Structural checks only — no solver gate ``base∧step ⊢ G``."""
    errors: List[str] = []
    if not obligations:
        return False, ["empty"]

    binder_vars = {v for v, _ in binders}
    if var not in binder_vars:
        errors.append(f"var_not_in_binders:{var}")

    ctor_arities: Dict[str, List[str]] = {}
    if profile is not None:
        ctor_arities = {
            str(k): list(v or [])
            for k, v in (profile.signature.get("constructor_arities") or {}).items()
        }

    for obl in obligations:
        obl.validate_errors = []
        if not obl.formula or not obl.formula.strip().startswith("("):
            errors.append(f"illformed:{obl.obl_id}")
            obl.validate_errors.append("illformed")
            continue

        if obl.kind == "measure":
            # Measure obligations are not ctor substitutions of the matrix.
            continue

        # Non-nullary constructors must appear applied, never as bare constants.
        ar = ctor_arities.get(obl.ctor)
        if ar is None:
            # Int Peano uses synthetic ctors 0 / (+ 1 _).
            ar = [] if obl.ctor == _INT_BASE else (
                ["Int"] if obl.ctor == _INT_STEP else None
            )
        if ar is not None and len(ar) > 0:
            term = (obl.inst_term or obl.ctor).strip()
            if not term.startswith("("):
                errors.append(f"bare_ctor:{obl.obl_id}:{obl.ctor}")
                obl.validate_errors.append("bare_ctor")
            elif obl.ctor not in term:
                errors.append(f"ctor_missing_in_term:{obl.obl_id}")
                obl.validate_errors.append("ctor_missing_in_term")

        if not _matrix_consistent(obl, binders, matrix, var):
            errors.append(f"subst_mismatch:{obl.obl_id}")
            obl.validate_errors.append("subst_mismatch")

    measure_only = bool(obligations) and all(o.kind == "measure" for o in obligations)
    if measure_only:
        kinds = {o.ctor for o in obligations}
        bridge_ctors = kinds - {"nonneg", "wf"}
        if not bridge_ctors:
            # Abstract WF retired; measure schemes must carry concrete bridges.
            errors.append("missing_measure_bridges")
            return (len(errors) == 0), errors
        return (len(errors) == 0), errors

    if sort in _INT_SORTS:
        kinds = {(o.kind, o.ctor) for o in obligations}
        if ("base", _INT_BASE) not in kinds:
            errors.append("missing_base@0")
        if ("step", _INT_STEP) not in kinds:
            errors.append("missing_step@+1")
    else:
        expected = set()
        if profile is not None:
            dt_ctors = dict(profile.signature.get("datatype_constructors") or {})
            expected = set(dt_ctors.get(sort) or [])
            if not expected:
                for c, ar in ctor_arities.items():
                    if not ar or sort in ar:
                        expected.add(c)
        covered = {o.ctor for o in obligations}
        if expected and not expected.issubset(covered):
            missing = sorted(expected - covered)
            errors.append("incomplete_ctors:" + ",".join(missing))
        # Must not claim success with zero obligations for a non-empty datatype.
        if expected and not obligations:
            errors.append("empty_cover")

    return (len(errors) == 0), errors


def _generate_adt(
    profile: ProblemProfile,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
) -> List[SchemeObligation]:
    ctor_arities: Dict[str, List[str]] = dict(
        profile.signature.get("constructor_arities") or {}
    )
    dt_ctors: Dict[str, List[str]] = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    allowed = list(dt_ctors.get(sort) or [])
    if not allowed:
        for c, ar in sorted(ctor_arities.items()):
            if not ar or sort in ar:
                allowed.append(c)
    out: List[SchemeObligation] = []
    for ctor in allowed:
        arg_sorts = list(ctor_arities.get(ctor) or [])
        if sort not in arg_sorts:
            # Non-recursive ctor on ``sort``: still apply foreign-sort args
            # (e.g. Z.P : Nat → Z must become ``(P _b0)``, never bare ``P``).
            formula, inst_term = _make_base_formula(
                binders, matrix, var, ctor, arg_sorts,
            )
            out.append(SchemeObligation(
                obl_id=f"base_{ctor}",
                kind="base",
                ctor=ctor,
                formula=formula,
                induct_var=var,
                induct_sort=sort,
                inst_term=inst_term,
            ))
            continue
        formula, inst_term = _make_step_formula(
            binders, matrix, var, sort, ctor, arg_sorts,
        )
        if not formula:
            continue
        out.append(SchemeObligation(
            obl_id=f"step_{ctor}",
            kind="step",
            ctor=ctor,
            formula=formula,
            induct_var=var,
            induct_sort=sort,
            inst_term=inst_term,
        ))
    _ = MAX_VARS
    return out


def _generate_int(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
) -> List[SchemeObligation]:
    base_f = _instantiate_goal(binders, matrix, var, _INT_BASE)
    step_f, step_term = _make_int_step_formula(binders, matrix, var)
    out = [
        SchemeObligation(
            obl_id="base_0",
            kind="base",
            ctor=_INT_BASE,
            formula=base_f,
            induct_var=var,
            induct_sort=sort,
            inst_term=_INT_BASE,
        ),
    ]
    if step_f:
        out.append(SchemeObligation(
            obl_id="step_s",
            kind="step",
            ctor=_INT_STEP,
            formula=step_f,
            induct_var=var,
            induct_sort=sort,
            inst_term=step_term,
        ))
    return out


def _fresh_name(prefix: str, used: Set[str]) -> str:
    name = prefix
    n = 0
    while name in used:
        n += 1
        name = f"{prefix}_{n}"
    used.add(name)
    return name


def _make_base_formula(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    ctor: str,
    arg_sorts: Sequence[str],
) -> Tuple[str, str]:
    """Case obligation for a non-recursive constructor (possibly with args)."""
    used = {v for v, _ in binders}
    fresh_args: List[str] = []
    fresh_binders: List[Tuple[str, str]] = []
    for i, asort in enumerate(arg_sorts):
        name = _fresh_name(f"_b{i}", used)
        fresh_args.append(name)
        fresh_binders.append((name, asort))
    inst_term = f"({ctor} {' '.join(fresh_args)})" if fresh_args else ctor
    body = _subst_free(matrix, {var: inst_term})
    outer = [(v, s) for v, s in binders if v != var] + fresh_binders
    if not outer:
        return normalize_lemma_formula(body), inst_term
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in outer)
    return normalize_lemma_formula(f"(forall ({parts}) {body})"), inst_term


def _make_int_step_formula(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
) -> Tuple[Optional[str], str]:
    ih = matrix
    step_term = f"(+ 1 {var})"
    concl = _subst_free(matrix, {var: step_term})
    body = f"(=> {ih} {concl})"
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in binders)
    return normalize_lemma_formula(f"(forall ({parts}) {body})"), step_term


def _make_step_formula(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    sort: str,
    ctor: str,
    arg_sorts: Sequence[str],
) -> Tuple[Optional[str], str]:
    """``(forall (…) (=> (and P[t_i]…) P[C(...)]))`` for recursive positions."""
    used = {v for v, _ in binders}
    fresh_args: List[str] = []
    fresh_binders: List[Tuple[str, str]] = []
    rec_vars: List[str] = []
    for i, asort in enumerate(arg_sorts):
        name = _fresh_name(f"_ih{i}", used)
        fresh_args.append(name)
        fresh_binders.append((name, asort))
        if asort == sort:
            rec_vars.append(name)
    if not rec_vars:
        return None, ""
    ctor_term = f"({ctor} {' '.join(fresh_args)})" if fresh_args else ctor
    ihs = [_subst_free(matrix, {var: rv}) for rv in rec_vars]
    if len(ihs) == 1:
        ih_body = ihs[0]
    else:
        ih_body = "(and " + " ".join(ihs) + ")"
    concl = _subst_free(matrix, {var: ctor_term})
    body = f"(=> {ih_body} {concl})"
    outer = [(v, s) for v, s in binders if v != var] + fresh_binders
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in outer)
    return normalize_lemma_formula(f"(forall ({parts}) {body})"), ctor_term


def _instantiate_goal(
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
    term: str,
) -> str:
    body = _subst_free(matrix, {var: term})
    kept = [(v, s) for v, s in binders if v != var]
    if not kept:
        return normalize_lemma_formula(body)
    parts = " ".join(f"({v} {s})" if s else f"({v})" for v, s in kept)
    return normalize_lemma_formula(f"(forall ({parts}) {body})")


def _peel_forall_body(formula: str) -> str:
    text = (formula or "").strip()
    if not text.startswith("("):
        return text
    head, args = sexpr_head_args(text)
    if head == "forall" and args:
        return args[-1]
    return text


def _matrix_consistent(
    obl: SchemeObligation,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    var: str,
) -> bool:
    """Obligation body must be matrix[var:=inst] (step: under a top-level =>)."""
    body = _peel_forall_body(obl.formula or "")
    inst = (obl.inst_term or obl.ctor).strip()
    if not inst:
        return False
    expected = _subst_free(matrix, {var: inst})
    if obl.kind == "base":
        # Do NOT peel => — the whole matrix instance is the base obligation.
        return _formulas_alpha_eq_matrix(body, expected)
    # step: (=> IH* concl) with concl == matrix[var:=ctor_term]
    bh, ba = sexpr_head_args(body) if body.strip().startswith("(") else (None, [])
    if bh not in ("=>", "implies") or len(ba) < 2:
        return False
    concl = ba[-1]
    if not _formulas_alpha_eq_matrix(concl, expected):
        return False
    # IH side must mention at least one recursive subterm variable (_ih*).
    ih = ba[0]
    return "_ih" in ih or var in ih


def _formulas_alpha_eq_matrix(left: str, right: str) -> bool:
    a = normalize_lemma_formula(left)
    b = normalize_lemma_formula(right)
    return bool(a) and a == b


def _goal_raw(profile: ProblemProfile) -> Optional[str]:
    gid = profile.goal_formula_id
    for rec in profile.formulas:
        if rec.formula_id == gid or rec.role == "goal":
            raw = rec.raw or ""
            # Goals are often stored as the positive forall (profiler peels not).
            return raw
    return None


def _goal_symbols(profile: ProblemProfile) -> Set[str]:
    gid = profile.goal_formula_id
    for rec in profile.formulas:
        if rec.formula_id == gid or rec.role == "goal":
            return set(rec.symbols)
    return set()


def _structural_funs(profile: ProblemProfile) -> Set[str]:
    out: Set[str] = set()
    for fact in profile.recursion_structure:
        if fact.kind == "structural_recursion":
            for f in fact.function.split("/"):
                if f:
                    out.add(f)
    return out


def _nonstructural_funs(profile: ProblemProfile) -> Set[str]:
    out: Set[str] = set()
    for fact in profile.recursion_structure:
        if fact.kind in ("recursive_call", "other_decreasing_recursion"):
            # other_decreasing may still be Int Peano — not ADT non-structural.
            if fact.kind == "other_decreasing_recursion":
                continue
            for f in fact.function.split("/"):
                if f:
                    out.add(f)
    return out


def _sort_is_nonstructural_only(
    profile: ProblemProfile,
    sort: str,
    goal_syms: Set[str],
) -> bool:
    """True when goal-related recursion on ``sort`` is only recursive_call."""
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    saw_struct = False
    saw_nonstruct = False
    for fact in profile.recursion_structure:
        funs = [f for f in fact.function.split("/") if f]
        if goal_syms and not any(f in goal_syms for f in funs):
            continue
        touches = False
        for f in funs:
            meta = fun_sorts.get(f) or {}
            inputs = [str(s) for s in (meta.get("input_sorts") or [])]
            if sort in inputs:
                touches = True
                break
        if not touches:
            continue
        if fact.kind == "structural_recursion":
            saw_struct = True
        elif fact.kind == "recursive_call":
            saw_nonstruct = True
    return saw_nonstruct and not saw_struct
