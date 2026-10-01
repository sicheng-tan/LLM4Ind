"""Descent + μ-homomorphism (R1/R2) bridges for measure-style schemes.

Concrete lemmas only — no abstract WF, no benchmark-named semantic templates.
R1/R2 are driven by μ's domain sort, goal/peer helpers, and constructors.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Set, Tuple

from smt_patterns import normalize_lemma_formula

from problem_profiler.types import ProblemProfile

from .types import SchemeObligation

_MEASURE_RET = frozenset({"Int", "Nat", "nat", "Natural"})
# Never treat these as μ-domain helpers for R1.
_R1_SKIP_FUNS = frozenset({
    "plus", "minus", "mult", "div", "mod", "abs", "ite",
    "and", "or", "not", "=>", "=", "<", ">", "<=", ">=",
})

# Descent helpers: name prefixes / exact tokens (keep existing TIP coverage).
_DESCENT_NAME_PREFIXES = (
    "filter", "delete", "remove", "take", "drop", "ztake", "zdrop",
    "butlast", "evens", "odds",
)
_DESCENT_NAME_EXACT = frozenset({
    "bubble", "take", "drop", "ztake", "zdrop", "delete",
})
# Never treat these as μ-nonincreasing from name alone (signature ambiguous).
_DESCENT_NAME_BLOCK = frozenset({
    "append", "concat", "union", "inter", "reverse", "rev", "snoc",
    "cons", "zcons", "++", "insort", "insert", "sinsert", "qsort",
    "isort", "msort", "ssort", "tsort", "bsort", "hsort", "nmsort",
    "sort", "merge", "zip", "map", "interleave", "rotate",
})


def _is_descent_name(name: str) -> bool:
    low = name.lower()
    if low in _DESCENT_NAME_BLOCK:
        return False
    if low in _DESCENT_NAME_EXACT:
        return True
    return any(low.startswith(p) for p in _DESCENT_NAME_PREFIXES)


def generate_bridge_obligations(
    profile: ProblemProfile,
    *,
    binders: Sequence[Tuple[str, str]],
    matrix: str,
    induct_var: str,
    induct_sort: str,
    measure_fun: str,
    measure_ret_sort: str,
    use_nat_to_int: bool,
) -> List[SchemeObligation]:
    """Concrete descent + domain bridges (no abstract WF).

    Descent peers are taken first from goal-related recursive-call analysis;
    TIP-style name heuristics are only a fallback when that set is empty.
    """
    out: List[SchemeObligation] = []
    seen: Set[str] = set()
    goal_norm = normalize_lemma_formula(
        f"(forall ({' '.join(f'({v} {s})' for v, s in binders)}) {matrix})"
    ) if binders else normalize_lemma_formula(matrix)

    def _add(obl: SchemeObligation) -> None:
        key = normalize_lemma_formula(obl.formula)
        if not key or key in seen:
            return
        # Never emit the goal itself as a "bridge".
        if goal_norm and key == goal_norm:
            return
        seen.add(key)
        out.append(obl)

    rc_descents = _descent_from_recursive_calls(
        profile,
        induct_var=induct_var,
        induct_sort=induct_sort,
        measure_fun=measure_fun,
        use_nat_to_int=use_nat_to_int,
    )
    for obl in rc_descents:
        _add(obl)
    # Name-table fallback when RC peers produced no descent obligations.
    if not rc_descents:
        for obl in _descent_known_shapes(
            profile,
            induct_var=induct_var,
            induct_sort=induct_sort,
            measure_fun=measure_fun,
            use_nat_to_int=use_nat_to_int,
        ):
            _add(obl)

    # μ domain for R1/R2: prefer the measure's input sort over induct_sort
    # (they usually match; heap measures are on Heap even if binders differ).
    mu_sort = (
        _sort_of_fun_input(dict(profile.signature.get("fun_sorts") or {}), measure_fun, 0)
        or induct_sort
    )
    for obl in _mu_homomorphism_bridges(
        profile,
        measure_fun=measure_fun,
        measure_ret_sort=measure_ret_sort,
        mu_sort=mu_sort,
        use_nat_to_int=use_nat_to_int,
    ):
        _add(obl)

    for obl in _mu_strict_descent_bridges(
        profile,
        measure_fun=measure_fun,
        mu_sort=mu_sort,
        use_nat_to_int=use_nat_to_int,
    ):
        _add(obl)

    return out


def pick_or_synthesize_measure(
    profile: ProblemProfile,
    sort: str,
) -> Tuple[Optional[str], str, str]:
    """Return ``(measure_fun, ret_sort, prelude)``.

    Prefers an existing size-like symbol. If none, synthesizes a working-copy
    measure over recursive constructors (``__scheme_list_len`` for single-spine
    list shapes; ``__scheme_adt_size`` for trees / multi-arm spines).
    """
    from .generate import select_measure_fun, _nat_to_int_prelude

    mu = select_measure_fun(profile, sort)
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    if mu:
        ret = str((fun_sorts.get(mu) or {}).get("return_sort") or "Int")
        prelude = ""
        if ret != "Int":
            prelude = _nat_to_int_prelude(profile, ret) or ""
            if not prelude:
                return None, "", ""
        return mu, ret, prelude

    synth = _synthesize_adt_size(profile, sort)
    if synth is None:
        return None, "", ""
    fun, prelude = synth
    return fun, "Int", prelude


def is_bridge_primary(obligations: Sequence[SchemeObligation]) -> bool:
    """True when measure obligations are concrete bridges (not bare WF)."""
    if not obligations:
        return False
    if any(o.kind != "measure" for o in obligations):
        return False
    return any(o.ctor not in ("nonneg", "wf") for o in obligations)


def _mu_term(measure_fun: str, arg: str, *, use_nat_to_int: bool) -> str:
    raw = f"({measure_fun} {arg})"
    if use_nat_to_int:
        return f"(__scheme_nat_to_int {raw})"
    return raw


def _obl(
    *,
    obl_id: str,
    ctor: str,
    formula: str,
    induct_var: str,
    induct_sort: str,
) -> SchemeObligation:
    return SchemeObligation(
        obl_id=obl_id,
        kind="measure",
        ctor=ctor,
        formula=normalize_lemma_formula(formula),
        induct_var=induct_var,
        induct_sort=induct_sort,
        inst_term=induct_var,
    )


def _ctor_tables(
    profile: ProblemProfile, sort: str,
) -> Tuple[List[str], Dict[str, List[str]]]:
    dt = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    ar = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("constructor_arities") or {}).items()
    }
    return list(dt.get(sort) or []), ar


def _rec_positions(arg_sorts: Sequence[str], sort: str) -> List[int]:
    return [i for i, s in enumerate(arg_sorts) if s == sort]


def _list_nil_cons(
    profile: ProblemProfile, sort: str,
) -> Optional[Tuple[str, str, str]]:
    """``(nil, cons, elem_sort)`` for a *single-spine* list-like datatype.

    Requires exactly one nullary/non-recursive ctor and one ctor with
    **exactly one** recursive argument of ``sort`` (any index). Binary trees
    ``(node T T)`` are excluded (two recursive args).
    """
    ctors, ar = _ctor_tables(profile, sort)
    if len(ctors) < 2:
        return None
    nils = [c for c in ctors if not _rec_positions(ar.get(c) or [], sort)]
    spines = [
        c for c in ctors
        if len(_rec_positions(ar.get(c) or [], sort)) == 1
    ]
    if len(nils) == 1 and len(spines) == 1 and set(nils) | set(spines) == set(ctors):
        cons = spines[0]
        args = ar.get(cons) or []
        rec = _rec_positions(args, sort)[0]
        elem_args = [args[i] for i in range(len(args)) if i != rec]
        elem = str(elem_args[0]) if elem_args else "Int"
        return nils[0], cons, elem
    for nil_n, cons_n in (("nil", "cons"), ("Nil", "Cons"), ("znil", "zcons")):
        if nil_n in ctors and cons_n in ctors:
            args = ar.get(cons_n) or []
            recs = _rec_positions(args, sort)
            if len(recs) != 1:
                continue
            rec = recs[0]
            elem_args = [args[i] for i in range(len(args)) if i != rec]
            elem = str(elem_args[0]) if elem_args else "Int"
            return nil_n, cons_n, elem
    return None


def _synthesize_list_len(
    profile: ProblemProfile, sort: str,
) -> Optional[Tuple[str, str]]:
    """Backward-compatible alias: single-spine list measure only."""
    if _list_nil_cons(profile, sort) is None:
        return None
    return _synthesize_adt_size(profile, sort)


def _smt_sum(terms: Sequence[str]) -> str:
    terms = [t for t in terms if t]
    if not terms:
        return "0"
    if len(terms) == 1:
        return terms[0]
    out = terms[0]
    for t in terms[1:]:
        out = f"(+ {out} {t})"
    return out


def _synthesize_adt_size(
    profile: ProblemProfile, sort: str,
) -> Optional[Tuple[str, str]]:
    """Synthesize a WF size over recursive constructors (working copy only).

    * Single-spine list shape → ``__scheme_list_len``
    * Otherwise (trees, Bin, …) → ``__scheme_adt_size`` with
      ``1 + Σ size(rec_i)`` on each recursive constructor.
    """
    ctors, ar = _ctor_tables(profile, sort)
    if len(ctors) < 2:
        return None
    bases = [c for c in ctors if not _rec_positions(ar.get(c) or [], sort)]
    rec_ctors = [c for c in ctors if _rec_positions(ar.get(c) or [], sort)]
    if not bases or not rec_ctors:
        return None

    list_pair = _list_nil_cons(profile, sort)
    if list_pair is not None:
        fun = "__scheme_list_len"
        tag = "list length"
    else:
        fun = "__scheme_adt_size"
        tag = "ADT size"

    lines = [
        f"; induction scheme synthesized {tag} (working copy only)",
        f"(declare-fun {fun} ({sort}) Int)",
    ]
    ordered = list(bases) + [c for c in ctors if c not in bases]
    for ctor in ordered:
        args = list(ar.get(ctor) or [])
        recs = _rec_positions(args, sort)
        binders = [f"(__a{i} {args[i]})" for i in range(len(args))]
        app_args = " ".join(f"__a{i}" for i in range(len(args)))
        app = f"({ctor})" if not args else f"({ctor} {app_args})"
        if not recs:
            eqn = f"(= ({fun} {app}) 0)"
        else:
            parts = ["1"] + [f"({fun} __a{i})" for i in recs]
            eqn = f"(= ({fun} {app}) {_smt_sum(parts)})"
        if binders:
            lines.append(
                f"(assert (forall ({' '.join(binders)}) {eqn}))"
            )
        else:
            lines.append(f"(assert {eqn})")
    return fun, "\n".join(lines) + "\n"


def _descent_from_recursive_calls(
    profile: ProblemProfile,
    *,
    induct_var: str,
    induct_sort: str,
    measure_fun: str,
    use_nat_to_int: bool,
) -> List[SchemeObligation]:
    """μ(bridge-result) ≤ μ(arg) style lemmas from recursive_call peers."""
    goal_syms = _goal_symbols(profile)
    out: List[SchemeObligation] = []
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    mu = measure_fun
    peers_seen: Set[str] = set()

    for fact in profile.recursion_structure:
        if fact.kind != "recursive_call":
            continue
        funs = [f for f in fact.function.split("/") if f]
        if goal_syms and not any(f in goal_syms for f in funs):
            continue
        peers = list(fact.bridge_peers or [])
        for fun in funs:
            for peer in peers or _infer_peers_from_eqs(profile, fun):
                if peer in peers_seen:
                    continue
                peers_seen.add(peer)
                out.extend(
                    _descent_for_peer(
                        profile,
                        peer=peer,
                        induct_var=induct_var,
                        induct_sort=induct_sort,
                        measure_fun=mu,
                        use_nat_to_int=use_nat_to_int,
                        fun_sorts=fun_sorts,
                    )
                )
    return out


def _descent_known_shapes(
    profile: ProblemProfile,
    *,
    induct_var: str,
    induct_sort: str,
    measure_fun: str,
    use_nat_to_int: bool,
) -> List[SchemeObligation]:
    """TIP-style name fallback when recursive-call peers yielded no descent."""
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    functions = set(profile.signature.get("functions") or []) | set(fun_sorts)
    out: List[SchemeObligation] = []
    for name in sorted(functions):
        if not _is_descent_name(name):
            continue
        out.extend(
            _descent_for_peer(
                profile,
                peer=name,
                induct_var=induct_var,
                induct_sort=induct_sort,
                measure_fun=measure_fun,
                use_nat_to_int=use_nat_to_int,
                fun_sorts=fun_sorts,
            )
        )
    return out


def _selectors_to_sort(
    profile: ProblemProfile,
    product_sort: str,
    elem_sort: str,
) -> List[str]:
    """Selectors / unary funs ``product_sort → elem_sort`` (e.g. Pair→list)."""
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    sel_to_ctor = {
        str(k): str(v)
        for k, v in (profile.signature.get("selector_to_ctor") or {}).items()
    }
    arities = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("constructor_arities") or {}).items()
    }
    dt = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    ctor_domain = {
        ctor: sort
        for sort, ctors in dt.items()
        for ctor in (ctors or [])
    }
    selector_order = [str(s) for s in (profile.signature.get("selectors") or [])]

    out: List[str] = []
    # From declare-datatypes selectors (may lack fun_sorts entries).
    for sel, ctor in sel_to_ctor.items():
        domain = ctor_domain.get(ctor)
        if domain != product_sort:
            continue
        args = arities.get(ctor) or []
        siblings = [s for s in selector_order if sel_to_ctor.get(s) == ctor]
        if sel not in siblings:
            siblings = sorted(s for s, c in sel_to_ctor.items() if c == ctor)
        try:
            idx = siblings.index(sel)
        except ValueError:
            continue
        if idx < len(args) and args[idx] == elem_sort:
            out.append(sel)

    # Also unary functions with explicit sorts.
    names = set(profile.signature.get("selectors") or []) | set(fun_sorts)
    for name in names:
        meta = fun_sorts.get(name) or {}
        inputs = [str(s) for s in (meta.get("input_sorts") or [])]
        ret = str(meta.get("return_sort") or "")
        if len(inputs) == 1 and inputs[0] == product_sort and ret == elem_sort:
            out.append(name)

    prefer = ("second", "snd", "proj1", "proj2", "fst", "tail")
    def _key(n: str) -> Tuple[int, str]:
        low = n.lower()
        for i, p in enumerate(prefer):
            if low == p or low.endswith(p):
                return (i, n)
        return (len(prefer), n)
    return sorted(set(out), key=_key)


def _descent_name_blocked(name: str) -> bool:
    low = name.lower()
    if low in _DESCENT_NAME_BLOCK:
        return True
    # Prefix growers (e.g. append2) — keep narrow to avoid killing filter*.
    for blocked in ("append", "concat", "merge", "qsort", "isort", "msort"):
        if low == blocked or low.startswith(blocked + "_"):
            return True
    return False


def _descent_for_peer(
    profile: ProblemProfile,
    *,
    peer: str,
    induct_var: str,
    induct_sort: str,
    measure_fun: str,
    use_nat_to_int: bool,
    fun_sorts: dict,
) -> List[SchemeObligation]:
    mu = measure_fun
    peer_meta = fun_sorts.get(peer) or {}
    peer_in = [str(s) for s in (peer_meta.get("input_sorts") or [])]
    peer_out = str(peer_meta.get("return_sort") or "")
    out: List[SchemeObligation] = []
    blocked = _descent_name_blocked(peer)

    # Same-sort transformers: μ(f(…,x,…)) ≤ μ(x) (filter / take / delete / …).
    if (
        not blocked
        and peer_out == induct_sort
        and induct_sort in peer_in
    ):
        if len(peer_in) == 2 and peer_in[-1] == induct_sort:
            p_sort = peer_in[0]
            filt = f"({peer} p xs)"
            body = (
                f"(forall ((p {p_sort}) (xs {induct_sort})) "
                f"(<= {_mu_term(mu, filt, use_nat_to_int=use_nat_to_int)} "
                f"{_mu_term(mu, 'xs', use_nat_to_int=use_nat_to_int)}))"
            )
            out.append(_obl(
                obl_id=f"descent_{peer}_le",
                ctor=f"descent_{peer}",
                formula=body,
                induct_var=induct_var,
                induct_sort=induct_sort,
            ))
        elif len(peer_in) == 1 and peer_in[0] == induct_sort:
            body = (
                f"(forall ((xs {induct_sort})) "
                f"(<= {_mu_term(mu, f'({peer} xs)', use_nat_to_int=use_nat_to_int)} "
                f"{_mu_term(mu, 'xs', use_nat_to_int=use_nat_to_int)}))"
            )
            out.append(_obl(
                obl_id=f"descent_{peer}_le",
                ctor=f"descent_{peer}",
                formula=body,
                induct_var=induct_var,
                induct_sort=induct_sort,
            ))

    # Product unwrap: f : τ → σ with selector s : σ → τ (bubble/Pair generalized).
    if (
        peer_out
        and peer_out != induct_sort
        and induct_sort in peer_in
        and len(peer_in) == 1
        and peer_in[0] == induct_sort
    ):
        for sel in _selectors_to_sort(profile, peer_out, induct_sort):
            body = (
                f"(forall ((xs {induct_sort})) "
                f"(<= {_mu_term(mu, f'({sel} ({peer} xs))', use_nat_to_int=use_nat_to_int)} "
                f"{_mu_term(mu, 'xs', use_nat_to_int=use_nat_to_int)}))"
            )
            out.append(_obl(
                obl_id=f"descent_{peer}_{sel}_le",
                ctor=f"descent_{peer}_{sel}",
                formula=body,
                induct_var=induct_var,
                induct_sort=induct_sort,
            ))
            break  # one selector is enough (prefer second/…)

    return out


def _infer_peers_from_eqs(profile: ProblemProfile, fun: str) -> List[str]:
    """Fallback peer heads mentioned in self-call args of ``fun``."""
    constructors = set(profile.signature.get("constructors") or [])
    selectors = set(profile.signature.get("selectors") or [])
    peers: Set[str] = set()
    for rec in profile.formulas:
        if rec.role == "goal" or rec.role_source in ("lemma_library", "attempt_feedback"):
            continue
        if fun not in (rec.symbols or []):
            continue
        raw = rec.raw or ""
        if f"({fun} " not in raw:
            continue
        for sym in rec.symbols or []:
            if sym == fun or sym in constructors or sym in selectors:
                continue
            if sym in ("ite", "and", "or", "not", "=>", "=", "let", "forall", "exists"):
                continue
            peers.add(sym)
    return sorted(peers)[:6]


def _mu_domain_helpers(
    profile: ProblemProfile,
    *,
    mu_sort: str,
    measure_fun: str,
) -> List[str]:
    """Same-sort binary helpers linked to the goal via peers / equations."""
    goal_syms = _goal_symbols(profile)
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    peer_names: Set[str] = set()
    for fun in sorted(goal_syms):
        peer_names.update(_infer_peers_from_eqs(profile, fun))
    for fact in profile.recursion_structure:
        if fact.kind != "recursive_call":
            continue
        funs = [f for f in fact.function.split("/") if f]
        if goal_syms and not any(f in goal_syms for f in funs):
            continue
        peer_names.update(fact.bridge_peers or [])
        for fun in funs:
            peer_names.update(_infer_peers_from_eqs(profile, fun))

    out: List[str] = []
    for name, meta in sorted(fun_sorts.items()):
        if name == measure_fun or name in _R1_SKIP_FUNS:
            continue
        low = name.lower()
        if low in _R1_SKIP_FUNS or "minimum" in low or "maximum" in low:
            continue
        inputs = [str(s) for s in (meta.get("input_sorts") or [])]
        ret = str(meta.get("return_sort") or "")
        if len(inputs) != 2 or inputs[0] != mu_sort or inputs[1] != mu_sort:
            continue
        if ret != mu_sort:
            continue
        if name in goal_syms or name in peer_names:
            out.append(name)
    return out


def _mu_nullary_ctors(profile: ProblemProfile, mu_sort: str) -> List[str]:
    dt = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    ar = {
        str(k): list(v or [])
        for k, v in (profile.signature.get("constructor_arities") or {}).items()
    }
    return [c for c in (dt.get(mu_sort) or []) if not ar.get(c)]


def _mu_guard_preds(profile: ProblemProfile, mu_sort: str) -> List[str]:
    """Unary Bool predicates on ``mu_sort`` that appear in the goal."""
    goal_syms = _goal_symbols(profile)
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    out: List[str] = []
    for name in sorted(goal_syms):
        meta = fun_sorts.get(name) or {}
        inputs = [str(s) for s in (meta.get("input_sorts") or [])]
        ret = str(meta.get("return_sort") or "")
        if len(inputs) == 1 and inputs[0] == mu_sort and ret == "Bool":
            out.append(name)
    return out


def _mu_plus_op(profile: ProblemProfile, measure_ret_sort: str) -> str:
    if measure_ret_sort == "Int":
        return "+"
    functions = set(profile.signature.get("functions") or [])
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    if "plus" in functions or "plus" in fun_sorts:
        return "plus"
    return "+"


def _mu_homomorphism_bridges(
    profile: ProblemProfile,
    *,
    measure_fun: str,
    measure_ret_sort: str,
    mu_sort: str,
    use_nat_to_int: bool,
) -> List[SchemeObligation]:
    """R1: μ(H c x)=μ(x), μ(H x y)=μ(x)⊕μ(y), optional guard / predicate preserve."""
    if not measure_fun or not mu_sort:
        return []
    helpers = _mu_domain_helpers(profile, mu_sort=mu_sort, measure_fun=measure_fun)
    if not helpers:
        return []
    nullaries = _mu_nullary_ctors(profile, mu_sort)
    guards = _mu_guard_preds(profile, mu_sort)
    plus = _mu_plus_op(profile, measure_ret_sort)
    out: List[SchemeObligation] = []

    def _mu(arg: str) -> str:
        return _mu_term(measure_fun, arg, use_nat_to_int=use_nat_to_int)

    def _sum(a: str, b: str) -> str:
        if plus == "+":
            return f"(+ {_mu(a)} {_mu(b)})"
        return f"(plus {_mu(a)} {_mu(b)})"

    def _with_guards(body: str, vars_: Sequence[str]) -> str:
        if not guards:
            return body
        parts = [f"({g} {v})" for g in guards for v in vars_]
        if len(parts) == 1:
            return f"(=> {parts[0]} {body})"
        return f"(=> (and {' '.join(parts)}) {body})"

    for H in helpers:
        tag = H.replace("-", "_")
        for c in nullaries:
            # μ(H x c) = μ(x) and μ(H c x) = μ(x)
            out.append(_obl(
                obl_id=f"mu_hom_{tag}_base_r_{c}",
                ctor="mu_hom_base",
                formula=(
                    f"(forall ((x {mu_sort})) "
                    f"(= {_mu(f'({H} x {c})')} {_mu('x')}))"
                ),
                induct_var="x",
                induct_sort=mu_sort,
            ))
            out.append(_obl(
                obl_id=f"mu_hom_{tag}_base_l_{c}",
                ctor="mu_hom_base",
                formula=(
                    f"(forall ((x {mu_sort})) "
                    f"(= {_mu(f'({H} {c} x)')} {_mu('x')}))"
                ),
                induct_var="x",
                induct_sort=mu_sort,
            ))

        step_eq = f"(= {_mu(f'({H} a b)')} {_sum('a', 'b')})"
        step_body = _with_guards(step_eq, ("a", "b"))
        out.append(_obl(
            obl_id=f"mu_hom_{tag}_step",
            ctor="mu_hom_step",
            formula=f"(forall ((a {mu_sort}) (b {mu_sort})) {step_body})",
            induct_var="a",
            induct_sort=mu_sort,
        ))

        for P in guards:
            # Predicate preservation under H (generic leftist-style companion).
            preserve = f"({P} ({H} a b))"
            body = _with_guards(preserve, ("a", "b"))
            out.append(_obl(
                obl_id=f"mu_prop_{tag}_{P}",
                ctor="mu_prop_preserve",
                formula=f"(forall ((a {mu_sort}) (b {mu_sort})) {body})",
                induct_var="a",
                induct_sort=mu_sort,
            ))

    return out


def _mu_strict_descent_bridges(
    profile: ProblemProfile,
    *,
    measure_fun: str,
    mu_sort: str,
    use_nat_to_int: bool,
) -> List[SchemeObligation]:
    """R2: μ(H l r) < μ(C … l … r …) for ctors with ≥2 recursive μ-sort args."""
    if not measure_fun or not mu_sort:
        return []
    helpers = _mu_domain_helpers(profile, mu_sort=mu_sort, measure_fun=measure_fun)
    if not helpers:
        return []
    dt = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    ar = {
        str(k): list(v or [])
        for k, v in (profile.signature.get("constructor_arities") or {}).items()
    }
    out: List[SchemeObligation] = []

    def _mu(arg: str) -> str:
        return _mu_term(measure_fun, arg, use_nat_to_int=use_nat_to_int)

    for ctor in dt.get(mu_sort) or []:
        args = [str(s) for s in (ar.get(ctor) or [])]
        rec_idxs = [i for i, s in enumerate(args) if s == mu_sort]
        if len(rec_idxs) < 2:
            continue
        # Quantify all ctor args; compare H on first two recursive positions.
        binders = []
        terms = []
        for i, s in enumerate(args):
            v = f"_a{i}"
            binders.append(f"({v} {s})")
            terms.append(v)
        i0, i1 = rec_idxs[0], rec_idxs[1]
        left = terms[i0]
        right = terms[i1]
        ctor_term = f"({ctor} {' '.join(terms)})" if terms else ctor
        for H in helpers:
            tag = H.replace("-", "_")
            body = (
                f"(forall ({' '.join(binders)}) "
                f"(< {_mu(f'({H} {left} {right})')} {_mu(ctor_term)}))"
            )
            out.append(_obl(
                obl_id=f"mu_lt_{tag}_{ctor}",
                ctor="mu_lt",
                formula=body,
                induct_var=left,
                induct_sort=mu_sort,
            ))
    return out


def bridge_role(ctor: str) -> str:
    """Classify measure obligation for prompts: descent | semantic | side."""
    c = (ctor or "").strip()
    if c in ("nonneg", "wf"):
        return "side"
    if (
        c.startswith("descent_")
        or c.endswith("_le")
        or c == "mu_lt"
        or "merge_lt" in c
    ):
        return "descent"
    if (
        c.startswith("mu_hom_")
        or c.startswith("mu_prop_")
        or c.startswith("semantic_")
        or c.startswith("sort_")
        or c.startswith("heap_")
    ):
        return "semantic"
    return "other"


def _goal_symbols(profile: ProblemProfile) -> Set[str]:
    for rec in profile.formulas:
        if rec.formula_id == profile.goal_formula_id or rec.role == "goal":
            return set(rec.symbols or [])
    return set()


def _sort_of_fun_input(fun_sorts: dict, fun: str, idx: int) -> Optional[str]:
    meta = fun_sorts.get(fun) or {}
    inputs = [str(s) for s in (meta.get("input_sorts") or [])]
    if 0 <= idx < len(inputs):
        return inputs[idx]
    return None


def _ret(fun_sorts: dict, fun: str) -> str:
    return str((fun_sorts.get(fun) or {}).get("return_sort") or "")
