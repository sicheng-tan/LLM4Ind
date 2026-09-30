"""Recursion / observer / goal-relation analysis on a ProblemProfile."""

from __future__ import annotations

from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

from smt_patterns import equality_lhs, forall_matrix, peel_implication, sexpr_head_args

from .types import (
    GoalRelation,
    ObserverCandidate,
    ProblemProfile,
    RecursionFact,
)

_LOGIC = frozenset({
    "=", "not", "and", "or", "=>", "implies", "ite", "true", "false",
    "forall", "exists", "let", "!", "_", "match", "as", "par",
    "+", "-", "*", "div", "mod", "<", ">", "<=", ">=",
})


def enrich_profile(profile: ProblemProfile) -> ProblemProfile:
    """Fill recursion_structure, observer_candidates, goal_relations in place."""
    constructors: Set[str] = set(profile.signature.get("constructors") or [])
    fun_sorts: Dict[str, dict] = dict(profile.signature.get("fun_sorts") or {})
    datatypes: Set[str] = set(profile.signature.get("datatypes") or [])

    profile.recursion_structure = _analyze_recursion(profile, constructors)
    profile.observer_candidates = _analyze_observers(profile, fun_sorts, datatypes)
    refresh_goal_dependent_facts(profile)
    return profile


def refresh_goal_dependent_facts(profile: ProblemProfile) -> ProblemProfile:
    """Recompute relations, induction attempts, function links (after goal/library merge)."""
    from .function_links import analyze_function_links
    from .induction_attempts import analyze_induction_attempts

    profile.goal_relations = _analyze_relations(profile)
    profile.induction_attempts = analyze_induction_attempts(profile)
    profile.function_links = analyze_function_links(profile)
    return profile


def _goal_symbols(profile: ProblemProfile) -> Set[str]:
    gid = profile.goal_formula_id
    for rec in profile.formulas:
        if rec.formula_id == gid or rec.role == "goal":
            return set(rec.symbols)
    return set()


def _analyze_recursion(
    profile: ProblemProfile, constructors: Set[str],
) -> List[RecursionFact]:
    facts: List[RecursionFact] = []
    selectors: Set[str] = set(profile.signature.get("selectors") or [])
    selector_to_ctor: Dict[str, str] = {
        str(k): str(v)
        for k, v in (profile.signature.get("selector_to_ctor") or {}).items()
    }
    if not selectors and selector_to_ctor:
        selectors = set(selector_to_ctor.keys())
    datatype_ctors: Dict[str, List[str]] = {
        str(k): [str(x) for x in (v or [])]
        for k, v in (profile.signature.get("datatype_constructors") or {}).items()
    }
    fun_sorts: Dict[str, dict] = dict(profile.signature.get("fun_sorts") or {})
    declared = set(profile.signature.get("functions") or []) | selectors

    # Per function: equations with self-call, and those with ctor pattern on LHS.
    recursive_eqs: Dict[str, List[str]] = {}
    ctor_eqs: Dict[str, List[str]] = {}
    structural_eqs: Dict[str, List[str]] = {}  # same equation: ctor LHS + self-call
    selector_struct_eqs: Dict[str, List[str]] = {}
    ctor_names_used: Dict[str, Set[str]] = {}

    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        # Library / attempt lemmas are properties, not defining equations.
        if rec.role_source in ("lemma_library", "attempt_feedback"):
            continue

        # D: non-equality clauses (pref nil x) / (not (pref (cons…) nil)) still
        # contribute constructor coverage for case_split notes.
        for head, ctors in _clause_ctor_patterns(rec.raw, constructors, declared):
            if not ctors:
                continue
            ctor_eqs.setdefault(head, []).append(rec.formula_id)
            ctor_names_used.setdefault(head, set()).update(ctors)

        lhs = equality_lhs(rec.raw)
        if not lhs:
            continue
        head, args = sexpr_head_args(lhs) if lhs.startswith("(") else (lhs, [])
        if not head:
            continue
        declared.add(head)
        calls = _count_head_apps(rec.raw, head)
        has_rec = calls >= 2
        ctor_args = [a for a in args if _is_ctor_pattern(a, constructors)]
        has_ctor = bool(ctor_args)
        if has_rec:
            recursive_eqs.setdefault(head, []).append(rec.formula_id)
        if has_ctor:
            ctor_eqs.setdefault(head, []).append(rec.formula_id)
            for a in ctor_args:
                cname = _ctor_name(a, constructors)
                if cname:
                    ctor_names_used.setdefault(head, set()).add(cname)
        if has_rec and has_ctor:
            structural_eqs.setdefault(head, []).append(rec.formula_id)

        # A: selector/tester style — (= (f x y) (ite (is-S x) … (f (p x) y) …))
        lhs_vars = [
            a.strip() for a in args
            if a and not str(a).startswith("(") and a not in constructors
        ]
        if has_rec and lhs_vars and selectors:
            testers = _find_tester_apps(rec.raw, constructors)
            tester_ctors = {
                ctor for ctor, var in testers if var in lhs_vars
            }
            if tester_ctors and _has_selector_self_call(
                rec.raw, head, selectors, lhs_vars,
            ):
                selector_struct_eqs.setdefault(head, []).append(rec.formula_id)
                ctor_names_used.setdefault(head, set()).update(tester_ctors)
                # ite with one is-C and an else branch covers the other ctors.
                scrutinee_sorts = _arg_sorts_for_vars(head, args, lhs_vars, fun_sorts)
                for sort in scrutinee_sorts:
                    dt = datatype_ctors.get(sort) or []
                    if len(dt) >= 2:
                        ctor_names_used.setdefault(head, set()).update(dt)

    all_funs = sorted({
        *recursive_eqs.keys(),
        *ctor_eqs.keys(),
        *selector_struct_eqs.keys(),
    })
    for fun in all_funs:
        rec_ids = recursive_eqs.get(fun) or []
        ctor_ids = ctor_eqs.get(fun) or []
        struct_ids = structural_eqs.get(fun) or []
        sel_ids = selector_struct_eqs.get(fun) or []
        # Structural: classic ctor-LHS, or selector/tester style, or base+rec split.
        if struct_ids or sel_ids or (rec_ids and ctor_ids):
            fids = sorted(set(struct_ids) | set(sel_ids) | set(rec_ids) | set(ctor_ids))
            used = sorted(ctor_names_used.get(fun) or [])
            if sel_ids and not struct_ids:
                detail = "selector/tester defining equation with self-call"
            else:
                detail = "LHS constructor pattern with self-call in defining equations"
            if used:
                detail += f"; constructors={', '.join(used)}"
            facts.append(RecursionFact(
                function=fun,
                kind="structural_recursion",
                source_formula_ids=fids,
                evidence_level="structural",
                detail=detail,
            ))
            if len(used) >= 2:
                facts.append(RecursionFact(
                    function=fun,
                    kind="constructor_case_split",
                    source_formula_ids=sorted(set(ctor_ids) | set(sel_ids)),
                    evidence_level="structural",
                    detail=f"defining equations cover constructors {', '.join(used)}",
                ))
            continue
        if not rec_ids:
            continue
        if _looks_numeric_decrease(profile, fun):
            facts.append(RecursionFact(
                function=fun,
                kind="other_decreasing_recursion",
                source_formula_ids=sorted(set(rec_ids)),
                evidence_level="heuristic",
                detail="self-call with pred/succ/-/(+ 1 n) style argument",
            ))
        else:
            bridges = _bridge_symbols_for_fun(
                profile, fun, selectors, constructors,
            )
            detail = (
                "self-call not on constructor selectors "
                "(structural induction on the argument does not unfold this definition)"
            )
            if bridges:
                detail += f"; recursive args mention {', '.join(bridges)}"
            facts.append(RecursionFact(
                function=fun,
                kind="recursive_call",
                source_formula_ids=sorted(set(rec_ids)),
                evidence_level="structural",
                detail=detail,
                bridge_peers=bridges,
            ))

    # Mutual recursion: two functions each call the other in defining equations.
    funs = [f for f, ids in recursive_eqs.items() if ids]
    calls_map: Dict[str, Set[str]] = {f: set() for f in funs}
    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        if rec.role_source in ("lemma_library", "attempt_feedback"):
            continue
        lhs = equality_lhs(rec.raw)
        if not lhs:
            continue
        head, _ = sexpr_head_args(lhs) if lhs.startswith("(") else (lhs, [])
        if head not in calls_map:
            continue
        for sym in rec.symbols:
            if sym != head and sym in calls_map:
                calls_map[head].add(sym)
    seen_pairs: Set[tuple] = set()
    for a in funs:
        for b in calls_map.get(a, ()):
            if a in calls_map.get(b, ()) and a < b and (a, b) not in seen_pairs:
                seen_pairs.add((a, b))
                facts.append(RecursionFact(
                    function=f"{a}/{b}",
                    kind="mutual_recursion",
                    source_formula_ids=[],
                    evidence_level="structural",
                    detail=f"{a} and {b} call each other",
                ))
    return facts


def _arg_sorts_for_vars(
    fun: str,
    args: List[str],
    vars_: List[str],
    fun_sorts: Dict[str, dict],
) -> List[str]:
    meta = fun_sorts.get(fun) or {}
    input_sorts = [str(s) for s in (meta.get("input_sorts") or [])]
    out: List[str] = []
    for i, a in enumerate(args):
        if a in vars_ and i < len(input_sorts) and input_sorts[i]:
            out.append(input_sorts[i])
    return out


def _expand_lets(expr: str) -> str:
    """Substitute ``(let ((x e)…) body)`` bindings (best-effort, non-shadowing)."""
    text = (expr or "").strip()
    if not text.startswith("("):
        return text
    head, args = sexpr_head_args(text)
    if head == "let" and len(args) >= 2:
        bindings_blob = args[0]
        body = args[-1]
        mapping: Dict[str, str] = {}
        for item in _parse_binding_list(bindings_blob):
            if not item.startswith("("):
                continue
            bh, ba = sexpr_head_args(item)
            if bh and ba:
                mapping[bh.strip()] = _expand_lets(ba[0])
        expanded_body = _expand_lets(body)
        return _subst_free_vars(expanded_body, mapping)
    new_args = [_expand_lets(a) for a in args]
    if head is None:
        return text
    return "(" + " ".join([head] + new_args) + ")"


def _parse_binding_list(blob: str) -> List[str]:
    text = (blob or "").strip()
    if not text:
        return []
    if not text.startswith("("):
        return [text]
    inner = text[1:-1].strip() if text.endswith(")") else text[1:].strip()
    from smt_patterns import read_sexpr
    out: List[str] = []
    j = 0
    while True:
        tok, j = read_sexpr(inner, j)
        if tok is None:
            break
        out.append(tok)
    return out


def _subst_free_vars(expr: str, mapping: Dict[str, str]) -> str:
    text = (expr or "").strip()
    if not text:
        return text
    if not text.startswith("("):
        return mapping.get(text, text)
    head, args = sexpr_head_args(text)
    if head is None:
        return text
    if head in ("forall", "exists", "let") and args:
        # Do not substitute under binders; expand lets separately.
        return "(" + " ".join([head] + [_subst_free_vars(a, mapping) for a in args]) + ")"
    return "(" + " ".join([head] + [_subst_free_vars(a, mapping) for a in args]) + ")"


def _bridge_symbols_for_fun(
    profile: ProblemProfile,
    fun: str,
    selectors: Set[str],
    constructors: Set[str],
) -> List[str]:
    """Heads mentioned in self-call args that are not ctor selectors (e.g. filter)."""
    bridges: Set[str] = set()
    for rec in profile.formulas:
        if rec.role == "goal" or rec.role_source in ("lemma_library", "attempt_feedback"):
            continue
        if fun not in rec.symbols:
            continue
        raw = _expand_lets(rec.raw)
        bridges.update(
            _bridge_heads_in_self_calls(raw, fun, selectors, constructors)
        )
    return sorted(bridges)


def _bridge_heads_in_self_calls(
    expr: str,
    fun: str,
    selectors: Set[str],
    constructors: Set[str],
) -> Set[str]:
    found: Set[str] = set()

    def peel(arg: str) -> None:
        t = (arg or "").strip()
        if not t.startswith("("):
            return
        h, a = sexpr_head_args(t)
        if not h:
            return
        if h in selectors:
            for sub in a:
                peel(sub)
            return
        if h in constructors or h in _LOGIC or h == fun:
            for sub in a:
                peel(sub)
            return
        found.add(h)

    def walk(text: str) -> None:
        text = (text or "").strip()
        if not text.startswith("("):
            return
        head, args = sexpr_head_args(text)
        if head == fun:
            for a in args:
                peel(a)
        for a in args:
            walk(a)

    walk(expr)
    return found


def _clause_ctor_patterns(
    formula: str,
    constructors: Set[str],
    declared: Set[str],
) -> List[Tuple[str, List[str]]]:
    """Collect (head, ctor-names) from atoms, including non-equality clauses."""
    out: List[Tuple[str, List[str]]] = []
    for atom in _iter_atoms(formula):
        text = (atom or "").strip()
        if not text.startswith("("):
            continue
        head, args = sexpr_head_args(text)
        if head == "=" and len(args) >= 1:
            lhs = args[0].strip()
            if lhs.startswith("("):
                head, args = sexpr_head_args(lhs)
            else:
                continue
        if not head or head in _LOGIC:
            continue
        if declared and head not in declared and head not in constructors:
            # Still accept unknown heads that look like defined symbols.
            pass
        ctors = []
        for a in args:
            cname = _ctor_name(a, constructors)
            if cname:
                ctors.append(cname)
        if ctors:
            out.append((head, ctors))
    return out


def _iter_atoms(formula: str) -> Iterable[str]:
    body = peel_implication(forall_matrix(formula or ""))
    yield from _walk_bool(body)


def _walk_bool(expr: str) -> Iterable[str]:
    text = (expr or "").strip()
    if not text:
        return
    if not text.startswith("("):
        yield text
        return
    head, args = sexpr_head_args(text)
    if head in ("and", "or"):
        for a in args:
            yield from _walk_bool(a)
        return
    if head == "not" and args:
        yield from _walk_bool(args[0])
        return
    if head in ("=>", "implies") and len(args) >= 2:
        for a in args:
            yield from _walk_bool(a)
        return
    yield text


def _find_tester_apps(
    expr: str, constructors: Set[str],
) -> List[Tuple[str, str]]:
    """Return (ctor, scrutinee) for ``(is-C t)`` and ``((_ is C) t)``."""
    found: List[Tuple[str, str]] = []

    def walk(text: str) -> None:
        text = (text or "").strip()
        if not text.startswith("("):
            return
        head, args = sexpr_head_args(text)
        if head is None:
            return
        # (is-S x)
        if (
            isinstance(head, str)
            and head.startswith("is-")
            and len(head) > 3
            and len(args) == 1
        ):
            ctor = head[3:]
            if ctor in constructors or not constructors:
                scr = args[0].strip()
                if scr and not scr.startswith("("):
                    found.append((ctor, scr))
        # ((_ is S) x)
        if head.startswith("(") and len(args) == 1:
            ih, ia = sexpr_head_args(head)
            if ih == "_" and len(ia) >= 2 and ia[0].strip() == "is":
                ctor = ia[1].strip()
                if ctor in constructors or not constructors:
                    scr = args[0].strip()
                    if scr and not scr.startswith("("):
                        found.append((ctor, scr))
        for a in args:
            walk(a)
        if head.startswith("("):
            walk(head)

    walk(expr)
    return found


def _has_selector_self_call(
    expr: str,
    fun: str,
    selectors: Set[str],
    scrutinee_vars: List[str],
) -> bool:
    """True if a self-call passes ``(sel v)`` for selector sel and var v."""
    vars_ = set(scrutinee_vars)

    def is_sel_arg(term: str) -> bool:
        t = (term or "").strip()
        if not t.startswith("("):
            return False
        h, a = sexpr_head_args(t)
        return bool(h and h in selectors and a and a[0].strip() in vars_)

    def walk(text: str) -> bool:
        text = (text or "").strip()
        if not text.startswith("("):
            return False
        head, args = sexpr_head_args(text)
        if head == fun and any(is_sel_arg(a) for a in args):
            return True
        for a in args:
            if walk(a):
                return True
        return False

    return walk(expr)


def _count_head_apps(formula: str, head: str) -> int:
    # Cheap count of "(head " occurrences plus standalone — enough for recursion.
    needle = f"({head} "
    return formula.count(needle) + formula.count(f"({head})")


def _ctor_name(term: str, constructors: Set[str]) -> Optional[str]:
    text = (term or "").strip()
    if not text:
        return None
    if not text.startswith("("):
        return text if text in constructors else None
    h, _ = sexpr_head_args(text)
    return h if h and h in constructors else None


def _is_ctor_pattern(term: str, constructors: Set[str]) -> bool:
    """True for nullary ctor ``nil`` / ``zero`` or application ``(cons ...)``."""
    return _ctor_name(term, constructors) is not None


def _looks_numeric_decrease(profile: ProblemProfile, fun: str) -> bool:
    for rec in profile.formulas:
        if fun not in rec.symbols:
            continue
        if rec.role == "goal" or rec.role_source in ("lemma_library", "attempt_feedback"):
            continue
        raw = rec.raw
        if any(tok in raw for tok in (
            f"({fun} (pred ", f"({fun} (- ", f"({fun} (suc",
        )):
            return True
        # B: Int Peano via (+ 1 n) / (+ n 1) on a self-call argument.
        if _fun_has_int_succ_arg(raw, fun):
            return True
        # Guarded Int recursion: (>= n 0) / (> n 0) with ≥2 apps.
        if _count_head_apps(raw, fun) >= 2 and (
            "(>= " in raw or "(> " in raw or "(<= 0 " in raw
        ):
            return True
    return False


def _fun_has_int_succ_arg(raw: str, fun: str) -> bool:
    """True if some ``(fun …)`` argument is ``(+ 1 _)`` / ``(+ _ 1)`` (nested ok)."""

    def is_succ(term: str) -> bool:
        t = (term or "").strip()
        if not t.startswith("("):
            return False
        h, a = sexpr_head_args(t)
        if h != "+" or len(a) < 2:
            return False
        # (+ 1 n) or (+ n 1) or (+ 1 (+ 1 n))
        if a[0].strip() == "1" or a[1].strip() == "1":
            return True
        return any(is_succ(x) for x in a)

    def walk(text: str) -> bool:
        text = (text or "").strip()
        if not text.startswith("("):
            return False
        head, args = sexpr_head_args(text)
        if head == fun and any(is_succ(a) for a in args):
            return True
        return any(walk(a) for a in args)

    return walk(raw)


def _analyze_observers(
    profile: ProblemProfile,
    fun_sorts: Dict[str, dict],
    datatypes: Set[str],
) -> List[ObserverCandidate]:
    out: List[ObserverCandidate] = []
    defining: Dict[str, List[str]] = {}
    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        if rec.role_source in ("lemma_library", "attempt_feedback"):
            continue
        lhs = equality_lhs(rec.raw)
        if not lhs:
            # D: atomic Bool defs still count as defining for observers.
            for atom in _iter_atoms(rec.raw):
                if not atom.startswith("("):
                    continue
                h, _a = sexpr_head_args(atom)
                if h and h not in _LOGIC:
                    defining.setdefault(h, []).append(rec.formula_id)
            continue
        head, _ = sexpr_head_args(lhs) if lhs.startswith("(") else (lhs, [])
        if head:
            defining.setdefault(head, []).append(rec.formula_id)

    for name, meta in fun_sorts.items():
        inputs = [str(x) for x in (meta.get("input_sorts") or [])]
        ret = str(meta.get("return_sort") or "")
        if not inputs or not ret:
            continue
        # ADT input → non-ADT (or Bool/Int/Nat-like) return
        adt_in = any(s in datatypes for s in inputs)
        if not adt_in:
            continue
        # Observer: ADT domain to a different *ADT-or-not* return. Exclude
        # Lst→Lst (same ADT in and out), but keep Int×Lst→Int / Lst→Nat.
        if any(s in datatypes and s == ret for s in inputs):
            continue
        fids = defining.get(name) or []
        if fids:
            level = "structural"
            detail = "defined by equations; ADT input to a different output sort"
        else:
            level = "heuristic"
            detail = "signature-only observer guess"
        out.append(ObserverCandidate(
            function=name,
            input_sorts=inputs,
            return_sort=ret,
            source_formula_ids=sorted(set(fids)),
            evidence_level=level,  # type: ignore[arg-type]
            detail=detail,
        ))
    return out


def _analyze_relations(profile: ProblemProfile) -> List[GoalRelation]:
    goal_syms = _goal_symbols(profile)
    if not goal_syms:
        return []
    gid = profile.goal_formula_id or ""
    rec_funs = {
        r.function.split("/")[0]
        for r in profile.recursion_structure
        if r.kind in (
            "structural_recursion",
            "recursive_call",
            "other_decreasing_recursion",
        )
    }
    # mutual: function field is "a/b"
    for r in profile.recursion_structure:
        if r.kind == "mutual_recursion" and "/" in r.function:
            a, b = r.function.split("/", 1)
            rec_funs.add(a)
            rec_funs.add(b)

    obs = {
        o.function
        for o in profile.observer_candidates
        if o.evidence_level in ("explicit", "structural")
    }
    rels: List[GoalRelation] = []
    hit_rec = sorted(goal_syms & rec_funs)
    hit_obs = sorted(goal_syms & obs)
    if hit_rec and hit_obs:
        fids = [gid] if gid else []
        for r in profile.recursion_structure:
            if r.function.split("/")[0] in hit_rec or any(
                p in hit_rec for p in r.function.split("/")
            ):
                fids.extend(r.source_formula_ids)
        for o in profile.observer_candidates:
            if o.function in hit_obs:
                fids.extend(o.source_formula_ids)
        rels.append(GoalRelation(
            kind="goal_mentions_recursive_function_and_observer",
            symbols=hit_rec + hit_obs,
            formula_ids=sorted({x for x in fids if x}),
            evidence_level="structural",
            detail="goal mentions both recursive function(s) and observer candidate(s)",
        ))
    elif hit_rec:
        rels.append(GoalRelation(
            kind="goal_mentions_recursive_function",
            symbols=hit_rec,
            formula_ids=[gid] if gid else [],
            evidence_level="structural",
        ))
    return rels


def structural_rec_arg_positions(
    profile: ProblemProfile,
) -> Dict[str, Set[int]]:
    """Map structural functions to 0-based argument indices they recurse on.

    Derived from defining equations (not the goal):
    - ctor-LHS: ``(= (f (C …) y) … (f …) …)`` → index of ctor-pattern args
    - selector/tester: ``(= (f x y) (ite (is-C x) … (f (sel x) y) …))`` →
      indices of LHS vars that are tester scrutinees with selector self-calls
    """
    constructors: Set[str] = set(profile.signature.get("constructors") or [])
    selectors: Set[str] = set(profile.signature.get("selectors") or [])
    selector_to_ctor = {
        str(k): str(v)
        for k, v in (profile.signature.get("selector_to_ctor") or {}).items()
    }
    if not selectors and selector_to_ctor:
        selectors = set(selector_to_ctor.keys())

    struct_funs = {
        f
        for fact in profile.recursion_structure
        if fact.kind == "structural_recursion"
        for f in fact.function.split("/")
        if f
    }
    out: Dict[str, Set[int]] = {f: set() for f in struct_funs}
    if not struct_funs:
        return out

    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        if rec.role_source in ("lemma_library", "attempt_feedback"):
            continue
        lhs = equality_lhs(rec.raw)
        if not lhs:
            continue
        head, args = sexpr_head_args(lhs) if lhs.startswith("(") else (lhs, [])
        if head not in struct_funs or not args:
            continue
        calls = _count_head_apps(rec.raw, head)
        if calls < 2:
            # Base cases (no self-call) still mark ctor positions as inductive axes.
            pass

        for i, a in enumerate(args):
            if _is_ctor_pattern(a, constructors):
                out[head].add(i)

        lhs_vars = [
            a.strip() for a in args
            if a and not str(a).startswith("(") and a not in constructors
        ]
        if calls >= 2 and lhs_vars and selectors:
            # Only positions whose variable is peeled by a selector in a self-call
            # (not every is-C scrutinee — binary plus may test both args).
            peeled = _vars_peeled_in_self_calls(rec.raw, head, selectors, lhs_vars)
            for i, a in enumerate(args):
                if a.strip() in peeled:
                    out[head].add(i)

    # Fallback: single ADT-typed input → that index, when still empty.
    fun_sorts = dict(profile.signature.get("fun_sorts") or {})
    datatypes = set(profile.signature.get("datatypes") or [])
    for fun, positions in list(out.items()):
        if positions:
            continue
        meta = fun_sorts.get(fun) or {}
        inputs = [str(s) for s in (meta.get("input_sorts") or [])]
        adt_idxs = [i for i, s in enumerate(inputs) if s in datatypes]
        if len(adt_idxs) == 1:
            out[fun].add(adt_idxs[0])

    # Primary structural axis = leftmost recursive position (v1). Binary ops that
    # case-split on several ADT args still usually induct on the first.
    for fun, positions in list(out.items()):
        if len(positions) > 1:
            out[fun] = {min(positions)}
    return out


def _vars_peeled_in_self_calls(
    expr: str,
    fun: str,
    selectors: Set[str],
    scrutinee_vars: Sequence[str],
) -> Set[str]:
    """LHS vars ``v`` such that some self-call passes ``(sel v)``."""
    vars_ = set(scrutinee_vars)
    peeled: Set[str] = set()

    def walk(text: str) -> None:
        text = (text or "").strip()
        if not text.startswith("("):
            return
        head, args = sexpr_head_args(text)
        if head == fun:
            for a in args:
                t = (a or "").strip()
                if not t.startswith("("):
                    continue
                h, aa = sexpr_head_args(t)
                if h and h in selectors and aa:
                    v = aa[0].strip()
                    if v in vars_:
                        peeled.add(v)
        for a in args:
            walk(a)

    walk(expr)
    return peeled
