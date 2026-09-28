"""Recursion / observer / goal-relation analysis on a ProblemProfile."""

from __future__ import annotations

from typing import Dict, List, Optional, Set

from smt_patterns import equality_lhs, sexpr_head_args

from .types import (
    GoalRelation,
    ObserverCandidate,
    ProblemProfile,
    RecursionFact,
)


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
    # Per function: equations with self-call, and those with ctor pattern on LHS.
    recursive_eqs: Dict[str, List[str]] = {}
    ctor_eqs: Dict[str, List[str]] = {}
    structural_eqs: Dict[str, List[str]] = {}  # same equation: ctor LHS + self-call
    ctor_names_used: Dict[str, Set[str]] = {}

    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        # Library lemmas are properties, not defining equations.
        if rec.role_source == "lemma_library":
            continue
        lhs = equality_lhs(rec.raw)
        if not lhs:
            continue
        head, args = sexpr_head_args(lhs) if lhs.startswith("(") else (lhs, [])
        if not head:
            continue
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

    all_funs = sorted({*recursive_eqs.keys(), *ctor_eqs.keys()})
    for fun in all_funs:
        rec_ids = recursive_eqs.get(fun) or []
        ctor_ids = ctor_eqs.get(fun) or []
        struct_ids = structural_eqs.get(fun) or []
        # Structural: same-eq ctor+rec, or base ctor cases + separate recursive eq.
        if struct_ids or (rec_ids and ctor_ids):
            fids = sorted(set(struct_ids) | set(rec_ids) | set(ctor_ids))
            used = sorted(ctor_names_used.get(fun) or [])
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
            # Also note multi-ctor case split when ≥2 distinct ctors appear on LHS.
            if len(used) >= 2:
                facts.append(RecursionFact(
                    function=fun,
                    kind="constructor_case_split",
                    source_formula_ids=sorted(set(ctor_ids)),
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
                detail="self-call with pred/succ/- style argument",
            ))
        else:
            facts.append(RecursionFact(
                function=fun,
                kind="recursive_call",
                source_formula_ids=sorted(set(rec_ids)),
                evidence_level="structural",
                detail="self-call present; decrease pattern not established",
            ))

    # Mutual recursion: two functions each call the other in defining equations.
    funs = [f for f, ids in recursive_eqs.items() if ids]
    calls_map: Dict[str, Set[str]] = {f: set() for f in funs}
    for rec in profile.formulas:
        if rec.role == "goal":
            continue
        # Library lemmas are properties, not defining equations.
        if rec.role_source == "lemma_library":
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
        raw = rec.raw
        if any(tok in raw for tok in (f"({fun} (pred ", f"({fun} (- ", f"({fun} (suc")):
            return True
    return False


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
        # Library lemmas are properties, not defining equations.
        if rec.role_source == "lemma_library":
            continue
        lhs = equality_lhs(rec.raw)
        if not lhs:
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
        # Observer: ADT domain to a *different* sort (Nat/Int/Bool/other ADT).
        # Peano Nat is itself an ADT — still a valid observer return for lists.
        if any(s == ret for s in inputs):
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
        if r.kind in ("structural_recursion", "recursive_call", "other_decreasing_recursion")
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
