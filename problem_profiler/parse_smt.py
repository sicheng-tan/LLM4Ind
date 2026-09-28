"""SMT-LIB2 formula index, signature, and goal registration."""

from __future__ import annotations

import re
from typing import Dict, List, Optional, Set, Tuple

from smt_patterns import normalize_lemma_formula, read_sexpr, sexpr_head_args

from .types import FormulaRecord, ProblemProfile

_PROOF_GOAL_BLOCK = re.compile(
    r";\s*proof goal\b[^\n]*\n(?P<body>.*?);\s*proof goal end\b",
    re.IGNORECASE | re.DOTALL,
)

_SKIP_HEADS = frozenset({
    "set-logic", "set-option", "set-info", "check-sat", "exit",
    "get-proof", "get-model", "get-unsat-core", "echo",
})

_BUILTIN = frozenset({
    "=", "not", "and", "or", "=>", "implies", "ite", "true", "false",
    "forall", "exists", "let", "!", "_", "match", "as", "par",
    "+", "-", "*", "div", "mod", "<", ">", "<=", ">=",
})


def _parse_sort_list(blob: str) -> List[str]:
    text = (blob or "").strip()
    if not text or text == "()":
        return []
    if not text.startswith("("):
        return [text]
    inner = text[1:-1].strip() if text.endswith(")") else text[1:].strip()
    out: List[str] = []
    j = 0
    while True:
        tok, j = read_sexpr(inner, j)
        if tok is None:
            break
        out.append(tok.strip())
    return out


def collect_symbols(expr: str) -> List[str]:
    """Function / constant identifiers appearing in an s-expression."""
    found: List[str] = []
    seen: Set[str] = set()

    def walk(text: str) -> None:
        text = (text or "").strip()
        if not text:
            return
        if not text.startswith("("):
            tok = text
            if (
                tok
                and tok not in _BUILTIN
                and not tok.startswith(":")
                and not tok.isdigit()
                and tok[0] not in "-+"
            ):
                if tok not in seen:
                    seen.add(tok)
                    found.append(tok)
            return
        head, args = sexpr_head_args(text)
        if head is None:
            return
        if head == "_" and args:
            walk(args[0])
            return
        if head in ("forall", "exists") and len(args) >= 2:
            # Skip binder list; walk matrix only.
            walk(args[-1])
            return
        if head == "!" and args:
            walk(args[0])
            return
        if head not in _BUILTIN and head not in seen:
            seen.add(head)
            found.append(head)
        for arg in args:
            walk(arg)

    walk(expr)
    return found


def _unwrap_assert_body(body: str) -> str:
    head, args = sexpr_head_args(body)
    if head == "!" and args:
        return args[0]
    return body


def _goal_body_from_markers(smt: str) -> Optional[str]:
    m = _PROOF_GOAL_BLOCK.search(smt or "")
    if not m:
        return None
    bodies: List[str] = []
    i = 0
    chunk = m.group("body")
    while True:
        expr, i = read_sexpr(chunk, i)
        if expr is None:
            break
        head, args = sexpr_head_args(expr)
        if head == "assert" and args:
            bodies.append(_unwrap_assert_body(args[0]))
    return bodies[0] if bodies else None


def _strip_outer_not(term: str) -> Tuple[str, bool]:
    head, args = sexpr_head_args(term)
    if head == "not" and args:
        return args[0], True
    return term, False


def parse_smt_profile(smt_text: str, *, problem_id: str = "") -> ProblemProfile:
    """Build a formula index and signature from SMT-LIB2 text (no TPTP)."""
    profile = ProblemProfile(problem_id=problem_id or "")
    text = smt_text or ""
    functions: List[str] = []
    sorts: List[str] = []
    fun_sorts: Dict[str, Dict[str, object]] = {}
    datatypes: List[str] = []
    constructors: Set[str] = set()
    ctor_arities: Dict[str, List[str]] = {}
    datatype_ctors: Dict[str, List[str]] = {}
    f_idx = 0
    g_idx = 0

    marker_goal = _goal_body_from_markers(text)
    marker_norm = normalize_lemma_formula(marker_goal) if marker_goal else ""

    i = 0
    while True:
        expr, i = read_sexpr(text, i)
        if expr is None:
            break
        head, args = sexpr_head_args(expr)
        if not head or head in _SKIP_HEADS:
            continue
        if head == "declare-fun" and len(args) >= 3:
            name = args[0].strip()
            functions.append(name)
            arg_sorts = _parse_sort_list(args[1])
            ret = args[2].strip()
            fun_sorts[name] = {"input_sorts": arg_sorts, "return_sort": ret}
            if ret and ret not in sorts:
                sorts.append(ret)
            for s in arg_sorts:
                if s and s not in sorts:
                    sorts.append(s)
            continue
        if head in ("declare-datatype", "declare-datatypes"):
            # Best-effort: record datatype names and constructors.
            _collect_datatypes(
                expr, datatypes, constructors, sorts, ctor_arities, datatype_ctors,
            )
            continue
        if head == "define-fun" and len(args) >= 4:
            name = args[0].strip()
            functions.append(name)
            body = args[-1]
            fid = f"F{f_idx}"
            f_idx += 1
            profile.formulas.append(FormulaRecord(
                formula_id=fid,
                raw=normalize_lemma_formula(body),
                role="definition",
                role_source="define-fun",
                symbols=collect_symbols(body) + [name],
            ))
            continue
        if head != "assert" or not args:
            continue
        body = _unwrap_assert_body(args[0])
        body_norm = normalize_lemma_formula(body)
        stripped, was_not = _strip_outer_not(body)
        stripped_norm = normalize_lemma_formula(stripped)

        role = "axiom"
        role_source = "assert"
        formula_id = f"F{f_idx}"
        store_raw = body_norm

        if marker_norm and (
            body_norm == marker_norm
            or stripped_norm == marker_norm
            or normalize_lemma_formula(f"(not {stripped})") == marker_norm
        ):
            formula_id = f"G{g_idx}"
            g_idx += 1
            role = "goal"
            role_source = "proof_goal_marker"
            store_raw = stripped_norm if was_not else body_norm
            profile.goal_formula_id = formula_id
        else:
            f_idx += 1

        profile.formulas.append(FormulaRecord(
            formula_id=formula_id,
            raw=store_raw,
            role=role,
            role_source=role_source,
            symbols=collect_symbols(store_raw),
        ))

    if profile.goal_formula_id is None:
        # Heuristic: last negated quantified assert — mark unknown, do not claim explicit.
        for rec in reversed(profile.formulas):
            if rec.role != "axiom":
                continue
            stripped, was_not = _strip_outer_not(rec.raw)
            head, _ = sexpr_head_args(stripped)
            if was_not and head in ("forall", "exists"):
                rec.role = "goal"
                rec.role_source = "heuristic_last_not"
                rec.raw = normalize_lemma_formula(stripped)
                rec.symbols = collect_symbols(rec.raw)
                # Re-id for clarity
                old = rec.formula_id
                rec.formula_id = f"G{g_idx}"
                profile.goal_formula_id = rec.formula_id
                profile.evidence_notes.append(
                    f"goal role for {rec.formula_id} (was {old}) is heuristic_last_not"
                )
                break
        if profile.goal_formula_id is None:
            profile.evidence_notes.append("goal role unknown; no proof-goal marker")

    # Dedup signature lists preserving order
    def _uniq(xs: List[str]) -> List[str]:
        out: List[str] = []
        seen: Set[str] = set()
        for x in xs:
            if x and x not in seen:
                seen.add(x)
                out.append(x)
        return out

    profile.signature = {
        "functions": _uniq(functions),
        "sorts": _uniq(sorts),
        "datatypes": _uniq(datatypes),
        "constructors": sorted(constructors),
        "constructor_arities": {k: list(v) for k, v in sorted(ctor_arities.items())},
        "datatype_constructors": {
            k: list(v) for k, v in sorted(datatype_ctors.items())
        },
        "fun_sorts": fun_sorts,
    }
    return profile


def _collect_datatypes(
    expr: str,
    datatypes: List[str],
    constructors: Set[str],
    sorts: List[str],
    ctor_arities: Optional[Dict[str, List[str]]] = None,
    datatype_ctors: Optional[Dict[str, List[str]]] = None,
) -> None:
    head, args = sexpr_head_args(expr)
    if head == "declare-datatype" and args:
        name = args[0].strip()
        if name and name not in datatypes:
            datatypes.append(name)
            sorts.append(name)
        if len(args) >= 2:
            names = _add_ctors_from_group(args[1], constructors, ctor_arities)
            if datatype_ctors is not None and name:
                datatype_ctors[name] = names
        return
    if head == "declare-datatypes" and len(args) >= 2:
        # (declare-datatypes ((Lst 0) (Nat 0)) ( ((nil) (cons ...)) ((zero) (succ ...)) ))
        dt_names: List[str] = []
        for item in _parse_sexpr_list(args[0]):
            if item.startswith("("):
                ih, _ia = sexpr_head_args(item)
                nm = (ih or "").strip()
            else:
                nm = item.strip()
            if nm and nm not in datatypes:
                datatypes.append(nm)
                sorts.append(nm)
            if nm:
                dt_names.append(nm)
        # One constructor-group per datatype declaration.
        groups = _parse_sexpr_list(args[1])
        for idx, group in enumerate(groups):
            names = _add_ctors_from_group(group, constructors, ctor_arities)
            if datatype_ctors is not None and idx < len(dt_names):
                datatype_ctors[dt_names[idx]] = names


def _parse_sexpr_list(blob: str) -> List[str]:
    """Split ``(a b c)`` into argument s-exprs; bare token → single-element list."""
    text = (blob or "").strip()
    if not text:
        return []
    if not text.startswith("("):
        return [text]
    inner = text[1:-1].strip() if text.endswith(")") else text[1:].strip()
    out: List[str] = []
    j = 0
    while True:
        tok, j = read_sexpr(inner, j)
        if tok is None:
            break
        out.append(tok)
    return out


def _add_ctors_from_group(
    group: str,
    constructors: Set[str],
    ctor_sigs: Optional[Dict[str, List[str]]] = None,
) -> List[str]:
    """Extract ctor names / arg sorts from ``((nil) (cons (head Nat) (tail Lst)))``."""
    found: List[str] = []
    for ctor_decl in _parse_sexpr_list(group):
        text = (ctor_decl or "").strip()
        if not text:
            continue
        arg_sorts: List[str] = []
        if text.startswith("("):
            ch, args = sexpr_head_args(text)
            name = (ch or "").strip()
            for a in args:
                a = (a or "").strip()
                if a.startswith("("):
                    _sel, sel_args = sexpr_head_args(a)
                    if sel_args:
                        arg_sorts.append(sel_args[-1].strip())
                    elif _sel:
                        arg_sorts.append(_sel.strip())
                elif a:
                    arg_sorts.append(a)
        else:
            name = text
        if name and name not in _BUILTIN and not name.startswith(":"):
            constructors.add(name)
            found.append(name)
            if ctor_sigs is not None:
                ctor_sigs[name] = arg_sorts
    return found
