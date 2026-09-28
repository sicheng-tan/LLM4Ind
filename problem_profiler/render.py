"""Render gated profile facts as a lemma-generation prompt block."""

from __future__ import annotations

import re
from dataclasses import replace
from typing import Dict, List, Tuple

from .types import GatedProfileFacts, InductionAttempt, RecursionFact


def _qid(name: str) -> str:
    """Wrap a symbol so it is distinct from English prose."""
    text = (name or "").strip()
    if not text:
        return "``"
    return f"`{text}`"


def _qid_fun(name: str) -> str:
    """Wrap function id; ``a/b`` mutual pairs become ```a`/`b``.``"""
    parts = [p for p in (name or "").split("/") if p]
    if not parts:
        return _qid(name)
    return "/".join(_qid(p) for p in parts)


def _qid_list(names: List[str]) -> str:
    return ", ".join(_qid(n) for n in names if n)


def _ctors_from_detail(detail: str) -> List[str]:
    m = re.search(r"constructors=([^;]+)", detail or "")
    if not m:
        # "defining equations cover constructors cons, nil"
        m = re.search(r"constructors\s+([^;]+)$", detail or "")
    if not m:
        return []
    return [x.strip() for x in m.group(1).split(",") if x.strip()]


def _merge_recursion_facts(facts: List[RecursionFact]) -> List[Tuple[RecursionFact, bool]]:
    """Collapse structural_recursion + constructor_case_split for the same function.

    Returns (fact, case_split_flag) in stable order.
    """
    groups: Dict[str, List[RecursionFact]] = {}
    order: List[str] = []
    for fact in facts:
        key = fact.function
        if key not in groups:
            groups[key] = []
            order.append(key)
        groups[key].append(fact)

    out: List[Tuple[RecursionFact, bool]] = []
    for key in order:
        items = groups[key]
        struct = [f for f in items if f.kind == "structural_recursion"]
        cases = [f for f in items if f.kind == "constructor_case_split"]
        others = [
            f for f in items
            if f.kind not in ("structural_recursion", "constructor_case_split")
        ]
        if struct or cases:
            primary = struct[0] if struct else cases[0]
            # Prefer constructors / peers from any sibling.
            ctors: List[str] = []
            peers: List[str] = []
            for f in struct + cases:
                for c in _ctors_from_detail(f.detail):
                    if c not in ctors:
                        ctors.append(c)
                for p in f.link_peers or []:
                    if p not in peers:
                        peers.append(p)
            detail = f"constructors={', '.join(ctors)}" if ctors else ""
            merged = replace(
                primary,
                kind="structural_recursion" if struct else primary.kind,
                detail=detail,
                link="",  # not rendered
                link_peers=peers,
            )
            out.append((merged, bool(cases)))
        for f in others:
            out.append((replace(f, link=""), False))
    return out


def _recursion_note(fact: RecursionFact) -> str:
    parts: List[str] = []
    ctors = _ctors_from_detail(fact.detail)
    if ctors:
        parts.append("constructors=" + _qid_list(ctors))
    elif fact.detail and fact.detail.startswith("constructors="):
        parts.append(_decorate_ctors_only(fact.detail))
    if fact.link_peers:
        parts.append("link_with=" + _qid_list(fact.link_peers))
    return "; ".join(parts)


def _decorate_ctors_only(detail: str) -> str:
    ctors = _ctors_from_detail(detail)
    return "constructors=" + _qid_list(ctors) if ctors else ""


def _induction_detail_line(att: InductionAttempt) -> str:
    if att.status == "candidate" and not att.base_ctors and not att.step_ctors:
        return "attempt=none"
    parts: List[str] = []
    if att.base_ctors:
        parts.append("base@" + ",".join(_qid(c) for c in att.base_ctors))
    if att.step_ctors:
        parts.append("step@" + ",".join(_qid(c) for c in att.step_ctors))
    if att.base_ctors or att.step_ctors:
        covered = sorted(set(att.base_ctors) | set(att.step_ctors))
        parts.append(
            "case_split="
            + ("yes" if att.case_split else "no")
            + (f" ({_qid_list(covered)})" if covered else "")
        )
    return "; ".join(parts) if parts else "attempt=none"


def format_profile_prompt_block(gated: GatedProfileFacts) -> str:
    if gated is None or gated.is_empty():
        return ""
    lines = [
        "",
        "PROBLEM STRUCTURE (auxiliary information extracted from the SMT):",
        "  Identifiers enclosed in backticks denote function names, variables, "
        "sorts, or constructors (e.g., `len`).",
    ]
    if gated.recursion:
        lines.append(
            "  Recursion (constructor cases in definitions of goal-related functions):"
        )
        for fact, case_split in _merge_recursion_facts(gated.recursion):
            ev = "evidence=structural"
            if case_split:
                ev += ", case_split"
            elif fact.evidence_level and fact.evidence_level != "structural":
                ev = f"evidence={fact.evidence_level}"
            lines.append(
                f"    - {_qid_fun(fact.function)}: {fact.kind} ({ev})"
            )
            note = _recursion_note(fact)
            if note:
                lines.append(f"      note: {note}")
    if gated.observers:
        lines.append(
            "  Observer candidates (goal-related maps from an ADT to another sort):"
        )
        for obs in gated.observers:
            if obs.input_sorts:
                sig = (
                    f"{', '.join(_qid(s) for s in obs.input_sorts)} -> "
                    f"{_qid(obs.return_sort)}"
                )
            else:
                sig = _qid(obs.return_sort)
            lines.append(
                f"    - {_qid(obs.function)}: {sig} "
                f"(evidence={obs.evidence_level})"
            )
    if gated.relations:
        lines.append(
            "  Goal relations (which recursive/observer symbols the goal mentions):"
        )
        for rel in gated.relations:
            sym = ", ".join(_qid(s) for s in rel.symbols)
            lines.append(
                f"    - {rel.kind}: [{sym}] (evidence={rel.evidence_level})"
            )
    if gated.function_links:
        lines.append(
            "  Function links (goal functions that co-occur — or not — in axioms):"
        )
        related = [lk for lk in gated.function_links if lk.kind == "theorem_related"]
        missing = [lk for lk in gated.function_links if lk.kind == "missing_bridge"]
        for lk in related:
            pair = "–".join(_qid(s) for s in lk.symbols)
            lines.append(f"    - related: {pair}")
        for lk in missing:
            pair = "–".join(_qid(s) for s in lk.symbols)
            lines.append(f"    - missing_bridge: {pair}")
    if gated.induction_attempts:
        lines.append(
            "  Known induction attempts "
            "(base/step fragments already in the background for the CURRENT goal):"
        )
        lines.append(
            "    Legend: base@`C` = goal with induct var := `C`; "
            "step@`C` = `P(t)` => `P(C(...t...))`; "
            "attempt=none = missing; nested = inner binder."
        )
        ordered = sorted(
            enumerate(gated.induction_attempts),
            key=lambda it: (it[1].nest_level, it[0]),
        )
        for _i, att in ordered:
            pad = "    " + ("  " * max(0, int(att.nest_level)))
            bullet = "- nested " if att.nest_level else "- "
            detail = _induction_detail_line(att)
            lines.append(
                f"{pad}{bullet}var={_qid(att.induct_var)}:{_qid(att.induct_sort)}; "
                f"{detail}"
            )
    return "\n".join(lines) + "\n"
