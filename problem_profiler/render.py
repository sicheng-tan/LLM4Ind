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
        m = re.search(r"constructors\s+([^;]+)$", detail or "")
    if not m:
        return []
    return [x.strip() for x in m.group(1).split(",") if x.strip()]


def _merge_recursion_facts(facts: List[RecursionFact]) -> List[Tuple[RecursionFact, bool]]:
    """Collapse structural_recursion + constructor_case_split for the same function.

    Returns (fact, case_split_flag) in stable order. Notes (constructors /
    link_with) are not rendered.
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
            merged = replace(
                primary,
                kind="structural_recursion" if struct else primary.kind,
                detail="",
                link="",
                link_peers=[],
            )
            out.append((merged, bool(cases)))
        for f in others:
            out.append((replace(f, link="", link_peers=[], detail=""), False))
    return out


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
            "  Recursion (definitions of goal-related functions; "
            "`recursive_call` = self-call not on constructor selectors):"
        )
        for fact, case_split in _merge_recursion_facts(gated.recursion):
            if fact.kind == "recursive_call":
                ev = "evidence=structural"
                note = "not on constructor selectors"
                peers = list(fact.bridge_peers or [])
                if peers:
                    note += "; via " + ", ".join(_qid(p) for p in peers)
                lines.append(
                    f"    - {_qid_fun(fact.function)}: {fact.kind} ({ev}; {note})"
                )
                continue
            ev = "evidence=structural"
            if case_split:
                ev += ", case_split"
            elif fact.evidence_level and fact.evidence_level != "structural":
                ev = f"evidence={fact.evidence_level}"
            lines.append(
                f"    - {_qid_fun(fact.function)}: {fact.kind} ({ev})"
            )
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
    # Goal relations / Function links are not rendered.
    if gated.induction_attempts:
        lines.append(
            "  Known induction attempts "
            "(base/step fragments already in the background for the CURRENT goal):"
        )
        lines.append(
            "    Legend: base@`C` = goal with induct var := `C`; "
            "step@`C` = `P(t)` => `P(C(...t...))`; "
            "for `Int`, base@`0` / step@`(+ 1 _)` are the Peano-style cases; "
            "nested = inner binder among known attempts."
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
