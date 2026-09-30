"""Render gated profile facts as a lemma-generation prompt block."""

from __future__ import annotations

from dataclasses import replace
from typing import Dict, List, Tuple

from .types import GatedProfileFacts, RecursionFact


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
    # Goal relations / Function links / Known induction attempts are not
    # rendered. Scheme (when on) injects its own ledger via mate_glue; Known
    # α-match rows are omitted even when scheme is off (low hit rate / noise).
    return "\n".join(lines) + "\n"
