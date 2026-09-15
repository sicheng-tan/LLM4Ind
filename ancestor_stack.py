"""Path-local ancestor goal stack for cycle detection.

Strict ancestors only (not the current node). Used by static lemma screening
and optional PROOF PATH GOALS prompt blocks. Do not reconstruct this from
obligation-tree history.
"""

from __future__ import annotations

from typing import Callable, List, Mapping, Optional, Sequence, Tuple, Union

AncestorEntry = Mapping[str, Union[str, int]]
AncestorStack = Tuple[AncestorEntry, ...]


def empty_ancestor_stack() -> AncestorStack:
    return ()


def make_ancestor_entry(
    goal_id: str,
    depth: int,
    formula: str,
) -> AncestorEntry:
    return {
        "goal_id": str(goal_id or ""),
        "depth": int(depth),
        "formula": str(formula or "").strip(),
    }


def extend_ancestors(
    stack: Optional[Sequence[AncestorEntry]],
    goal_id: str,
    depth: int,
    formula: str,
) -> AncestorStack:
    """Return *stack* plus the current node (for a child to inherit)."""
    base: List[AncestorEntry] = [dict(e) for e in (stack or ())]
    entry = make_ancestor_entry(goal_id, depth, formula)
    if not entry["formula"]:
        return tuple(base)
    base.append(entry)
    return tuple(base)


def lemma_matches_ancestor(
    lemma: str,
    stack: Optional[Sequence[AncestorEntry]],
    *,
    equivalent: Callable[[str, str], bool],
) -> Optional[AncestorEntry]:
    """Return the first strict ancestor α/eq-equivalent to *lemma*, else None."""
    text = (lemma or "").strip()
    if not text:
        return None
    for entry in stack or ():
        formula = str(entry.get("formula") or "").strip()
        if formula and equivalent(text, formula):
            return entry
    return None


def format_proof_path_goals_for_prompt(
    *,
    current_id: str,
    current_depth: int,
    current_formula: str,
    stack: Optional[Sequence[AncestorEntry]],
) -> str:
    """User-prompt block listing CURRENT and STRICT ANCESTOR goals.

    Empty when there are no ancestors (root) or *current_formula* is missing.
    """
    ancestors = tuple(stack or ())
    cur = (current_formula or "").strip()
    if not ancestors or not cur:
        return ""
    lines = [
        "",
        "PROOF PATH GOALS (do not restate any of these as a lemma):",
        f"  CURRENT [id={current_id}, depth={int(current_depth)}]:",
        f"  {cur}",
    ]
    for i, entry in enumerate(ancestors):
        formula = str(entry.get("formula") or "").strip()
        if not formula:
            continue
        gid = str(entry.get("goal_id") or "")
        depth = entry.get("depth", "?")
        lines.append(f"  ANCESTOR A{i} [id={gid}, depth={depth}]:")
        lines.append(f"  {formula}")
    if len(lines) <= 4:
        return ""
    return "\n".join(lines)
