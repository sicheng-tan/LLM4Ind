"""Lemma library + compressed recursive obligation trees for later LLM attempts.

A new attempt still generates lemmas for the *current* goal. Successfully
discharged lemmas are stored as theorems and injected as axioms. The prompt
receives one well-formed obligation tree (the latest attempt that actually
recursed), not empty / invalid / useless attempts.
"""

from __future__ import annotations

import json
import logging
import os
import re
import tempfile
import threading
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence


LIBRARY_FILENAME = "lemma_library.json"
LIBRARY_BEGIN = "; proved lemma library"
LIBRARY_END = "; proved lemma library end"

NORMAL_KIND = "obligation_tree"

GUIDANCE_HINT_KINDS = (
    "need_rewrite",
    "need_directed_rewrite",
    "induction_stuck",
    "need_induction_lemma",
    "need_stronger_lemma",
    "need_arithmetic_lemma",
    "search_explosion",
    "induction_depth_limit",
    "high_difficulty_assertions",
)

MAX_LIBRARY_LEMMAS = 12
MAX_FORMULA_CHARS = 200
MAX_FOCUS_CHARS = 80
MAX_ATTEMPTS_KEPT = 12
MAX_HINT_KINDS = 3
MAX_FOCUS_TERMS = 2

_LIB_LOCK = threading.Lock()
_OFF_VALUES = frozenset({"0", "off", "false", "no"})


def _flag_enabled(name: str, default: str = "on") -> bool:
    return os.getenv(name, default).strip().lower() not in _OFF_VALUES


def lemma_library_enabled() -> bool:
    """Whether proved lemmas are stored, injected as axioms, and shown in the prompt."""
    return _flag_enabled("LEMMA_LIBRARY")


def obligation_tree_enabled() -> bool:
    """Whether the last well-formed obligation tree is recorded and shown in the prompt."""
    return _flag_enabled("OBLIGATION_TREE")


def normalize_lemma_formula(formula: str) -> str:
    return re.sub(r"\s+", " ", (formula or "").strip())


def compact_formula(formula: Optional[str], limit: int = MAX_FORMULA_CHARS) -> str:
    text = normalize_lemma_formula(formula or "")
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 3)] + "..."


def lemma_library_path(base_path: str) -> Path:
    return Path(base_path) / LIBRARY_FILENAME


def empty_obligation_state() -> dict:
    return {"attempts": [], "last_normal_tree_id": None}


def load_lemma_library(base_path: str) -> List[dict]:
    path = lemma_library_path(base_path)
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    lemmas = data.get("lemmas") if isinstance(data, dict) else data
    if not isinstance(lemmas, list):
        return []
    return [item for item in lemmas if isinstance(item, dict) and item.get("formula")]


def save_lemma_library(base_path: str, lemmas: Sequence[dict]) -> None:
    path = lemma_library_path(base_path)
    payload = {"lemmas": list(lemmas)[-MAX_LIBRARY_LEMMAS:]}
    tmp_file = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=str(path.parent),
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as handle:
            tmp_file = Path(handle.name)
            json.dump(payload, handle, ensure_ascii=False, indent=2)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp_file, path)
    except OSError:
        if tmp_file is not None:
            try:
                tmp_file.unlink()
            except OSError:
                pass


def add_proved_lemma(
    base_path: str,
    formula: str,
    *,
    origin: str = "",
    attempt: int = 0,
    depth: int = 0,
) -> Optional[str]:
    """Record a fully discharged lemma. Returns its library id, or None if empty."""
    if not lemma_library_enabled():
        return None
    formula = normalize_lemma_formula(formula)
    if not formula:
        return None
    with _LIB_LOCK:
        lemmas = load_lemma_library(base_path)
        for item in lemmas:
            if normalize_lemma_formula(str(item.get("formula") or "")) == formula:
                return str(item.get("id") or "")
        next_n = 1
        for item in lemmas:
            match = re.fullmatch(r"lib_(\d+)", str(item.get("id") or ""))
            if match:
                next_n = max(next_n, int(match.group(1)) + 1)
        lib_id = f"lib_{next_n}"
        lemmas.append({
            "id": lib_id,
            "formula": formula,
            "status": "proved",
            "origin": origin,
            "attempt": attempt,
            "depth": depth,
        })
        save_lemma_library(base_path, lemmas)
        logging.info(
            "lemma library +%s origin=%s attempt=%s depth=%s",
            lib_id, origin, attempt, depth,
        )
        return lib_id


def inject_library_axioms(smt_content: str, lemmas: Sequence[dict]) -> str:
    """Insert proved lemmas as axioms just before the proof-goal block."""
    stripped = re.sub(
        rf"{re.escape(LIBRARY_BEGIN)}.*?{re.escape(LIBRARY_END)}\n?",
        "",
        smt_content,
        flags=re.DOTALL,
    )
    if not lemmas:
        return stripped
    lines = [LIBRARY_BEGIN]
    for item in lemmas:
        lib_id = str(item.get("id") or "lib")
        formula = normalize_lemma_formula(str(item.get("formula") or ""))
        if not formula:
            continue
        lines.append(f"; {lib_id}")
        lines.append(f"(assert {formula})")
    lines.append(LIBRARY_END)
    block = "\n".join(lines) + "\n"
    marker = "; proof goal"
    idx = stripped.find(marker)
    if idx >= 0:
        return stripped[:idx] + block + stripped[idx:]
    return block + stripped


def materialize_smt_with_library(smt_path: Path, base_path: str) -> Path:
    """Write a sibling SMT file that includes the lemma library, if any."""
    if not lemma_library_enabled():
        return smt_path
    lemmas = load_lemma_library(base_path)
    if not lemmas:
        return smt_path
    content = inject_library_axioms(
        smt_path.read_text(encoding="utf-8"), lemmas
    )
    out = smt_path.with_name(smt_path.stem + ".__lib.smt2")
    out.write_text(content, encoding="utf-8")
    return out


def solver_smt_content(smt_content: str, base_path: Optional[str]) -> str:
    if not base_path or not lemma_library_enabled():
        return smt_content
    return inject_library_axioms(smt_content, load_lemma_library(base_path))


def classify_failed_attempt(extracted: Sequence[str], failed_data: dict) -> str:
    if not extracted:
        return "empty"
    extracted_list = list(extracted)
    for group in failed_data.get("useless_lemma_groups") or []:
        lemmas = group if isinstance(group, list) else group.get("lemmas", [])
        if lemmas == extracted_list:
            return "useless"
    return "invalid"


def last_normal_tree(obligation: Optional[dict]) -> Optional[dict]:
    if not isinstance(obligation, dict):
        return None
    tree_id = obligation.get("last_normal_tree_id")
    attempts = obligation.get("attempts") or []
    if tree_id is not None:
        for rec in reversed(attempts):
            if rec.get("id") == tree_id and rec.get("kind") == NORMAL_KIND:
                tree = rec.get("tree")
                return tree if isinstance(tree, dict) else None
    for rec in reversed(attempts):
        if rec.get("kind") == NORMAL_KIND and rec.get("tree"):
            return rec["tree"]
    return None


def append_attempt(
    obligation: Optional[dict],
    kind: str,
    tree: Optional[dict] = None,
) -> dict:
    state = dict(obligation or empty_obligation_state())
    attempts = list(state.get("attempts") or [])
    attempt_id = (attempts[-1]["id"] + 1) if attempts else 1
    record = {"id": attempt_id, "kind": kind, "tree": tree if kind == NORMAL_KIND else None}
    attempts.append(record)
    state["attempts"] = attempts[-MAX_ATTEMPTS_KEPT:]
    if kind == NORMAL_KIND and tree:
        state["last_normal_tree_id"] = attempt_id
    elif "last_normal_tree_id" not in state:
        state["last_normal_tree_id"] = None
    return state


def next_attempt_id(obligation: Optional[dict]) -> int:
    attempts = (obligation or {}).get("attempts") or []
    return (attempts[-1]["id"] + 1) if attempts else 1


def make_child_node(
    *,
    node_id: str,
    formula: Optional[str],
    status: str,
    lib: Optional[str] = None,
    atp: Optional[dict] = None,
    reason: Optional[str] = None,
    children: Optional[List[dict]] = None,
) -> dict:
    node: Dict[str, Any] = {
        "id": node_id,
        "role": "lemma",
        "formula": normalize_lemma_formula(formula or "") or None,
        "status": status,
        "lib": lib,
        "children": list(children or []),
    }
    # ATP hints stay on the node prompt (FEEDBACK_REPAIR_HINTS), not the tree.
    if reason and status == "invalid":
        node["reason"] = compact_formula(str(reason), MAX_FOCUS_CHARS * 2)
    return node


def make_goal_tree(goal_id: str, children: Sequence[dict], *, proved: bool) -> dict:
    return {
        "id": goal_id,
        "role": "goal",
        "formula": None,
        "status": "proved" if proved else "open",
        "lib": None,
        "children": list(children),
    }


def compact_atp_from_failed_data(failed_data: Optional[dict]) -> dict:
    hints: List[str] = []
    focus: List[str] = []
    for hint in (failed_data or {}).get("repair_hints") or []:
        kind = str(hint.get("kind") or "")
        if kind in GUIDANCE_HINT_KINDS and kind not in hints:
            hints.append(kind)
        for term in hint.get("induction_focus") or []:
            compact = compact_formula(str(term), MAX_FOCUS_CHARS)
            if compact and compact not in focus:
                focus.append(compact)
            if len(focus) >= MAX_FOCUS_TERMS:
                break
        if len(hints) >= MAX_HINT_KINDS and len(focus) >= MAX_FOCUS_TERMS:
            break
    return {"hints": hints[:MAX_HINT_KINDS], "focus": focus[:MAX_FOCUS_TERMS]}


def short_label(node: dict) -> str:
    lib = node.get("lib")
    if node.get("status") == "proved" and lib:
        return str(lib)
    node_id = str(node.get("id") or "")
    if node.get("role") == "goal" or not node_id:
        return "G"
    rest = node_id.replace("template", "", 1).lstrip("_")
    return f"L{rest}" if rest else node_id


def first_invalid_reason(node: Optional[dict]) -> str:
    """Depth-first reason from an invalid node; empty if the tree has none."""
    if not isinstance(node, dict):
        return ""
    if str(node.get("status") or "") == "invalid":
        return str(node.get("reason") or "").strip() or "invalid"
    for child in node.get("children") or []:
        found = first_invalid_reason(child)
        if found:
            return found
    return ""


def _guidance_bracket(node: dict) -> str:
    """Tree labels: only invalid carries a short reason. No ATP hint kinds."""
    if str(node.get("status") or "") != "invalid":
        return ""
    reason = compact_formula(node.get("reason"), MAX_FOCUS_CHARS * 2)
    if not reason:
        return ""
    return f" [{reason}]"


def _node_line(node: dict, *, is_root: bool = False) -> str:
    status = str(node.get("status") or "open")
    if is_root:
        return f"G  {status}"
    label = short_label(node)
    formula = compact_formula(node.get("formula"))
    line = f"{label}  {status}{_guidance_bracket(node)}"
    if formula:
        line += f"  {formula}"
    return line


def render_obligation_tree(tree: dict) -> List[str]:
    lines: List[str] = []

    def walk(node: dict, prefix: str, is_last: bool, is_root: bool) -> None:
        if is_root:
            lines.append(_node_line(node, is_root=True))
            child_prefix = ""
        else:
            branch = "└─ " if is_last else "├─ "
            lines.append(prefix + branch + _node_line(node))
            child_prefix = prefix + ("   " if is_last else "│  ")
        children = node.get("children") or []
        for i, child in enumerate(children):
            walk(child, child_prefix, i == len(children) - 1, False)

    walk(tree, "", True, True)
    return lines


def format_obligation_prompt(
    library: Sequence[dict],
    obligation: Optional[dict],
    *,
    include_library: Optional[bool] = None,
    include_tree: Optional[bool] = None,
    for_diagnosis: bool = False,
) -> str:
    """Compressed, comment-prefixed block for the next LLM attempt."""
    if for_diagnosis:
        include_library = False
        if include_tree is None:
            include_tree = True
    elif include_library is None:
        include_library = lemma_library_enabled()
    if include_tree is None:
        include_tree = obligation_tree_enabled()
    shown_library = list(library) if include_library else []
    tree = last_normal_tree(obligation) if include_tree else None
    if not shown_library and not tree:
        return ""

    tree_legend = (
        [
            "; OBLIGATION HISTORY: use this tree to judge whether the CURRENT goal is a theorem; do not propose lemmas.",
            "; proved / failed / invalid describe child lemmas; only invalid includes a reason.",
            "; Child invalid: use its reason to judge whether the CURRENT goal is also invalid.",
            "; This tree is the last split that passed usefulness and recursed; later useless attempts do not replace it.",
        ]
        if for_diagnosis else
        [
            "; OBLIGATION HISTORY: generate lemmas for the CURRENT goal only.",
            "; proved: reuse. failed: you may weaken. invalid: do not weaken; use the reason.",
            "; Child invalid: use its reason to judge whether the CURRENT goal is also invalid.",
            "; This tree is the last split that passed usefulness and recursed; later useless attempts do not replace it.",
        ]
    )
    parts = [""]
    if shown_library and tree:
        parts.extend([
            "; OBLIGATION HISTORY: generate lemmas for the CURRENT goal only.",
            "; Library formulas are already axioms. Do not resend a failed split.",
            "; proved: reuse. failed: you may weaken. invalid: do not weaken; use the reason.",
            "; Child invalid: use its reason to judge whether the CURRENT goal is also invalid.",
            "; This tree is the last split that passed usefulness and recursed; later useless attempts do not replace it.",
        ])
    elif shown_library:
        parts.extend([
            "; LEMMA LIBRARY: these formulas are already axioms for the CURRENT goal.",
            "; You may reuse them; do not regenerate equivalent lemmas.",
        ])
    else:
        parts.extend(tree_legend)
    if shown_library:
        parts.append("; Library (already proved, in axioms):")
        for item in shown_library:
            lib_id = item.get("id") or "lib"
            formula = compact_formula(item.get("formula"))
            parts.append(f";   {lib_id}: {formula}")
    if tree:
        attempt_id = (obligation or {}).get("last_normal_tree_id") or "?"
        parts.append(f"; Last obligation tree (attempt {attempt_id}; for reference only):")
        for line in render_obligation_tree(tree):
            parts.append(f";   {line}")
    return "\n".join(parts)


def format_diagnosis_tree_prompt(obligation: Optional[dict]) -> str:
    """Tree-only block for the extra invalid-check LLM call."""
    return format_obligation_prompt(
        [],
        obligation,
        include_library=False,
        include_tree=True,
        for_diagnosis=True,
    )
