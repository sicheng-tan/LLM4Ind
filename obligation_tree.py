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
from typing import Any, Dict, List, Optional, Sequence, Tuple


LIBRARY_FILENAME = "lemma_library.json"
LIBRARY_BEGIN = "; proved lemma library"
LIBRARY_END = "; proved lemma library end"

NORMAL_KIND = "obligation_tree"

# Kinds still emitted by derive_repair_hints and shown on the obligation tree.
# Disabled / misleading kinds (need_stronger_lemma, need_induction_lemma,
# induction_depth_limit, timeout, search_explosion-as-hint) are omitted.
GUIDANCE_HINT_KINDS = (
    "need_rewrite",
    "need_directed_rewrite",
    "induction_stuck",
    "need_arithmetic_lemma",
    "high_difficulty_assertions",
)

HARVEST_CVC_PROFILES = ("cvc5_inductive", "cvc4_default")
# Same single schedule as usefulness / node prove / scheme short-prove.
HARVEST_VAMPIRE_PROFILES = (
    "induction_portfolio",
)
HARVEST_DISPATCH_KEY = "harvest_dispatch"
MAX_FORMULA_CHARS = 200
MAX_FOCUS_CHARS = 80
MAX_ATTEMPTS_KEPT = 12
MAX_HINT_KINDS = 3
MAX_FOCUS_TERMS = 2

CHILD_INVALID_JUDGE_LINE = (
    "Child invalid: use its reason to judge whether the CURRENT goal is also invalid."
)

_LIB_LOCK = threading.Lock()
_OFF_VALUES = frozenset({"0", "off", "false", "no"})


def _flag_enabled(name: str, default: str = "on") -> bool:
    return os.getenv(name, default).strip().lower() not in _OFF_VALUES


def lemma_library_enabled() -> bool:
    """Whether proved lemmas are stored, injected as axioms, and shown in the prompt."""
    return _flag_enabled("LEMMA_LIBRARY")


def local_lemma_harvest_enabled() -> bool:
    """Timeout harvest of directly proved lemmas as role=local (needs the library)."""
    return lemma_library_enabled() and _flag_enabled("LEMMA_LIBRARY_LOCAL")


def usefulness_harvest_delay_s() -> float:
    """Seconds to wait before speculative A⊢c_i while usefulness still runs."""
    raw = os.getenv("USEFULNESS_HARVEST_DELAY_S")
    if raw is None or str(raw).strip() == "":
        return 2.0
    try:
        return max(0.0, float(raw))
    except (TypeError, ValueError):
        return 2.0


def harvest_retry_timeout_s() -> int:
    """Timeout for proving G after local harvest; does not change the 60s usefulness budget."""
    raw = os.getenv("HARVEST_RETRY_TIMEOUT")
    if raw is None or str(raw).strip() == "":
        return 2
    try:
        return max(1, int(float(raw)))
    except (TypeError, ValueError):
        return 2


def root_finish_prove_timeout_s() -> int:
    """Root-only re-prove after LLM attempts fail.

    Default **120**. Uses ``perform_initial_verification`` (injects the
    lemma library when that flag is on). The longer budget is the point:
    no library-growth gate. Set ``ROOT_FINISH_PROVE_TIMEOUT=0`` / ``off``
    to disable. Call sites also cap by remaining task budget.
    """
    raw = os.getenv("ROOT_FINISH_PROVE_TIMEOUT", "120")
    token = str(raw).strip().lower()
    if token in _OFF_VALUES or token == "":
        return 0
    try:
        return max(0, int(float(token)))
    except (TypeError, ValueError):
        return 120


def obligation_tree_enabled() -> bool:
    """Whether the last well-formed obligation tree is recorded and shown in the prompt."""
    return _flag_enabled("OBLIGATION_TREE")


def lemma_library_role(item: Optional[dict]) -> str:
    """Missing role is pin (pre-harvest libraries)."""
    role = str((item or {}).get("role") or "pin").strip().lower()
    return "local" if role == "local" else "pin"


def normalize_lemma_formula(formula: str) -> str:
    return re.sub(r"\s+", " ", (formula or "").strip())


def lemmas_equivalent(left: str, right: str) -> bool:
    """Whitespace collapse or α-normalization; not a fuzzy similarity check."""
    a = normalize_lemma_formula(left)
    b = normalize_lemma_formula(right)
    if not a or not b:
        return False
    if a == b:
        return True
    try:
        from cvc5_runner import canonical_smt_term
        return canonical_smt_term(a) == canonical_smt_term(b)
    except Exception:
        return False


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
    items = list(lemmas)
    payload = {"lemmas": items}
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


def _next_library_id(lemmas: Sequence[dict]) -> str:
    next_n = 1
    for item in lemmas:
        match = re.fullmatch(r"lib_(\d+)", str(item.get("id") or ""))
        if match:
            next_n = max(next_n, int(match.group(1)) + 1)
    return f"lib_{next_n}"


def add_proved_lemma(
    base_path: str,
    formula: str,
    *,
    origin: str = "",
    attempt: int = 0,
    depth: int = 0,
    role: str = "pin",
    prelude: str = "",
) -> Optional[str]:
    """Record a discharged lemma. ``role`` is pin (useful split) or local (timeout harvest).

    ``prelude`` is optional SMT (declare-fun / defining asserts) required by
    the formula — e.g. InductionScheme ``measure_prelude`` for
    ``__scheme_nat_to_int``. Injected before library asserts.

    Returns its library id, or None if empty / local harvest is off. Duplicate
    formulas (whitespace or α-equivalent) keep the existing id; a later pin
    promotes local in place. There is no size cap: pins and locals both append.
    Equivalent formulas are also dropped from ``unproved_lemmas`` and
    ``revival_lemmas`` in this folder.
    """
    want = "local" if str(role or "pin").strip().lower() == "local" else "pin"
    if want == "local" and not local_lemma_harvest_enabled():
        return None
    formula = normalize_lemma_formula(formula)
    if not formula:
        return None
    prelude = str(prelude or "").strip()
    from exp_stats import log_exp
    from lemma_gates import purge_unproved_equivalent

    n_drop = purge_unproved_equivalent(base_path, formula)
    if n_drop:
        log_exp("unproved_drop", n=n_drop)

    if not lemma_library_enabled():
        return None

    with _LIB_LOCK:
        lemmas = load_lemma_library(base_path)
        for item in lemmas:
            stored = str(item.get("formula") or "")
            if not lemmas_equivalent(stored, formula):
                continue
            lib_id = str(item.get("id") or "")
            existing_role = lemma_library_role(item)
            changed = False
            if existing_role == "local" and want == "pin":
                item["role"] = "pin"
                item["origin"] = origin or item.get("origin") or ""
                item["attempt"] = attempt
                item["depth"] = depth
                changed = True
                log_exp("library_promote", id=lib_id, role="pin")
                logging.info("lemma library promote %s local→pin", lib_id)
            if prelude and not str(item.get("prelude") or "").strip():
                item["prelude"] = prelude
                changed = True
                log_exp("library_prelude_attach", id=lib_id)
            if changed:
                save_lemma_library(base_path, lemmas)
            elif normalize_lemma_formula(stored) != formula:
                log_exp("library_alpha_dup", id=lib_id, role=existing_role)
                logging.info("lemma library skip α-dup %s", lib_id)
            return lib_id or None

        lib_id = _next_library_id(lemmas)
        entry = {
            "id": lib_id,
            "formula": formula,
            "status": "proved",
            "role": want,
            "origin": origin,
            "attempt": attempt,
            "depth": depth,
        }
        if prelude:
            entry["prelude"] = prelude
        lemmas.append(entry)
        save_lemma_library(base_path, lemmas)
        logging.info(
            "lemma library +%s role=%s origin=%s attempt=%s depth=%s prelude=%s",
            lib_id, want, origin, attempt, depth, bool(prelude),
        )
        return lib_id


_SCHEME_HELPER_RE = re.compile(r"\b(__scheme_[A-Za-z_][A-Za-z0-9_]*)\b")
_SMT_LOGIC_RE = re.compile(r"\(set-logic\s+([A-Za-z0-9_+]+)\)")
# Sort tokens that require arithmetic logics (scheme μ helpers return Int).
_ARITH_SORT_RE = re.compile(r"(?<![A-Za-z0-9_])(Int|Real)(?![A-Za-z0-9_])")


def _text_needs_arith_sorts(text: str) -> Tuple[bool, bool]:
    """Return ``(need_int, need_real)`` if *text* mentions those SMT sorts."""
    need_int = False
    need_real = False
    for m in _ARITH_SORT_RE.finditer(text or ""):
        if m.group(1) == "Int":
            need_int = True
        else:
            need_real = True
    return need_int, need_real


def _logic_allows_int(logic: str) -> bool:
    u = (logic or "").upper()
    if u in ("ALL", "QF_ALL"):
        return True
    return any(tag in u for tag in ("LIA", "LRA", "NIA", "NRA"))


def _logic_allows_real(logic: str) -> bool:
    u = (logic or "").upper()
    if u in ("ALL", "QF_ALL"):
        return True
    return any(tag in u for tag in ("LRA", "NRA"))


def _upgrade_logic_name(logic: str, *, need_int: bool, need_real: bool) -> Optional[str]:
    """Map a logic that cannot host Int/Real helpers to one that can."""
    if need_real and not _logic_allows_real(logic):
        table = {
            "UFDT": "UFDTLIRA",
            "QF_UFDT": "QF_UFDTLIRA",
            "UF": "UFLRA",
            "QF_UF": "QF_UFLRA",
            "UFDTLIA": "UFDTLIRA",
            "QF_UFDTLIA": "QF_UFDTLIRA",
            "UFLIA": "UFLRA",
            "QF_UFLIA": "QF_UFLRA",
        }
        return table.get(logic, "ALL")
    if need_int and not _logic_allows_int(logic):
        table = {
            "UFDT": "UFDTLIA",
            "QF_UFDT": "QF_UFDTLIA",
            "UF": "UFLIA",
            "QF_UF": "QF_UFLIA",
        }
        return table.get(logic, "ALL")
    return None


def ensure_smt_logic_for_arith(smt_content: str, *, need_int: bool, need_real: bool) -> str:
    """Rewrite ``(set-logic …)`` when library prelude introduces Int/Real.

    Scheme measure helpers (``__scheme_list_len : list → Int`` etc.) are often
    pinned into UFDT problems. Without upgrading to UFDTLIA/ALL, CVC
    ``--parse-only`` wellformed screening rejects *every* lemma against the
    injected background — including lemmas that never mention Int.
    """
    if not need_int and not need_real:
        return smt_content
    m = _SMT_LOGIC_RE.search(smt_content or "")
    if not m:
        return smt_content
    new_logic = _upgrade_logic_name(m.group(1), need_int=need_int, need_real=need_real)
    if not new_logic or new_logic == m.group(1):
        return smt_content
    logging.info(
        "lemma library upgrade set-logic %s → %s (scheme arith prelude)",
        m.group(1), new_logic,
    )
    return smt_content[: m.start(1)] + new_logic + smt_content[m.end(1) :]


def upgrade_smt_logic_for_text(smt_content: str, extra_text: str = "") -> str:
    """Upgrade ``set-logic`` if *extra_text* (prelude) introduces Int/Real sorts."""
    need_int, need_real = _text_needs_arith_sorts(extra_text or "")
    return ensure_smt_logic_for_arith(
        smt_content, need_int=need_int, need_real=need_real,
    )


def scheme_helpers_in_text(text: str) -> List[str]:
    """Unique ``__scheme_*`` identifiers referenced in SMT / formulas."""
    seen = set()
    out: List[str] = []
    for name in _SCHEME_HELPER_RE.findall(text or ""):
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def _prelude_declares(prelude: str, name: str) -> bool:
    if not prelude or not name:
        return False
    return bool(
        re.search(
            rf"\(declare-fun\s+{re.escape(name)}\b",
            prelude,
        )
    )


def collect_library_preludes(lemmas: Sequence[dict]) -> str:
    """Deduped measure / synth preludes stored on library rows."""
    chunks: List[str] = []
    seen = set()
    for item in lemmas or []:
        prelude = str((item or {}).get("prelude") or "").strip()
        if not prelude or prelude in seen:
            continue
        seen.add(prelude)
        chunks.append(prelude)
    return "\n".join(chunks).strip()


def inject_library_axioms(
    smt_content: str,
    lemmas: Sequence[dict],
    *,
    add_patterns: bool = False,
) -> str:
    """Insert proved lemmas as axioms just before the proof-goal block.

    Emits any stored ``prelude`` (scheme measure helpers) once before asserts.
    Lemmas that reference undeclared ``__scheme_*`` helpers are skipped so a
    polluted library cannot break parse-only wellformed checks for other lemmas.

    When a prelude (or injected formula) introduces ``Int``/``Real`` into a
    non-arith logic such as ``UFDT``, rewrite ``set-logic`` to ``UFDTLIA`` /
    ``ALL`` so CVC wellformed screening and prove runs stay consistent.

    When ``add_patterns`` is set, directed equalities get a ``:pattern`` on
    the LHS for E-matching. Subgoal SMT stays bare.
    """
    from smt_patterns import format_assert_line
    from exp_stats import log_exp

    stripped = re.sub(
        rf"{re.escape(LIBRARY_BEGIN)}.*?{re.escape(LIBRARY_END)}\n?",
        "",
        smt_content,
        flags=re.DOTALL,
    )
    if not lemmas:
        return stripped

    prelude_block = collect_library_preludes(lemmas)
    declared = {
        name
        for name in scheme_helpers_in_text(prelude_block + "\n" + stripped)
        if _prelude_declares(prelude_block, name)
        or re.search(rf"\(declare-fun\s+{re.escape(name)}\b", stripped)
    }

    lines = [LIBRARY_BEGIN]
    if prelude_block:
        lines.append("; scheme measure prelude (from library pins)")
        lines.append(prelude_block)

    n_skip = 0
    emitted_formulas: List[str] = []
    for item in lemmas:
        lib_id = str(item.get("id") or "lib")
        formula = normalize_lemma_formula(str(item.get("formula") or ""))
        if not formula:
            continue
        needed = scheme_helpers_in_text(formula)
        missing = [n for n in needed if n not in declared]
        row_prelude = str(item.get("prelude") or "").strip()
        if missing and row_prelude:
            for n in list(missing):
                if _prelude_declares(row_prelude, n):
                    missing.remove(n)
                    declared.add(n)
        if missing:
            n_skip += 1
            logging.warning(
                "lemma library skip %s: missing scheme prelude for %s",
                lib_id, ", ".join(missing),
            )
            continue
        lines.append(f"; {lib_id}")
        lines.append(format_assert_line(formula, add_pattern=add_patterns))
        emitted_formulas.append(formula)
    if n_skip:
        log_exp("library_skip_missing_prelude", n=n_skip)
    lines.append(LIBRARY_END)
    block = "\n".join(lines) + "\n"

    need_int, need_real = _text_needs_arith_sorts(prelude_block)
    for formula in emitted_formulas:
        fi, fr = _text_needs_arith_sorts(formula)
        need_int = need_int or fi
        need_real = need_real or fr
    stripped = ensure_smt_logic_for_arith(
        stripped, need_int=need_int, need_real=need_real,
    )

    marker = "; proof goal"
    idx = stripped.find(marker)
    if idx >= 0:
        return stripped[:idx] + block + stripped[idx:]
    return block + stripped


def materialize_smt_with_library(
    smt_path: Path,
    base_path: str,
    *,
    add_patterns: bool = False,
    dest: Optional[Path] = None,
) -> Path:
    """Write a sibling SMT file that includes the lemma library, if any."""
    if not lemma_library_enabled():
        return smt_path
    lemmas = load_lemma_library(base_path)
    if not lemmas:
        return smt_path
    content = inject_library_axioms(
        smt_path.read_text(encoding="utf-8"),
        lemmas,
        add_patterns=add_patterns,
    )
    out = dest if dest is not None else smt_path.with_name(smt_path.stem + ".__lib.smt2")
    out.write_text(content, encoding="utf-8")
    return out


def solver_smt_content(
    smt_content: str,
    base_path: Optional[str],
    *,
    add_patterns: bool = False,
) -> str:
    if not base_path or not lemma_library_enabled():
        return smt_content
    return inject_library_axioms(
        smt_content,
        load_lemma_library(base_path),
        add_patterns=add_patterns,
    )

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


def make_goal_tree(
    goal_id: str,
    children: Sequence[dict],
    *,
    proved: bool,
    formula: Optional[str] = None,
) -> dict:
    return {
        "id": goal_id,
        "role": "goal",
        "formula": normalize_lemma_formula(formula or "") or None,
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
    depth: int = 0,
) -> str:
    """Compressed title-and-indent block for the next LLM attempt.

    The 'CURRENT goal may also be invalid' instruction is only for child
    generation (depth >= 1) and the extra diagnosis call. The root still sees
    invalid children as history, but is not asked to abort the original goal.
    """
    if for_diagnosis:
        include_library = False
        if include_tree is None:
            include_tree = obligation_tree_enabled()
    elif include_library is None:
        include_library = lemma_library_enabled()
    if include_tree is None:
        include_tree = obligation_tree_enabled()
    shown_library = list(library) if include_library else []
    tree = last_normal_tree(obligation) if include_tree else None
    if not shown_library and not tree:
        return ""

    judge_current = bool(for_diagnosis or int(depth or 0) >= 1)
    if for_diagnosis:
        tree_legend = [
            "OBLIGATION HISTORY: use this tree to judge whether the CURRENT goal is a theorem; do not propose lemmas.",
            "proved / failed / invalid describe child lemmas; only invalid includes a reason.",
        ]
    else:
        tree_legend = [
            "OBLIGATION HISTORY: generate lemmas for the CURRENT goal only.",
            "proved: reuse. failed: you may weaken. invalid: do not weaken; use the reason.",
        ]
    if judge_current:
        tree_legend.append(CHILD_INVALID_JUDGE_LINE)
    parts = [""]
    if shown_library and tree:
        parts.extend([
            "OBLIGATION HISTORY: generate lemmas for the CURRENT goal only.",
            "Library formulas are already axioms. Do not resend a failed split.",
            "proved: reuse. failed: you may weaken. invalid: do not weaken; use the reason.",
        ])
        if judge_current:
            parts.append(CHILD_INVALID_JUDGE_LINE)
    elif shown_library:
        parts.extend([
            "LEMMA LIBRARY: these formulas are already axioms for the CURRENT goal.",
            "You may reuse them; do not regenerate equivalent lemmas.",
        ])
    else:
        parts.extend(tree_legend)
    if shown_library:
        prelude_block = collect_library_preludes(shown_library)
        if prelude_block:
            parts.append("Scheme measure prelude (definition in SMT axioms):")
            for pl in prelude_block.splitlines():
                parts.append(f"  {pl}" if pl.strip() else "  ")
        parts.append("Library (already proved, in axioms):")
        for item in shown_library:
            lib_id = item.get("id") or "lib"
            formula = compact_formula(item.get("formula"))
            parts.append(f"  {lib_id}: {formula}")
    if tree:
        attempt_id = (obligation or {}).get("last_normal_tree_id") or "?"
        parts.append(f"Last obligation tree (attempt {attempt_id}; for reference only):")
        for line in render_obligation_tree(tree):
            parts.append(f"  {line}")
    return "\n".join(parts)


def format_diagnosis_tree_prompt(obligation: Optional[dict]) -> str:
    """Tree-only block for the extra invalid-check LLM call."""
    if not obligation_tree_enabled():
        return ""
    return format_obligation_prompt(
        [],
        obligation,
        include_library=False,
        include_tree=True,
        for_diagnosis=True,
    )
