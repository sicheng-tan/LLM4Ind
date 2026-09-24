"""Optional LLM hints from solver feedback (FEEDBACK_LLM_HINTS).

Default **off**. Requires at least one failed usefulness group (so the first
lemma-generation call is never steered by HD-only hints). After a useless
group, the diagnoser runs only if there is an unproved revival pool **and**
the lemma library has new ids vs the last baseline (first call compares
against an empty library, so any proved lemma counts as a change). Difficulty
is optional: when absent, the observation pack omits hard-axiom / hotspot
blocks. GOAL is the current proof-node formula.
The diagnoser chooses no_action (leave generation alone), new_direction
(text only), or revise_candidate (pending formulas plus notes).
"""

from __future__ import annotations

import json
import logging
import re
import time
from typing import Any, Dict, List, Optional, Sequence, Set

from cvc5_runner import classify_difficulty_term
from exp_flags import feedback_llm_hints_enabled, repair_hints_enabled
from exp_stats import add_llm_time, log_exp, record_llm_generation
from llm_time_budget import invoke_configured_chat
from obligation_tree import (
    last_normal_tree,
    load_lemma_library,
    normalize_lemma_formula,
)

HINTS_KIND = "llm_feedback_hints"
HINT_NO_ACTION = "no_action"
HINT_NEW_DIRECTION = "new_direction"
HINT_REVISE_CANDIDATE = "revise_candidate"
HINT_MODES = (HINT_NO_ACTION, HINT_NEW_DIRECTION, HINT_REVISE_CANDIDATE)
MAX_AXIOMS = 4
MAX_EVIDENCE = 8
MAX_HINT_CHARS = 900
MIN_HINT_CHARS = 24
# Block HD-only steering of the first lemma generation.
MIN_USELESS_GROUPS_FOR_HINTS = 1
# Soft ceilings above full706 llmhint maxima (library≤18, cum-unique
# unproved proxy≤15). Pathological blow-ups still truncated; prefer the
# newest entries, not random sampling.
MAX_REVIVE_CANDIDATES = 24
MAX_LIBRARY_SHOW = 24
MAX_REVIVE_OUT = 24
MAX_CANDIDATES = 12
_HD_USEFULNESS_CONTEXTS = frozenset({"usefulness_check", "usefulness"})

_JSON_FENCE = re.compile(r"```(?:json)?\s*(\{.*?\})\s*```", re.DOTALL | re.IGNORECASE)
_ANY_FENCE = re.compile(r"```(?:\w+)?\s*(.*?)\s*```", re.DOTALL)
_JSON_OBJECT = re.compile(r"\{.*\}", re.DOTALL)
_ID_TOKEN = re.compile(r"\b([EAGCR]\d+)\b")

HINTS_SYSTEM = """You help repair a failed SMT inductive attempt.
You receive blocked solver observations for your reading only.
Rules:
- difficulty ranks runtime hotspots; not proof necessity.
- search-change stats are weak signals; for reference only.
- Revival candidates are unproved. They may be true or false, useful or useless;
  they are not known true and not library axioms. Do not invent formulas.
- The lemma library has new proved axioms. Re-evaluate the unproved revival candidates
  in that new context.
- Choose exactly one mode:
  NO_ACTION: generation should proceed as usual; do not steer it.
  NEW_DIRECTION: none of the revival candidates are worth bringing back;
    explain a different lemma shape in the note.
  REVISE_CANDIDATE: select a few pool formulas as unproved references;
    the lemma generator decides how to use them.
- When you mention a formula, quote it in full. Never refer to candidates by id."""

HINTS_USER_TEMPLATE = """From the observations below, choose a mode and write a short note.

Return ONLY one JSON object:
{{
  "mode": "NO_ACTION" | "NEW_DIRECTION" | "REVISE_CANDIDATE",
  "note": "shown to the lemma generator unless mode is NO_ACTION",
  "revive": [{{"formula": "(forall ...)", "note": "how this formula might help"}}]
}}
NO_ACTION: leave note/revive empty; the generator is not shown this block.
NEW_DIRECTION: fill note only (no revive). Tell the generator to try a new shape.
REVISE_CANDIDATE: copy formulas verbatim from REVIVAL CANDIDATES
(at most {max_revive}; prefer the most relevant); optional per-formula note.
Unselected pool formulas are omitted.
LAST CANDIDATE LEMMAS are the previous generation round.
REVIVAL CANDIDATES are historical unproved lemmas, not only last round.

{body}
""".replace("{max_revive}", str(MAX_REVIVE_OUT))


def _prompt_formula(formula: Optional[str]) -> str:
    """Whitespace-normalized formula for diagnoser I/O; do not truncate."""
    return normalize_lemma_formula(formula or "")


def _hd_hints(hints: Sequence[dict]) -> List[dict]:
    out: List[dict] = []
    for hint in hints or []:
        if not isinstance(hint, dict):
            continue
        if str(hint.get("kind") or "") == "high_difficulty_assertions":
            out.append(hint)
    return out


def _is_usefulness_hd(hint: dict) -> bool:
    ctx = str(hint.get("context") or "")
    if ctx in _HD_USEFULNESS_CONTEXTS:
        return True
    return str(hint.get("attempt_id") or "").startswith("usefulness")


def _latest_hd_hint(failed_data: dict) -> Optional[dict]:
    """HD from the last useless group's usefulness dump only.

    Skip initial-goal / node-level fallbacks: those dumps predate later
    candidate sets and library growth.
    """
    groups = failed_data.get("useless_lemma_groups") or []
    if not groups or not isinstance(groups[-1], dict):
        return None
    for hint in reversed(_hd_hints(groups[-1].get("repair_hints") or [])):
        if _is_usefulness_hd(hint):
            return hint
    return None


def has_difficulty_observations(failed_data: Optional[dict]) -> bool:
    """True when we already have HD axioms or a cached difficulty dump."""
    data = failed_data if isinstance(failed_data, dict) else {}
    hd = _latest_hd_hint(data)
    if hd and (hd.get("hard_axioms") or hd.get("goal_fragments")):
        return True
    base = data.get("baseline_diag")
    if isinstance(base, dict) and base.get("difficulty"):
        return True
    return False


def llm_hints_eligible(failed_data: Optional[dict]) -> bool:
    """True when hints may inject: enough useless groups (not first gen)."""
    groups = (failed_data or {}).get("useless_lemma_groups") or []
    return len(groups) >= MIN_USELESS_GROUPS_FOR_HINTS


def has_hint_opportunity(
    failed_data: Optional[dict],
    *,
    library: Optional[Sequence[dict]] = None,
    prev_library_ids: Optional[Sequence[str]] = None,
) -> bool:
    """True when unproved revival candidates exist *and* the library grew.

    Missing ``prev_library_ids`` is an empty-library baseline: any current
    library id counts as a change (the first diagnoser call).
    """
    if not _revival_candidate_items(failed_data or {}):
        return False
    prev = [] if prev_library_ids is None else list(prev_library_ids)
    return bool(_library_show_items(library or [], prev_ids=prev))


def _recorded_library_baseline(failed_data: Optional[dict]) -> List[str]:
    """Last snapshotted library ids; missing record means empty library."""
    rec = (failed_data or {}).get("llm_hints")
    if not isinstance(rec, dict) or "library_ids" not in rec:
        return []
    return [str(x) for x in (rec.get("library_ids") or []) if x]


def _persist_library_baseline(
    base_path: str,
    goal_name: str,
    library: Sequence[dict],
    *,
    load_failed_lemmas,
    save_failed_lemmas,
) -> None:
    """Remember current library ids so the next growth can satisfy the AND gate."""
    ids = _library_ids(library)
    failed_data = load_failed_lemmas(base_path, goal_name)
    rec = failed_data.get("llm_hints")
    rec = dict(rec) if isinstance(rec, dict) else {}
    rec["library_ids"] = ids
    failed_data["llm_hints"] = rec
    save_failed_lemmas(base_path, goal_name, failed_data)


def _library_fingerprint(library: Sequence[dict]) -> str:
    ids = [
        str(item.get("id") or "")
        for item in (library or [])
        if isinstance(item, dict) and item.get("id")
    ]
    if not ids:
        return "lib0"
    return f"lib{len(ids)}:{ids[-1]}"


def _library_ids(library: Sequence[dict]) -> List[str]:
    return [
        str(item.get("id") or "")
        for item in (library or [])
        if isinstance(item, dict) and item.get("id")
    ]


def _library_show_items(
    library: Sequence[dict],
    *,
    prev_ids: Optional[Sequence[str]] = None,
) -> List[Dict[str, str]]:
    """Library entries to show. ``prev_ids is not None``: only ids not in that baseline."""
    source = list(library or [])
    if prev_ids is not None:
        prev = {str(x) for x in prev_ids if x}
        source = [
            item for item in source
            if isinstance(item, dict) and str(item.get("id") or "") not in prev
        ]
    else:
        source = source[-MAX_LIBRARY_SHOW:]
    items: List[Dict[str, str]] = []
    for item in source[-MAX_LIBRARY_SHOW:]:
        if not isinstance(item, dict):
            continue
        formula = str(item.get("formula") or "").strip()
        if not formula:
            continue
        items.append({
            "id": str(item.get("id") or ""),
            "formula": _prompt_formula(formula),
            "role": str(item.get("role") or ""),
            "new": prev_ids is not None,
        })
    return items


def _revival_candidate_items(failed_data: dict) -> List[Dict[str, str]]:
    """Soft-failed lemmas only (unproved/timeout); never invalid.

    If the pool exceeds ``MAX_REVIVE_CANDIDATES``, keep the newest entries
    (list tail), not a random sample.
    """
    invalid_keys: Set[str] = set()
    for rec in failed_data.get("invalid_lemmas") or []:
        if isinstance(rec, dict):
            raw = str(rec.get("lemma") or "")
        else:
            raw = str(rec or "")
        key = normalize_lemma_formula(raw)
        if key:
            invalid_keys.add(key)
    out: List[Dict[str, str]] = []
    seen: Set[str] = set()
    for rec in failed_data.get("unproved_lemmas") or []:
        if not isinstance(rec, dict):
            continue
        formula = str(rec.get("lemma") or "").strip()
        if not formula:
            continue
        key = normalize_lemma_formula(formula)
        if not key or key in seen or key in invalid_keys:
            continue
        status = _normalize_prove_status(rec.get("status") or "unproved")
        if status == "invalid":
            continue
        seen.add(key)
        out.append({
            "formula": _prompt_formula(formula),
            "status": status or "unproved",
        })
    if len(out) > MAX_REVIVE_CANDIDATES:
        out = out[-MAX_REVIVE_CANDIDATES:]
    for i, item in enumerate(out, 1):
        item["id"] = f"R{i}"
    return out


def _source_attempt_id(
    failed_data: dict,
    *,
    library: Optional[Sequence[dict]] = None,
) -> str:
    hd = _latest_hd_hint(failed_data)
    if hd and hd.get("attempt_id"):
        base = str(hd["attempt_id"])
    else:
        groups = failed_data.get("useless_lemma_groups") or []
        if groups and isinstance(groups[-1], dict):
            g = groups[-1]
            base = (
                f"group:{g.get('status')}:{len(g.get('lemmas') or [])}:"
                f"{g.get('difficulty_dump_complete')}"
            )
        else:
            base = "baseline"
    n_unproved = len(failed_data.get("unproved_lemmas") or [])
    return f"{base}|{_library_fingerprint(library or [])}|u{n_unproved}"


def _formula_evidence_hint(failed_data: dict) -> Optional[dict]:
    target = _source_attempt_id(failed_data)
    for hint in failed_data.get("repair_hints") or []:
        if not isinstance(hint, dict):
            continue
        if str(hint.get("kind") or "") != "solver_formula_evidence":
            continue
        if str(hint.get("attempt_id") or "") == target or not hint.get("attempt_id"):
            return hint
    groups = failed_data.get("useless_lemma_groups") or []
    if groups and isinstance(groups[-1], dict):
        for hint in groups[-1].get("repair_hints") or []:
            if isinstance(hint, dict) and str(hint.get("kind") or "") == "solver_formula_evidence":
                return hint
    return None


def _slim_stats(blob):
    if not isinstance(blob, dict):
        return {}
    out = {}
    for key in ("CONJ_TOTAL", "INST_TOTAL", "QUANTIFIERS_SKOLEMIZE"):
        if key in blob:
            out[key] = int(blob.get(key) or 0)
    return out


def _stats_direction(before, after):
    if after is None:
        return "?"
    if before is None:
        return str(after)
    b, a = int(before), int(after)
    if a > int(round(b * 1.1)) and a > b:
        tag = "↑"
    elif a < int(round(b * 0.9)) and a < b:
        tag = "↓"
    else:
        tag = "flat"
    return f"{b} → {a} ({tag})"


def _normalize_prove_status(raw):
    """Map stored statuses to short tokens; no editorial 'not useful' gloss."""
    s = str(raw or "").strip().lower()
    if not s:
        return ""
    if s in ("proved", "unsat", "valid"):
        return "proved"
    if s == "invalid" or "invalid" in s:
        return "invalid"
    if s in ("failed", "sat"):
        return "failed"
    if "timeout" in s:
        return "timeout"
    if "unproved" in s or s in ("unknown", "incomplete"):
        return "unproved"
    return s.replace("useful_but_", "").replace("_", " ")[:24]


def _prove_status_lookup(failed_data):
    """formula → proved|failed|timeout|unproved|invalid from existing sidecar data."""
    out = {}
    for rec in failed_data.get("unproved_lemmas") or []:
        if not isinstance(rec, dict):
            continue
        formula = str(rec.get("lemma") or "").strip()
        if not formula:
            continue
        status = _normalize_prove_status(rec.get("status") or "unproved")
        if status:
            out[formula] = status
    for rec in failed_data.get("invalid_lemmas") or []:
        if isinstance(rec, dict):
            formula = str(rec.get("lemma") or "").strip()
        else:
            formula = str(rec or "").strip()
        if formula:
            out[formula] = "invalid"
    try:
        from obligation_tree import last_normal_tree
        tree = last_normal_tree(failed_data.get("obligation"))
    except Exception:
        tree = None

    def walk(node):
        if not isinstance(node, dict):
            return
        if str(node.get("role") or "") == "lemma":
            formula = str(node.get("formula") or "").strip()
            status = _normalize_prove_status(node.get("status"))
            if formula and status in ("proved", "failed", "timeout", "unproved", "invalid"):
                # Prefer tree prove/fail/invalid over unproved_lemmas gloss.
                if formula not in out or status in ("proved", "failed", "invalid"):
                    out[formula] = status
        for child in node.get("children") or []:
            walk(child)

    if tree:
        walk(tree)
    return out


def _attributed_id_set(group):
    if not isinstance(group, dict):
        return set()
    ids = group.get("attributed_ids") or []
    if isinstance(ids, (list, tuple, set)):
        return {str(x) for x in ids if x}
    return set()


def _candidate_id_for_formula(group, formula, index):
    """Prefer stored candidate_ids map; else C{index}."""
    if isinstance(group, dict):
        mapping = group.get("candidate_ids")
        if isinstance(mapping, dict):
            for key, val in mapping.items():
                if str(val) == formula and str(key).startswith("C"):
                    return str(key)
                if str(key) == formula and str(val).startswith("C"):
                    return str(val)
    return f"C{index}"


def _current_node_goal(
    failed_data,
    *,
    current_goal: Optional[str] = None,
    hd: Optional[dict] = None,
) -> str:
    """Full formula of the node currently being proved.

    Prefer the live node formula, then the obligation-tree root, then
    solver-extracted goal_term. Difficulty ``goal_fragments`` are last:
    they can be dump pieces rather than the whole current goal.
    """
    text = normalize_lemma_formula(current_goal or "")
    if text:
        return text
    tree = last_normal_tree((failed_data or {}).get("obligation"))
    if isinstance(tree, dict):
        text = normalize_lemma_formula(str(tree.get("formula") or ""))
        if text:
            return text
    base = (failed_data or {}).get("baseline_diag")
    if isinstance(base, dict):
        text = normalize_lemma_formula(str(base.get("goal_term") or ""))
        if text:
            return text
    hd = hd or {}
    frags = hd.get("goal_fragments") or []
    if frags:
        return normalize_lemma_formula(str(frags[0] or ""))
    return ""


def build_observation_pack(
    failed_data,
    *,
    library: Optional[Sequence[dict]] = None,
    prev_library_ids: Optional[Sequence[str]] = None,
    current_goal: Optional[str] = None,
):
    """Pack goal / optional hard axioms / last candidates / library / revive pool.

    Difficulty is optional. None only when there is no goal, no last group,
    no library delta to show, and no revival pool. Caller should also gate
    on ``llm_hints_eligible``. Goal comes from the current proof node
    (``current_goal`` or the obligation-tree root), not from HD.
    """
    hd = _latest_hd_hint(failed_data) or {}
    base = failed_data.get("baseline_diag") if isinstance(failed_data.get("baseline_diag"), dict) else {}
    goal = _current_node_goal(failed_data, current_goal=current_goal, hd=hd)
    axioms: List[str] = []
    for raw in (hd.get("hard_axioms") or []):
        term = str(raw or "")
        if not term:
            continue
        if classify_difficulty_term(term, goal) != "axiom":
            continue
        axioms.append(term)
        if len(axioms) >= MAX_AXIOMS:
            break

    scores = hd.get("hard_axiom_scores") if isinstance(hd.get("hard_axiom_scores"), dict) else {}
    rarely = {str(a) for a in (hd.get("rarely_instantiated") or []) if a}
    ranked = sorted(
        ((str(ax), int(scores.get(str(ax)) or 0)) for ax in axioms),
        key=lambda pair: -pair[1],
    )
    hard_axioms = []
    for i, (ax, score) in enumerate(ranked, 1):
        hard_axioms.append({
            "formula": _prompt_formula(ax),
            "rank": i,
            "score": score,
            "rarely_instantiated": normalize_lemma_formula(ax) in {
                normalize_lemma_formula(r) for r in rarely
            },
        })

    groups = failed_data.get("useless_lemma_groups") or []
    group = groups[-1] if groups and isinstance(groups[-1], dict) else None
    dump_complete = bool(group.get("difficulty_dump_complete")) if group else bool(base.get("difficulty"))
    prove_lookup = _prove_status_lookup(failed_data)
    attributed = _attributed_id_set(group)

    candidates = []
    if group:
        raw_lemmas = [str(x) for x in (group.get("lemmas") or []) if x][:MAX_CANDIDATES]
        for i, lemma in enumerate(raw_lemmas, 1):
            cid = _candidate_id_for_formula(group, lemma, i)
            entry = {
                "id": cid,
                "formula": _prompt_formula(lemma),
                "group_failed": True,
                "attributed": cid in attributed,
            }
            prove = prove_lookup.get(lemma)
            if not prove:
                target = normalize_lemma_formula(lemma)
                for form, st in prove_lookup.items():
                    if normalize_lemma_formula(form) == target:
                        prove = st
                        break
            entry["prove"] = prove or "unknown"
            candidates.append(entry)

    mix_stats = _slim_stats(group.get("mix_stats") if group else None)
    base_stats = _slim_stats(base.get("stats"))
    stats_delta = None
    if mix_stats:
        stats_delta = {
            key: _stats_direction(base_stats.get(key), mix_stats.get(key))
            for key in ("CONJ_TOTAL", "INST_TOTAL", "QUANTIFIERS_SKOLEMIZE")
            if key in mix_stats
        }

    lib_items = _library_show_items(library or [], prev_ids=prev_library_ids)
    revive_pool = _revival_candidate_items(failed_data)
    if not (
        goal
        or hard_axioms
        or candidates
        or lib_items
        or revive_pool
    ):
        return None

    evidence = []
    for i, ax in enumerate(hard_axioms[:MAX_EVIDENCE], 1):
        evidence.append({
            "id": f"E{i}",
            "kind": "difficulty",
            "profile": str(hd.get("context") or base.get("strategy") or ""),
            "complete": dump_complete,
            "fact": f"difficulty rank {ax['rank']} (d={ax['score']})",
            "formula": ax["formula"],
            "related": "",
        })

    return {
        "attempt_id": _source_attempt_id(failed_data, library=library),
        "dump_complete": dump_complete,
        "goal": {
            "id": "G1",
            "formula": _prompt_formula(goal) if goal else "",
        },
        "axioms": [
            {"id": f"A{i}", "formula": ax["formula"]}
            for i, ax in enumerate(hard_axioms, 1)
        ],
        "hard_axioms": hard_axioms,
        "evidence": evidence,
        "previous_candidates": candidates,
        "library": lib_items,
        "library_new": prev_library_ids is not None,
        "revival_candidates": revive_pool,
        "group_status": str((group or {}).get("status") or base.get("status") or ""),
        "status": str((group or {}).get("status") or base.get("status") or ""),
        "stats_delta": stats_delta,
    }


def format_observation_prompt_body(pack):
    """Blocked observations for the hints LLM (no dump_complete note block)."""
    lines = []
    goal = pack.get("goal") or {}
    lines.append("=== GOAL ===")
    lines.append(f"  {goal.get('formula') or '(unknown)'}")

    hard = pack.get("hard_axioms") or []
    axioms = pack.get("axioms") or []
    if hard or axioms:
        lines.append("")
        lines.append("=== HARD AXIOMS (last usefulness dump, hotspots not proof dependencies) ===")
        if hard:
            for ax in hard:
                bits = [f"rank {ax.get('rank')}"]
                if ax.get("score"):
                    bits.append(f"d={ax.get('score')}")
                if ax.get("rarely_instantiated"):
                    bits.append("rarely instantiated in this dump")
                lines.append(f"  - {ax.get('formula')}")
                lines.append(f"    [{', '.join(bits)}]")
        else:
            for ax in axioms:
                lines.append(f"  - {ax.get('formula')}")

    prev = pack.get("previous_candidates") or []
    if prev:
        lines.append("")
        lines.append("=== LAST CANDIDATE LEMMAS (previous generation round; usefulness: A ∧ these → goal) ===")
        group_status = pack.get("group_status") or pack.get("status") or "?"
        lines.append(f"  Group result: {group_status} (goal not proved with this candidates)")
        show_hotspot = bool(pack.get("hard_axioms") or pack.get("axioms"))
        for item in prev:
            lines.append(f"  - {item.get('formula')}")
            outcome_bits = ["in failed group"]
            if show_hotspot:
                if item.get("attributed"):
                    outcome_bits.append("attributed=yes (touched a hotspot)")
                else:
                    outcome_bits.append("attributed=no")
            prove = item.get("prove") or "unknown"
            # Bare token: proved|failed|timeout|unproved|invalid|unknown.
            outcome_bits.append(f"prove={prove}")
            lines.append(f"    outcome: {'; '.join(outcome_bits)}")

    delta = pack.get("stats_delta")
    if isinstance(delta, dict) and delta:
        lines.append("")
        lines.append("=== SEARCH CHANGE VS BASELINE (for reference) ===")
        parts = []
        for key, label in (
            ("CONJ_TOTAL", "CONJ"),
            ("INST_TOTAL", "INST"),
            ("QUANTIFIERS_SKOLEMIZE", "SKOL"),
        ):
            if key in delta:
                parts.append(f"{label}: {delta[key]}")
        if parts:
            lines.append("  " + "   ".join(parts))

    lib_items = pack.get("library") or []
    lines.append("")
    if pack.get("library_new"):
        lines.append("=== LEMMA LIBRARY (new since last hint; context change) ===")
    else:
        lines.append("=== LEMMA LIBRARY (recent proved; context so far) ===")
    if lib_items:
        for item in lib_items:
            role = item.get("role") or ""
            role_bit = f" [{role}]" if role else ""
            lines.append(f"  - {item.get('formula')}{role_bit}")
    else:
        lines.append("  (no new library lemmas)" if pack.get("library_new") else "  (empty)")

    revive_pool = pack.get("revival_candidates") or []
    lines.append("")
    lines.append(
        "=== REVIVAL CANDIDATES (historical unproved lemmas, not only last round) ==="
    )
    if revive_pool:
        for item in revive_pool:
            status = item.get("status") or "unproved"
            lines.append(f"  - {item.get('formula')}  [status={status}]")
    else:
        lines.append("  (none)")

    return "\n".join(lines)


def _strip_orphan_ids(text: str) -> str:
    """Drop bare E/A/G/C/R tokens so generation prompts stay self-contained."""
    if not text:
        return ""
    cleaned = _ID_TOKEN.sub("", text)
    cleaned = re.sub(r"\s{2,}", " ", cleaned)
    cleaned = re.sub(r"\s+([,.;:])", r"\1", cleaned)
    return cleaned.strip(" ,;:")


def _normalize_hint_text(text: str) -> str:
    cleaned = _strip_orphan_ids((text or "").strip())
    if len(cleaned) > MAX_HINT_CHARS:
        cleaned = cleaned[: MAX_HINT_CHARS - 3].rstrip() + "..."
    return cleaned


def _text_from_legacy_json(data: dict) -> str:
    """Collapse older multi-field JSON into one prose note."""
    for key in ("text", "hint", "analysis", "note", "advice"):
        val = data.get(key)
        if isinstance(val, str) and val.strip():
            return val.strip()
    hyps = data.get("hypotheses")
    if not isinstance(hyps, list):
        return ""
    parts: List[str] = []
    for hyp in hyps[:2]:
        if not isinstance(hyp, dict):
            continue
        chunk = str(hyp.get("interpretation") or "").strip()
        alt = str(hyp.get("alternative_explanation") or "").strip()
        conn = str(hyp.get("goal_connection") or "").strip()
        cand = str(hyp.get("candidate_lemma") or "").strip()
        if alt:
            chunk = f"{chunk} Alternative: {alt}" if chunk else alt
        if conn:
            chunk = f"{chunk} Goal link: {conn}" if chunk else conn
        if cand:
            chunk = (
                f"{chunk} Suggested shape: {_prompt_formula(cand)}"
                if chunk
                else f"Suggested shape: {_prompt_formula(cand)}"
            )
        if chunk:
            parts.append(chunk)
    return " ".join(parts).strip()


def _filter_revive_list(
    raw_items: Any,
    allowed: Sequence[Any],
) -> List[Dict[str, str]]:
    """Keep revive formulas that are in the offered pool.

    Legacy ``action: hold`` is dropped (same as unselected). Other action
    fields are ignored.
    """
    if not isinstance(raw_items, list):
        return []
    by_id: Dict[str, dict] = {}
    by_norm: Dict[str, dict] = {}
    for cand in allowed or []:
        if isinstance(cand, dict):
            formula = str(cand.get("formula") or "").strip()
            cid = str(cand.get("id") or "").strip()
        else:
            formula = str(cand or "").strip()
            cid = ""
        if not formula:
            continue
        rec = {
            "id": cid,
            "formula": _prompt_formula(formula),
        }
        if cid:
            by_id[cid] = rec
        by_norm[normalize_lemma_formula(formula)] = rec
    out: List[Dict[str, str]] = []
    seen: Set[str] = set()
    for item in raw_items:
        formula = ""
        cid = ""
        action = ""
        why = ""
        if isinstance(item, dict):
            cid = str(item.get("id") or "").strip()
            formula = str(item.get("formula") or "").strip()
            action = str(item.get("action") or "").strip().lower()
            why = str(item.get("note") or item.get("why") or item.get("reason") or "").strip()
        else:
            formula = str(item or "").strip()
        if action == "hold":
            continue
        match = None
        if cid and cid in by_id:
            match = by_id[cid]
        elif formula:
            match = by_norm.get(normalize_lemma_formula(formula))
        if not match:
            continue
        key = normalize_lemma_formula(match["formula"])
        if key in seen:
            continue
        seen.add(key)
        rec = {
            "id": match.get("id") or cid,
            "formula": match["formula"],
        }
        if why:
            rec["note"] = why[:240]
        out.append(rec)
        if len(out) >= MAX_REVIVE_OUT:
            break
    return out


def _normalize_hint_mode(raw: Any, *, n_revive: int, has_text: bool) -> str:
    token = str(raw or "").strip().lower().replace("-", "_").replace(" ", "_")
    aliases = {
        "no_action": HINT_NO_ACTION,
        "noaction": HINT_NO_ACTION,
        "none": HINT_NO_ACTION,
        "skip": HINT_NO_ACTION,
        "new_direction": HINT_NEW_DIRECTION,
        "newdirection": HINT_NEW_DIRECTION,
        "new": HINT_NEW_DIRECTION,
        "revise_candidate": HINT_REVISE_CANDIDATE,
        "revise_candidates": HINT_REVISE_CANDIDATE,
        "revise": HINT_REVISE_CANDIDATE,
        "revive": HINT_REVISE_CANDIDATE,
    }
    mode = aliases.get(token, "")
    if not mode:
        if n_revive:
            mode = HINT_REVISE_CANDIDATE
        elif has_text:
            mode = HINT_NEW_DIRECTION
        else:
            mode = HINT_NO_ACTION
    if mode == HINT_REVISE_CANDIDATE and not n_revive:
        mode = HINT_NEW_DIRECTION if has_text else HINT_NO_ACTION
    if mode == HINT_NEW_DIRECTION and not has_text:
        mode = HINT_NO_ACTION
    return mode


def parse_llm_feedback_hints(
    raw: Optional[str],
    *,
    revival_candidates: Optional[Sequence[Any]] = None,
) -> Optional[Dict[str, Any]]:
    """Parse into ``{\"mode\", \"text\", \"revive\": [{formula, note}]}``."""
    text = (raw or "").strip()
    if not text:
        return None

    revive_raw: Any = []
    note = ""
    mode_raw = ""

    fenced = _ANY_FENCE.search(text)
    if fenced and text.strip().startswith("```"):
        text = fenced.group(1).strip()

    blob = None
    if text.startswith("{") or _JSON_FENCE.search(raw or ""):
        m = _JSON_FENCE.search(raw or "")
        if m:
            blob = m.group(1)
        else:
            m2 = _JSON_OBJECT.search(text)
            if m2:
                blob = m2.group(0)
    if blob:
        try:
            data = json.loads(blob)
        except json.JSONDecodeError:
            data = None
        if isinstance(data, dict):
            note = (
                str(data.get("note") or data.get("text") or "").strip()
                or _text_from_legacy_json(data)
            )
            revive_raw = data.get("revive") or data.get("revival") or []
            mode_raw = data.get("mode") or ""
            if str(data.get("kind") or "") in (
                "NO_ACTION", "NEW_DIRECTION", "REVISE_CANDIDATE",
                HINT_NO_ACTION, HINT_NEW_DIRECTION, HINT_REVISE_CANDIDATE,
            ):
                mode_raw = mode_raw or data.get("kind")
        else:
            note = text
    else:
        note = text

    cleaned = _normalize_hint_text(note)
    allowed = list(revival_candidates or [])
    revive = _filter_revive_list(revive_raw, allowed) if allowed else []
    mode = _normalize_hint_mode(
        mode_raw, n_revive=len(revive), has_text=len(cleaned) >= MIN_HINT_CHARS,
    )
    if mode == HINT_NO_ACTION:
        return {"mode": mode, "text": "", "revive": []}
    if mode == HINT_NEW_DIRECTION:
        if len(cleaned) < MIN_HINT_CHARS:
            return None
        return {"mode": mode, "text": cleaned, "revive": []}
    if len(revive) < 1:
        return None
    return {"mode": mode, "text": cleaned, "revive": revive}


def hint_text(hints: Any) -> str:
    """Extract display text from stored hints (new or legacy)."""
    if isinstance(hints, str):
        return _normalize_hint_text(hints)
    if not isinstance(hints, dict):
        return ""
    if hints.get("text") or hints.get("note"):
        return _normalize_hint_text(str(hints.get("text") or hints.get("note") or ""))
    return _normalize_hint_text(_text_from_legacy_json(hints))


def hint_revive_entries(hints: Any) -> List[Dict[str, str]]:
    if not isinstance(hints, dict):
        return []
    items = hints.get("revive") or hints.get("revival") or []
    if not isinstance(items, list):
        return []
    out: List[Dict[str, str]] = []
    for item in items:
        if isinstance(item, dict):
            formula = str(item.get("formula") or "").strip()
            action = str(item.get("action") or "").strip().lower()
            if action == "hold":
                continue
            if not formula:
                continue
            out.append({
                "id": str(item.get("id") or ""),
                "formula": _prompt_formula(formula),
            })
            note = str(item.get("note") or item.get("why") or "").strip()
            if note:
                out[-1]["note"] = note[:240]
        else:
            formula = str(item or "").strip()
            if formula:
                out.append({
                    "id": "",
                    "formula": _prompt_formula(formula),
                })
        if len(out) >= MAX_REVIVE_OUT:
            break
    return out


def hint_revive_list(hints: Any) -> List[str]:
    """Selected pending formulas (legacy hold excluded)."""
    return [item["formula"] for item in hint_revive_entries(hints)]


def hint_mode(hints: Any) -> str:
    """Stored or inferred mode: no_action / new_direction / revise_candidate."""
    if isinstance(hints, str):
        text = _normalize_hint_text(hints)
        return HINT_NEW_DIRECTION if len(text) >= MIN_HINT_CHARS else HINT_NO_ACTION
    if not isinstance(hints, dict):
        return HINT_NO_ACTION
    entries = hint_revive_entries(hints)
    text = hint_text(hints)
    return _normalize_hint_mode(
        hints.get("mode"),
        n_revive=len(entries),
        has_text=len(text) >= MIN_HINT_CHARS,
    )


def _hints_are_cached(hints: Any) -> bool:
    if hint_mode(hints) == HINT_NO_ACTION:
        return isinstance(hints, dict) and str(hints.get("mode") or "") == HINT_NO_ACTION
    return bool(hint_text(hints) or hint_revive_list(hints))


def format_llm_hints_lines(
    record: Optional[dict],
    *,
    indent: str = "    ",
) -> List[str]:
    """Lines for SOLVER HINTS nested under LAST ATTEMPT / INITIAL SOLVE."""
    if not isinstance(record, dict):
        return []
    hints = record.get("hints")
    mode = hint_mode(hints)
    if mode == HINT_NO_ACTION:
        return []
    text = hint_text(hints)
    entries = hint_revive_entries(hints) if mode == HINT_REVISE_CANDIDATE else []
    if not text and not entries:
        return []
    ind = indent
    sub = indent + "  "
    if mode == HINT_NEW_DIRECTION:
        return [
            f"{ind}SOLVER HINTS (rejectable; new direction):",
            (
                f"{sub}Previous unproved candidates are not worth reviving as-is. "
                f"Propose a different lemma shape."
            ),
            f"{sub}{text}",
        ]
    lines = [
        f"{ind}SOLVER HINTS (rejectable; pending candidates):",
        (
            f"{sub}Pending formulas are unproved: they may or may not be true, "
            f"and may or may not help the CURRENT goal. They are not library "
            f"axioms. Decide for yourself how to use each one, or ignore them."
        ),
    ]
    if text:
        lines.append(f"{sub}{text}")
    if entries:
        lines.append(f"{sub}pending (unproved; not assumed true or useful):")
        for i, item in enumerate(entries, 1):
            lines.append(f"{sub}  {i}. {item.get('formula')}")
            note = item.get("note") or ""
            if note:
                lines.append(f"{sub}     note: {note}")
    return lines


def format_llm_hints_for_prompt(record: Optional[dict]) -> str:
    """Standalone block (tests / callers); prefer nesting via format_attempt_feedback."""
    lines = format_llm_hints_lines(record, indent="")
    if not lines:
        return ""
    return "\n" + "\n".join(lines)


def maybe_refresh_llm_hints(
    base_path: str,
    goal_name: str,
    *,
    llm: Any,
    config: dict,
    load_failed_lemmas,
    save_failed_lemmas,
    backend: str = "cvc5",
    current_goal: Optional[str] = None,
) -> Optional[dict]:
    """Run LLM-hints when flag is on and usefulness failed.

    Skips Vampire, fewer than ``MIN_USELESS_GROUPS_FOR_HINTS`` groups,
    missing unproved pool or missing library growth vs the last baseline
    (first call: vs empty library),
    and when stored hints already match the current attempt_id. Difficulty
    is optional (HD omitted from the pack). ``current_goal`` is the formula
    of the node being proved.
    """
    if not feedback_llm_hints_enabled():
        return None
    if not repair_hints_enabled():
        return None
    if str(backend or "").lower() != "cvc5":
        return None
    failed_data = load_failed_lemmas(base_path, goal_name)
    if not llm_hints_eligible(failed_data):
        log_exp(
            "llm_feedback_hints_skip",
            goal=goal_name,
            reason="need_useless_group",
            n_groups=len(failed_data.get("useless_lemma_groups") or []),
        )
        return None
    library = load_lemma_library(base_path)
    baseline = _recorded_library_baseline(failed_data)
    pack = build_observation_pack(
        failed_data,
        library=library,
        prev_library_ids=baseline,
        current_goal=current_goal,
    )
    if pack is None:
        _persist_library_baseline(
            base_path, goal_name, library,
            load_failed_lemmas=load_failed_lemmas,
            save_failed_lemmas=save_failed_lemmas,
        )
        log_exp(
            "llm_feedback_hints_skip",
            goal=goal_name,
            reason="empty_pack",
        )
        return None
    attempt_id = str(pack.get("attempt_id") or "")
    existing = failed_data.get("llm_hints")
    if (
        isinstance(existing, dict)
        and str(existing.get("attempt_id") or "") == attempt_id
        and _hints_are_cached(existing.get("hints"))
    ):
        return existing
    if not has_hint_opportunity(
        failed_data, library=library, prev_library_ids=baseline,
    ):
        _persist_library_baseline(
            base_path, goal_name, library,
            load_failed_lemmas=load_failed_lemmas,
            save_failed_lemmas=save_failed_lemmas,
        )
        log_exp(
            "llm_feedback_hints_skip",
            goal=goal_name,
            reason="no_opportunity",
            n_unproved=len(failed_data.get("unproved_lemmas") or []),
            library_new=bool(pack.get("library") or []),
            n_prev_library=len(baseline),
        )
        return None

    user_body = format_observation_prompt_body(pack)
    messages = [
        {"role": "system", "content": HINTS_SYSTEM},
        {"role": "user", "content": HINTS_USER_TEMPLATE.format(body=user_body)},
    ]
    started = time.time()
    raw = ""
    parse_error = None
    hints = None
    try:
        response, budget = invoke_configured_chat(llm, messages, config)
        if budget.apply:
            log_exp(
                "llm_budget",
                goal=goal_name,
                timeout_s=budget.timeout_s,
                http_retries=budget.max_retries,
                phase="feedback_llm_hints",
            )
        raw = getattr(response, "content", "") or ""
        revive_pool = [
            item for item in (pack.get("revival_candidates") or [])
            if isinstance(item, dict) and item.get("formula")
        ]
        hints = parse_llm_feedback_hints(raw, revival_candidates=revive_pool)
        if hints is None:
            parse_error = "empty_or_short_hint"
    except Exception as exc:
        parse_error = str(exc)
        logging.warning("LLM feedback hints failed: %s", exc)

    elapsed = time.time() - started
    add_llm_time(base_path, elapsed)
    record_llm_generation(
        base_path,
        goal=goal_name,
        strategy="feedback_llm_hints",
        prompt_folder="",
        smt_file="",
        system_text=HINTS_SYSTEM,
        user_text=messages[1]["content"],
        feedback="",
        lemmas=hint_revive_list(hints or {}),
        elapsed=elapsed,
        parse_error=parse_error,
        raw=raw,
    )
    if hints is None:
        log_exp(
            "llm_feedback_hints",
            goal=goal_name,
            ok=False,
            reason=parse_error or "empty",
            attempt_id=attempt_id,
        )
        return None

    record = {
        "kind": HINTS_KIND,
        "attempt_id": attempt_id,
        "dump_complete": bool(pack.get("dump_complete")),
        "library_fingerprint": _library_fingerprint(library),
        "library_ids": _library_ids(library),
        "hints": hints,
    }
    failed_data = load_failed_lemmas(base_path, goal_name)
    failed_data["llm_hints"] = record
    save_failed_lemmas(base_path, goal_name, failed_data)
    log_exp(
        "llm_feedback_hints",
        goal=goal_name,
        ok=True,
        attempt_id=attempt_id,
        hint_chars=len(hints.get("text") or ""),
        n_revive=len(hint_revive_list(hints)),
        mode=str(hints.get("mode") or ""),
    )
    return record
