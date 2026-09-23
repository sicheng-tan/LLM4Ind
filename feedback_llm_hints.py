"""Optional LLM hints from solver feedback (FEEDBACK_LLM_HINTS).

Default **off**. When on, and the latest attempt already has difficulty /
``high_difficulty_assertions`` observations, run one LLM call that writes a
short self-contained analysis+suggestion for the next lemma-generation prompt.
No separate SMT parse: axioms and goal come from those hints /
``baseline_diag`` only. Skip entirely when difficulty is missing.
"""

from __future__ import annotations

import json
import logging
import re
import time
from typing import Any, Dict, List, Optional, Sequence

from exp_flags import feedback_llm_hints_enabled, repair_hints_enabled
from exp_stats import add_llm_time, log_exp, record_llm_generation
from llm_time_budget import invoke_configured_chat
from obligation_tree import compact_formula

HINTS_KIND = "llm_feedback_hints"
MAX_AXIOMS = 4
MAX_EVIDENCE = 8
MAX_CANDIDATES = 3
MAX_FORMULA_CHARS = 280
MAX_HINT_CHARS = 900
MIN_HINT_CHARS = 24

_JSON_FENCE = re.compile(r"```(?:json)?\s*(\{.*?\})\s*```", re.DOTALL | re.IGNORECASE)
_ANY_FENCE = re.compile(r"```(?:\w+)?\s*(.*?)\s*```", re.DOTALL)
_JSON_OBJECT = re.compile(r"\{.*\}", re.DOTALL)
_ID_TOKEN = re.compile(r"\b([EAGC]\d+)\b")

HINTS_SYSTEM = """You help repair a failed SMT inductive attempt.
You receive blocked solver observations for your reading only.
Rules:
- difficulty ranks runtime hotspots; not proof necessity.
- search-change stats are weak signals; for reference only.
- Write a short analysis note as a hint for another LLM that will propose lemmas.
- When you mention a formula, quote it in full."""

HINTS_USER_TEMPLATE = """From the observations below, write one short note:
what looks stuck, and what lemma direction to try next.
Plain text only. When mentioning a formula, quote it in full.

{body}
"""


def _hd_hints(hints: Sequence[dict]) -> List[dict]:
    out: List[dict] = []
    for hint in hints or []:
        if not isinstance(hint, dict):
            continue
        if str(hint.get("kind") or "") == "high_difficulty_assertions":
            out.append(hint)
    return out


def _latest_hd_hint(failed_data: dict) -> Optional[dict]:
    group = None
    groups = failed_data.get("useless_lemma_groups") or []
    if groups and isinstance(groups[-1], dict) and "repair_hints" in groups[-1]:
        group = groups[-1]
    hints: Sequence[dict]
    if isinstance(group, dict):
        hints = group.get("repair_hints") or []
    else:
        hints = failed_data.get("repair_hints") or []
    hds = _hd_hints(hints)
    if hds:
        return hds[-1]
    # Fall back to node-level repair_hints (initial solve before any group).
    hds = _hd_hints(failed_data.get("repair_hints") or [])
    return hds[-1] if hds else None


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


def _source_attempt_id(failed_data: dict) -> str:
    hd = _latest_hd_hint(failed_data)
    if hd and hd.get("attempt_id"):
        return str(hd["attempt_id"])
    groups = failed_data.get("useless_lemma_groups") or []
    if groups and isinstance(groups[-1], dict):
        g = groups[-1]
        return (
            f"group:{g.get('status')}:{len(g.get('lemmas') or [])}:"
            f"{g.get('difficulty_dump_complete')}"
        )
    return "baseline"


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


def build_observation_pack(failed_data):
    """Pack goal / hard axioms / last candidates / light stats. None if no difficulty."""
    if not has_difficulty_observations(failed_data):
        return None
    hd = _latest_hd_hint(failed_data) or {}
    base = failed_data.get("baseline_diag") if isinstance(failed_data.get("baseline_diag"), dict) else {}
    goal = ""
    if hd.get("goal_fragments"):
        goal = str((hd.get("goal_fragments") or [""])[0] or "")
    if not goal:
        goal = str(base.get("goal_term") or "")
    axioms = [str(a) for a in (hd.get("hard_axioms") or []) if a][:MAX_AXIOMS]
    if not axioms and base.get("difficulty"):
        for item in base.get("difficulty") or []:
            if not isinstance(item, (list, tuple)) or len(item) < 2:
                continue
            term, score = item[0], item[1]
            if int(score or 0) <= 0:
                continue
            axioms.append(str(term))
            if len(axioms) >= MAX_AXIOMS:
                break
    if not axioms and not goal:
        return None

    scores = hd.get("hard_axiom_scores") if isinstance(hd.get("hard_axiom_scores"), dict) else {}
    rarely = {str(a) for a in (hd.get("rarely_instantiated") or []) if a}
    ranked = sorted(
        ((str(ax), int(scores.get(str(ax)) or 0)) for ax in axioms),
        key=lambda pair: -pair[1],
    )
    hard_axioms = []
    for i, (ax, score) in enumerate(ranked, 1):
        hard_axioms.append({
            "formula": compact_formula(ax, MAX_FORMULA_CHARS),
            "rank": i,
            "score": score,
            "rarely_instantiated": ax in rarely or compact_formula(ax, MAX_FORMULA_CHARS) in {
                compact_formula(r, MAX_FORMULA_CHARS) for r in rarely
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
                "formula": compact_formula(lemma, MAX_FORMULA_CHARS),
                "group_failed": True,
                "attributed": cid in attributed,
            }
            prove = prove_lookup.get(lemma)
            if not prove:
                target = entry["formula"]
                for form, st in prove_lookup.items():
                    if compact_formula(form, MAX_FORMULA_CHARS) == target:
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
        "attempt_id": _source_attempt_id(failed_data),
        "dump_complete": dump_complete,
        "goal": {
            "id": "G1",
            "formula": compact_formula(goal, MAX_FORMULA_CHARS) if goal else "",
        },
        "axioms": [
            {"id": f"A{i}", "formula": ax["formula"]}
            for i, ax in enumerate(hard_axioms, 1)
        ],
        "hard_axioms": hard_axioms,
        "evidence": evidence,
        "previous_candidates": candidates,
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
    lines.append("")
    lines.append("=== HARD AXIOMS (difficulty hotspots; not proof dependencies) ===")
    hard = pack.get("hard_axioms") or []
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
        for ax in pack.get("axioms") or []:
            lines.append(f"  - {ax.get('formula')}")
        if not pack.get("axioms"):
            lines.append("  (none)")

    prev = pack.get("previous_candidates") or []
    if prev:
        lines.append("")
        lines.append("=== LAST CANDIDATE LEMMAS (usefulness: A ∧ candidates → goal) ===")
        group_status = pack.get("group_status") or pack.get("status") or "?"
        lines.append(f"  Group result: {group_status} (goal not proved with this set)")
        for item in prev:
            lines.append(f"  - {item.get('formula')}")
            outcome_bits = ["in failed group"]
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

    return "\n".join(lines)


def _strip_orphan_ids(text: str) -> str:
    """Drop bare E/A/G/C tokens so generation prompts stay self-contained."""
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
                f"{chunk} Suggested shape: {compact_formula(cand, MAX_FORMULA_CHARS)}"
                if chunk
                else f"Suggested shape: {compact_formula(cand, MAX_FORMULA_CHARS)}"
            )
        if chunk:
            parts.append(chunk)
    return " ".join(parts).strip()


def parse_llm_feedback_hints(raw: Optional[str]) -> Optional[Dict[str, Any]]:
    """Parse model output into ``{\"text\": ...}``. Accepts plain prose or legacy JSON."""
    text = (raw or "").strip()
    if not text:
        return None

    # Prefer plain prose; only peel fences / JSON when the whole reply is wrapped.
    fenced = _ANY_FENCE.search(text)
    if fenced and text.strip().startswith("```"):
        text = fenced.group(1).strip()

    if text.startswith("{") or _JSON_FENCE.search(raw or ""):
        blob = None
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
                text = _text_from_legacy_json(data)

    cleaned = _normalize_hint_text(text)
    if len(cleaned) < MIN_HINT_CHARS:
        return None
    return {"text": cleaned}


def hint_text(hints: Any) -> str:
    """Extract display text from stored hints (new or legacy)."""
    if isinstance(hints, str):
        return _normalize_hint_text(hints)
    if not isinstance(hints, dict):
        return ""
    if hints.get("text"):
        return _normalize_hint_text(str(hints.get("text") or ""))
    return _normalize_hint_text(_text_from_legacy_json(hints))


def format_llm_hints_lines(
    record: Optional[dict],
    *,
    indent: str = "    ",
) -> List[str]:
    """Lines for SOLVER HINTS nested under LAST ATTEMPT / INITIAL SOLVE."""
    if not isinstance(record, dict):
        return []
    text = hint_text(record.get("hints"))
    if not text:
        return []
    ind = indent
    sub = indent + "  "
    return [
        f"{ind}SOLVER HINTS (rejectable; not an order):",
        f"{sub}Check against the goal and axioms; revise or ignore if wrong.",
        f"{sub}{text}",
    ]


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
) -> Optional[dict]:
    """Run LLM-hints when flag is on and difficulty observations exist.

    Skips Vampire, missing difficulty, and when the stored hints already
    matches the current attempt_id.
    """
    if not feedback_llm_hints_enabled():
        return None
    if not repair_hints_enabled():
        return None
    if str(backend or "").lower() != "cvc5":
        return None
    failed_data = load_failed_lemmas(base_path, goal_name)
    if not has_difficulty_observations(failed_data):
        log_exp(
            "llm_feedback_hints_skip",
            goal=goal_name,
            reason="no_difficulty",
        )
        return None
    pack = build_observation_pack(failed_data)
    if pack is None:
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
        and hint_text(existing.get("hints"))
    ):
        return existing

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
        hints = parse_llm_feedback_hints(raw)
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
        lemmas=[],
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
    )
    return record
