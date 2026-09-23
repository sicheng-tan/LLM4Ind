"""LAST ATTEMPT advice: last-round diagnosis → next lemma bias.

Works for every ``--strategy-mode`` (default / naive / v2 / …). Gated only by
``PROMPT_ADVICE`` (and CVC backend). ``advice_from_failed_data`` returns None
when the flag is off.

Not pipeline states (STOP / CHILD-FIRST / CONTINUE). Not solver routing.
``advice: TRIGGER`` is a matchable equational bridge, not SMT ``:pattern``.

PRUNE/BRIDGE compare the last usefulness mix against this node's latest
**goal-only** baseline (A ∪ Lib ⊢ G): first initial prove, harvest-exhausted
A⊢cᵢ copied on skip_initial, or harvest_retry after the library grows.
A previous mix is not the baseline (it already contains candidate lemmas).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, replace
from typing import Any, Dict, List, Optional, Sequence, Tuple

from exp_flags import prompt_advice_enabled
from obligation_tree import compact_formula, last_normal_tree, obligation_tree_enabled
from cvc5_runner import classify_difficulty_term
from solver_relative_metrics import (
    EXPLOSION_LOG_GAIN,
    SKOLEM_PER_CONJ_MAX,
    is_relative_drop,
    is_relative_gain,
    log_gain,
)
from smt_patterns import equality_lhs, has_directed_equality

ADVICE_TRIGGER = "TRIGGER"
ADVICE_LOCALIZE = "LOCALIZE"
ADVICE_PRUNE = "PRUNE"
ADVICE_BRIDGE = "BRIDGE"
ADVICE_GENERALIZE = "GENERALIZE"

CHANNEL_CONJ = "cvc5_inductive"
CHANNEL_INST = "cvc5_simple"
PRUNE_CONSTRAINT = "do not resend the listed kept lemmas unchanged."

_HINT_GENERALIZE = (
    "possible directions: a one-step unfold if IH is enough; a missing "
    "constructor-case lemma; generalize a too-specific failed child; "
    "otherwise generalize variables, weaken a hypothesis, or emit a "
    "shorter local equality. Do not restate the CURRENT goal."
)

_APP = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_+*/<>=!?-]*)")
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_+*/<>=!?-]*")
_RESERVED = frozenset({
    "forall", "exists", "assert", "and", "or", "not", "xor", "ite", "let", "as",
    "true", "false", "distinct", "par", "match", "case", "lambda", "!", "_",
})
_CTOR = frozenset({
    "succ", "pred", "zero", "cons", "nil", "head", "tail", "s", "z",
})


@dataclass(frozen=True)
class PromptAdvice:
    name: str
    because: str
    hint: str
    shape: Optional[str] = None
    reason: str = ""
    constraint: Optional[str] = None


_LOCAL_VS_PARENT_NOTE = (
    "prefer lemmas that help close the open parent; do not resend proved locals."
)


ADVICE_SYSTEM_FOLLOW = (
    "If LAST ATTEMPT lists advice, follow that bias; "
    "GENERALIZE's hint is a set of possible directions, not a closed menu. "
)


def apply_advice_system_instruction(system_prompt: str) -> str:
    """Drop the follow-advice sentence when ``PROMPT_ADVICE`` is off."""
    text = system_prompt or ""
    if prompt_advice_enabled():
        return text
    return text.replace(ADVICE_SYSTEM_FOLLOW, "")


def format_advice_lines(advice: Optional[PromptAdvice]) -> List[str]:
    if advice is None:
        return []
    lines: List[str] = []
    if advice.name:
        lines.extend([
            f"    advice: {advice.name}",
            f"    because: {advice.because}",
            f"    hint: {advice.hint}",
        ])
        if advice.shape:
            lines.append(f"    shape: {advice.shape}")
    if advice.constraint:
        lines.append(f"    constraint: {advice.constraint}")
    return lines


def format_local_vs_parent_lines(
    failed_data: Optional[dict],
    *,
    limit_proved: int = 2,
) -> List[str]:
    """Contrast proved local children with the still-open parent goal.

    Shown under LAST ATTEMPT / INITIAL SOLVE when the obligation tree has proved
    lemma children while the parent goal remains open. Caps proved formulas to
    keep the block short.
    """
    data = failed_data if isinstance(failed_data, dict) else {}
    if not obligation_tree_enabled():
        return []
    tree = last_normal_tree(data.get("obligation"))
    if isinstance(tree, dict) and str(tree.get("status") or "") == "proved":
        return []
    proved = _proved_child_formulas(data)[: max(0, int(limit_proved))]
    if not proved:
        return []
    parent = _open_parent_formula(data)
    lines = ["    already proved (local):"]
    for formula in proved:
        lines.append(f"      {compact_formula(formula)}")
    if parent:
        lines.append(f"    still open (parent): {compact_formula(parent)}")
    else:
        lines.append("    still open (parent): CURRENT goal")
    lines.append(f"    note: {_LOCAL_VS_PARENT_NOTE}")
    return lines


def advice_from_failed_data(
    failed_data: Optional[dict],
    *,
    backend: str = "cvc5",
    has_kept: Optional[bool] = None,
) -> Optional[PromptAdvice]:
    """Pick at most one CVC advice from the last attempt / baseline."""
    data = failed_data if isinstance(failed_data, dict) else {}
    if str(backend or "").lower() != "cvc5":
        return None
    if not prompt_advice_enabled():
        return None
    group = _last_group(data)
    kept = _group_lemmas(group)
    if has_kept is None:
        has_kept = bool(kept)
    hints = _attempt_hints(data, group)
    hd, rare, goals, sources = _hint_terms(hints)
    failed_children = _failed_child_formulas(data)
    proved_children = _proved_child_formulas(data)
    mix_stats = _group_stats(group)
    base_stats = _diag_stats(data.get("baseline_diag"))
    dump_ok = _dumps_complete(data, group)
    attributed = _group_attributed(group)
    goal_b, goal_c, dump_ok = _goal_difficulty_triple(data, group, dump_ok)
    conj_mix, conj_base = _channel_stats(group, data.get("baseline_diag"), CHANNEL_CONJ)
    inst_mix, inst_base = _channel_stats(group, data.get("baseline_diag"), CHANNEL_INST)
    return select_prompt_advice(
        has_kept=bool(has_kept),
        hard_axioms=hd,
        rarely_instantiated=rare,
        goal_fragments=goals,
        source_lemmas=sources,
        failed_children=failed_children,
        proved_children=proved_children,
        baseline_stats=base_stats,
        mix_stats=mix_stats,
        conj_mix_stats=conj_mix,
        conj_base_stats=conj_base,
        inst_mix_stats=inst_mix,
        inst_base_stats=inst_base,
        dump_complete=dump_ok,
        attributed=attributed,
        goal_difficulty_baseline=goal_b,
        goal_difficulty_mix=goal_c,
    )


def select_prompt_advice(
    *,
    has_kept: bool,
    hard_axioms: Sequence[str] = (),
    rarely_instantiated: Sequence[str] = (),
    goal_fragments: Sequence[str] = (),
    source_lemmas: Sequence[str] = (),
    failed_children: Sequence[str] = (),
    proved_children: Sequence[str] = (),
    baseline_stats: Optional[dict] = None,
    mix_stats: Optional[dict] = None,
    dump_complete: bool = False,
    attributed: bool = False,
    goal_difficulty_baseline: Optional[int] = None,
    goal_difficulty_mix: Optional[int] = None,
    conj_mix_stats: Optional[dict] = None,
    conj_base_stats: Optional[dict] = None,
    inst_mix_stats: Optional[dict] = None,
    inst_base_stats: Optional[dict] = None,
) -> Optional[PromptAdvice]:
    """One primary advice; PRUNE is a constraint. Missing dumps are not 0/unused."""
    hd = [x for x in hard_axioms if x]
    rare = [x for x in rarely_instantiated if x]
    goals = [x for x in goal_fragments if x]
    children = [x for x in failed_children if x]
    goal_not_drop = _goal_not_dropped(
        goal_difficulty_baseline, goal_difficulty_mix, dump_complete,
    )
    conj_m = conj_mix_stats if conj_mix_stats is not None else mix_stats
    conj_b = conj_base_stats if conj_base_stats is not None else baseline_stats
    inst_m = inst_mix_stats if inst_mix_stats is not None else mix_stats
    inst_b = inst_base_stats if inst_base_stats is not None else baseline_stats
    volume_up = _volume_explosion(conj_m, conj_b, inst_m, inst_b)
    constraint = None
    if has_kept and volume_up and goal_not_drop and not attributed:
        constraint = PRUNE_CONSTRAINT

    picked: Optional[PromptAdvice] = None
    parents = hd + list(source_lemmas) + goals
    if children and _shares_constructors(parents, children):
        child = compact_formula(children[0])
        proved_locals = [x for x in proved_children if x]
        because = (
            f"failed child {child} shares constructors with the CURRENT "
            "goal or a hotspot axiom."
        )
        hint = _HINT_GENERALIZE
        if proved_locals:
            because += (
                " Some sibling children are already proved locally while the "
                "parent goal is still open."
            )
            hint = (
                f"{_HINT_GENERALIZE} Prefer closing the open parent over "
                "resending already-proved locals."
            )
        picked = PromptAdvice(
            name=ADVICE_GENERALIZE,
            because=because,
            hint=hint,
            reason="ctor_failed_child",
        )
    elif hd and rare:
        focus = rare[0]
        picked = PromptAdvice(
            name=ADVICE_TRIGGER,
            because=(
                f"high-difficulty axiom {compact_formula(focus)} had no matching "
                "formula instantiations (qid-only traces do not count as triggered)."
            ),
            hint=(
                "emit a directed equality whose LHS aligns with a CURRENT-goal "
                "subterm or that recursive/constructor call so E-matching can fire."
            ),
            shape=_trigger_shape(focus, goals),
            reason="rare_inst",
        )
    elif has_kept and dump_complete and goal_not_drop and attributed:
        picked = PromptAdvice(
            name=ADVICE_BRIDGE,
            because=(
                "a named mix candidate was difficulty-attributed but "
                "CURRENT-goal difficulty did not drop."
            ),
            hint=(
                "Connect the CURRENT goal to a relevant part of the previous "
                "candidate or hotspot, possibly through an intermediate "
                "function or invariant. Prefer a small step whose role in the "
                "remaining proof is explicit."
            ),
            reason="named_attributed_no_goal_drop",
        )
    elif _localize_signal(
        conj_b, conj_m, has_kept,
        inst_mix=inst_m, inst_base=inst_b,
    ):
        picked = PromptAdvice(
            name=ADVICE_LOCALIZE,
            because=(
                "conjecture-gen rose while instantiations and skolemization did "
                "not rise in step."
            ),
            hint=(
                "emit a definitional one-step equality; do not strengthen the "
                "whole CURRENT goal."
            ),
            shape=_localize_shape(hd, goals),
            reason="conj_without_inst",
        )
    if picked is not None:
        return replace(picked, constraint=constraint) if constraint else picked
    if constraint:
        return PromptAdvice(
            name="",
            because="",
            hint="",
            reason="prune_constraint",
            constraint=constraint,
        )
    return None


def _last_group(data: dict) -> Any:
    groups = data.get("useless_lemma_groups") or []
    return groups[-1] if groups else None


def _group_lemmas(group: Any) -> List[str]:
    if isinstance(group, list):
        return [str(item) for item in group if item]
    if isinstance(group, dict):
        return [str(item) for item in (group.get("lemmas") or []) if item]
    return []


def _attempt_hints(data: dict, group: Any) -> Sequence[dict]:
    if isinstance(group, dict) and "repair_hints" in group:
        return group.get("repair_hints") or []
    return data.get("repair_hints") or []


def _hint_terms(
    hints: Sequence[dict],
) -> Tuple[List[str], List[str], List[str], List[str]]:
    hd: List[str] = []
    rare: List[str] = []
    goals: List[str] = []
    sources: List[str] = []
    for hint in hints:
        if not isinstance(hint, dict):
            continue
        if str(hint.get("kind") or "") != "high_difficulty_assertions":
            continue
        for item in hint.get("hard_axioms") or []:
            if item and item not in hd:
                hd.append(str(item))
        for item in hint.get("rarely_instantiated") or []:
            if item and item not in rare:
                rare.append(str(item))
        for item in hint.get("goal_fragments") or []:
            if item and item not in goals:
                goals.append(str(item))
        for item in hint.get("source_lemmas") or []:
            if item and item not in sources:
                sources.append(str(item))
    return hd, rare, goals, sources


def _group_stats(group: Any) -> Optional[dict]:
    if isinstance(group, dict) and isinstance(group.get("mix_stats"), dict):
        return dict(group["mix_stats"])
    return None


def _diag_stats(diag: Any) -> Dict[str, int]:
    if not isinstance(diag, dict):
        return {}
    stats = diag.get("stats")
    if not isinstance(stats, dict):
        return {}
    return {str(k): int(v or 0) for k, v in stats.items()}


def _dumps_complete(data: dict, group: Any) -> bool:
    mix_ok = isinstance(group, dict) and bool(group.get("difficulty_dump_complete"))
    base = data.get("baseline_diag")
    base_ok = isinstance(base, dict) and (
        bool(base.get("difficulty")) or bool(base.get("dump_complete"))
    )
    return bool(mix_ok and base_ok)


def _profile_map(obj: Any) -> dict:
    if not isinstance(obj, dict):
        return {}
    if isinstance(obj.get("per_profile"), dict):
        return obj["per_profile"]
    if isinstance(obj.get("portfolio_results"), dict):
        return obj["portfolio_results"]
    return {}


def _profile_stats(blob: Any) -> Optional[dict]:
    if not isinstance(blob, dict):
        return None
    stats = blob.get("stats")
    if not isinstance(stats, dict) or not stats:
        return None
    return {str(k): int(v or 0) for k, v in stats.items()}


def _channel_stats(group: Any, baseline: Any, profile: str) -> Tuple[Optional[dict], Optional[dict]]:
    mix = _profile_stats(_profile_map(group).get(profile))
    base = _profile_stats(_profile_map(baseline).get(profile))
    return mix, base


def _group_attributed(group: Any) -> bool:
    if not isinstance(group, dict):
        return False
    if group.get("attributed_ids"):
        return True
    if group.get("difficulty_attributed"):
        return True
    for blob in _profile_map(group).values():
        if isinstance(blob, dict) and blob.get("attributed_ids"):
            return True
    return False


def _goal_difficulty_triple(
    data: dict, group: Any, dump_ok: bool,
) -> Tuple[Optional[int], Optional[int], bool]:
    mix_map = _profile_map(group)
    base_map = _profile_map(data.get("baseline_diag"))
    simple_m = mix_map.get(CHANNEL_INST)
    simple_b = base_map.get(CHANNEL_INST)
    if isinstance(simple_m, dict) and isinstance(simple_b, dict):
        if simple_m.get("dump_complete") and simple_b.get("dump_complete"):
            gm = simple_m.get("goal_difficulty")
            gb = simple_b.get("goal_difficulty")
            if gm is not None and gb is not None:
                return int(gb), int(gm), True
    gb: Optional[int] = None
    gc: Optional[int] = None
    if isinstance(group, dict):
        if group.get("goal_difficulty_baseline") is not None:
            gb = int(group["goal_difficulty_baseline"])
        if group.get("goal_difficulty_mix") is not None:
            gc = int(group["goal_difficulty_mix"])
    if gb is None:
        gb = _goal_score_from_diag(data.get("baseline_diag"))
    return gb, gc, dump_ok


def _goal_score_from_diag(diag: Any) -> Optional[int]:
    if not isinstance(diag, dict):
        return None
    goal_term = diag.get("goal_term")
    for item in diag.get("difficulty") or []:
        if not isinstance(item, (list, tuple)) or len(item) < 2:
            continue
        term, score = item[0], item[1]
        if int(score or 0) > 0 and classify_difficulty_term(str(term), goal_term) == "goal":
            return int(score)
    return None


def _goal_not_dropped(
    baseline: Optional[int],
    mix: Optional[int],
    dump_complete: bool,
) -> bool:
    """True only when both dumps exist and goal score did not relatively drop."""
    if not dump_complete or baseline is None or mix is None:
        return False
    return not is_relative_drop(baseline, mix)


def _volume_explosion(
    conj_mix: Optional[dict],
    conj_base: Optional[dict],
    inst_mix: Optional[dict] = None,
    inst_base: Optional[dict] = None,
) -> bool:
    """Paired same-profile CONJ/INST explosion. Missing side is not a gain."""
    conj_up = False
    if conj_mix and conj_base:
        conj_up = log_gain(
            int(conj_mix.get("CONJ_TOTAL") or 0),
            int(conj_base.get("CONJ_TOTAL") or 0),
        ) >= EXPLOSION_LOG_GAIN
    inst_up = False
    if inst_mix and inst_base:
        inst_up = log_gain(
            int(inst_mix.get("INST_TOTAL") or 0),
            int(inst_base.get("INST_TOTAL") or 0),
        ) >= EXPLOSION_LOG_GAIN
    return bool(conj_up or inst_up)


def _funs(formula: str) -> set:
    applied = {name for name in _APP.findall(formula or "") if name not in _RESERVED}
    tokens = {name for name in _IDENT.findall(formula or "") if name not in _RESERVED}
    # Nullary constructors (zero, nil) are identifiers, not (zero ...) apps.
    return applied | (tokens & _CTOR)


def _shares_constructors(parents: Sequence[str], children: Sequence[str]) -> bool:
    parent_funs = set()
    child_funs = set()
    for formula in parents:
        parent_funs |= _funs(formula)
    for formula in children:
        child_funs |= _funs(formula)
    return bool((parent_funs & child_funs) & _CTOR)


def _trigger_shape(axiom: str, goals: Sequence[str]) -> str:
    if goals and has_directed_equality(goals[0]):
        lhs = equality_lhs(goals[0])
        if lhs:
            return f"(forall (...) (= {lhs} …))"
    if has_directed_equality(axiom):
        lhs = equality_lhs(axiom)
        if lhs:
            return f"(forall (...) (= {lhs} …))"
    return compact_formula(axiom)


def _localize_shape(axioms: Sequence[str], goals: Sequence[str]) -> Optional[str]:
    for formula in list(axioms) + list(goals):
        if has_directed_equality(formula) and (_funs(formula) & _CTOR):
            lhs = equality_lhs(formula)
            if lhs:
                return f"(forall (...) (= {lhs} …))"
    return None


def _localize_signal(
    baseline_stats: Optional[dict],
    mix_stats: Optional[dict],
    has_kept: bool,
    *,
    inst_mix: Optional[dict] = None,
    inst_base: Optional[dict] = None,
) -> bool:
    """CONJ up vs paired baseline; INST/SKOL not up. Missing INST is not 'no growth'."""
    inst_m = inst_mix if inst_mix is not None else mix_stats
    inst_b = inst_base if inst_base is not None else baseline_stats
    if mix_stats and baseline_stats and inst_m and inst_b:
        conj_c = int(mix_stats.get("CONJ_TOTAL") or 0)
        conj_b = int(baseline_stats.get("CONJ_TOTAL") or 0)
        inst_c = int(inst_m.get("INST_TOTAL") or 0)
        inst_b_n = int(inst_b.get("INST_TOTAL") or 0)
        skol_c = int(mix_stats.get("QUANTIFIERS_SKOLEMIZE") or 0)
        skol_b = int(baseline_stats.get("QUANTIFIERS_SKOLEMIZE") or 0)
        if (
            is_relative_gain(conj_c, conj_b)
            and not is_relative_gain(inst_c, inst_b_n)
            and not is_relative_gain(skol_c, skol_b, rare=True)
        ):
            return True
    if has_kept or mix_stats:
        return False
    stats = baseline_stats or {}
    conj = int(stats.get("CONJ_TOTAL") or 0)
    skol = int(stats.get("QUANTIFIERS_SKOLEMIZE") or 0)
    inst = int(stats.get("INST_TOTAL") or 0)
    if conj <= 0:
        return False
    return (skol / conj) <= SKOLEM_PER_CONJ_MAX and inst <= skol


def _failed_child_formulas(data: dict) -> List[str]:
    return _lemma_child_formulas(data, status="failed")


def _proved_child_formulas(data: dict) -> List[str]:
    return _lemma_child_formulas(data, status="proved")


def _lemma_child_formulas(data: dict, *, status: str) -> List[str]:
    if not obligation_tree_enabled():
        return []
    tree = last_normal_tree(data.get("obligation"))
    out: List[str] = []
    want = str(status or "")

    def walk(node: Any) -> None:
        if not isinstance(node, dict):
            return
        if (
            str(node.get("role") or "") == "lemma"
            and str(node.get("status") or "") == want
        ):
            formula = str(node.get("formula") or "").strip()
            if formula:
                out.append(formula)
        for child in node.get("children") or []:
            walk(child)

    walk(tree)
    return out


def _open_parent_formula(data: dict) -> Optional[str]:
    """Best available formula for the still-open parent / CURRENT goal."""
    tree = last_normal_tree(data.get("obligation"))
    if isinstance(tree, dict):
        if str(tree.get("status") or "") == "proved":
            return None
        formula = str(tree.get("formula") or "").strip()
        if formula:
            return formula
    diag = data.get("baseline_diag")
    if isinstance(diag, dict):
        goal = str(diag.get("goal_term") or "").strip()
        if goal:
            return goal
    return None
