"""CVC5 ``:pattern`` helpers for axiom injection.

Patterns are an *injection* option (``CVC_PATTERNS`` / ``--cvc-patterns``),
independent of ``--strategy-mode``. Used when lemmas are axioms in
``A ∪ Lib ∪ C ⊢ G``. Subgoal / validation SMT files stay bare.
"""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional, Sequence, Tuple

from exp_flags import resolve_cvc_patterns_enabled
from solver_relative_metrics import (
    EMATCHING_PER_CONJ_MAX,
    EMATCHING_PER_CONJ_SOFT,
    INST_OF_MATCHING_MAX,
)


_TIMEOUT_STATUSES = frozenset({"timeout", "unknown"})
_BANG_ATTR = re.compile(r"\(\s*!\s+")


def normalize_lemma_formula(formula: str) -> str:
    return re.sub(r"\s+", " ", (formula or "").strip())


def _skip_ws(text: str, i: int) -> int:
    n = len(text)
    while i < n and text[i].isspace():
        i += 1
    return i


def read_sexpr(text: str, i: int = 0) -> Tuple[Optional[str], int]:
    """Read one SMT-LIB s-expression starting at ``i``; return (expr, next_i)."""
    i = _skip_ws(text, i)
    n = len(text)
    if i >= n:
        return None, i
    if text[i] != "(":
        j = i
        while j < n and not text[j].isspace() and text[j] not in "()":
            j += 1
        return text[i:j], j
    depth = 0
    j = i
    while j < n:
        ch = text[j]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[i : j + 1], j + 1
        j += 1
    return None, i


def sexpr_head_args(expr: str) -> Tuple[Optional[str], List[str]]:
    """Split ``(head arg...)`` into head token and argument s-exprs."""
    text = (expr or "").strip()
    if not text.startswith("("):
        return None, []
    inner = text[1:-1].strip() if text.endswith(")") else text[1:].strip()
    head, i = read_sexpr(inner, 0)
    if head is None:
        return None, []
    args: List[str] = []
    n = len(inner)
    while True:
        i = _skip_ws(inner, i)
        if i >= n:
            break
        arg, i = read_sexpr(inner, i)
        if arg is None:
            break
        args.append(arg)
    return head, args


def strip_bang_attrs(formula: str) -> str:
    """Unwrap ``(! φ :attr ...)`` layers, keeping φ."""
    text = normalize_lemma_formula(formula)
    while True:
        m = _BANG_ATTR.match(text)
        if not m:
            return text
        body, i = read_sexpr(text, m.end())
        if body is None:
            return text
        # Skip trailing attributes until the closing ')' of the bang form.
        # text is "(! BODY :attr ...)" — BODY already consumed; drop rest.
        text = normalize_lemma_formula(body)


def forall_matrix(formula: str) -> str:
    """Return the body of the outermost ``forall``, else the formula itself."""
    text = strip_bang_attrs(formula)
    head, args = sexpr_head_args(text)
    if head != "forall" or len(args) < 2:
        return text
    return strip_bang_attrs(args[-1])


def peel_implication(body: str) -> str:
    """Follow ``=>`` / ``implies`` to the conclusion."""
    text = strip_bang_attrs(body)
    while True:
        head, args = sexpr_head_args(text)
        if head in ("=>", "implies") and len(args) >= 2:
            text = strip_bang_attrs(args[-1])
            continue
        return text


def equality_lhs(formula: str) -> Optional[str]:
    """LHS of a top-level / conclusion ``(= L R)``, or None."""
    body = peel_implication(forall_matrix(formula))
    head, args = sexpr_head_args(body)
    if head != "=" or len(args) < 2:
        return None
    return args[0].strip() or None


def is_app_term(term: str) -> bool:
    """True for compound applications ``(f ...)`` (good E-matching triggers)."""
    text = (term or "").strip()
    if not text.startswith("("):
        return False
    head, _args = sexpr_head_args(text)
    if head is None:
        return False
    # Indexed identifiers like (_ BitVec 8) are not useful triggers alone.
    if head == "_":
        return False
    return True


def has_directed_equality(formula: str) -> bool:
    lhs = equality_lhs(formula)
    return bool(lhs and is_app_term(lhs))


def formulas_have_directed_equality(formulas: Sequence[str]) -> bool:
    return any(has_directed_equality(f) for f in formulas if f)


def infer_trigger_pattern(formula: str) -> Optional[str]:
    """Return a ``:pattern`` value like ``((plus (s x) y))``, or None."""
    lhs = equality_lhs(formula)
    if not lhs or not is_app_term(lhs):
        return None
    return f"({lhs})"


def format_assert_line(formula: str, *, add_pattern: bool = False) -> str:
    """``(assert φ)`` or ``(assert (! φ :pattern ((f …))))`` for directed eqs."""
    text = normalize_lemma_formula(formula)
    if text.startswith("(assert"):
        inner, _ = read_sexpr(text, 0)
        if inner and inner.startswith("(assert"):
            head, args = sexpr_head_args(inner)
            if head == "assert" and args:
                text = normalize_lemma_formula(args[0])
    text = strip_bang_attrs(text)
    if add_pattern:
        pat = infer_trigger_pattern(text)
        if pat:
            return f"(assert (! {text} :pattern {pat}))"
    return f"(assert {text})"


def _diag_stats(failed_data: Optional[dict]) -> Dict[str, int]:
    """Best available cached CVC stats (baseline 60s, else short diagnostic)."""
    data = failed_data if isinstance(failed_data, dict) else {}
    for key in ("baseline_diag", "baseline_diag_short"):
        diag = data.get(key)
        if not isinstance(diag, dict):
            continue
        stats = diag.get("stats")
        if isinstance(stats, dict) and stats:
            return {str(k): int(v or 0) for k, v in stats.items()}
    return {}


def ematching_total(stats: Optional[dict]) -> int:
    """Pure E-matching volume (excludes CBQI)."""
    st = stats or {}
    return int(st.get("QUANTIFIERS_INST_E_MATCHING") or 0) + int(
        st.get("QUANTIFIERS_INST_E_MATCHING_SIMPLE") or 0
    )


def v2_pattern_features(failed_data: Optional[dict]) -> Dict[str, Any]:
    """Booleans for the CVC ``:pattern`` gate (independent of prompt mode).

    ``trigger`` is ``rare_inst`` only: a high-difficulty axiom had no
    formula-shaped instantiations. That is the case where E-matching triggers
    are actually missing.

    ``useful_timeout`` and ``rewrite_scarce`` are still computed for logs, but
    they do not open the gate. Timeout is common and would spend a 6-way
    ±pattern contrast (4 CVC profiles + simple/inductive with ``:pattern``)
    on coverage rather than the scarce QI-rare cases. Low ``E_MATCHING/CONJ``
    prefers successes on full706, so it is not a trigger either.
    ``search_explosion`` is not consulted.
    """
    data = failed_data if isinstance(failed_data, dict) else {}
    hints = data.get("repair_hints") or []
    kinds = {
        str(h.get("kind") or "")
        for h in hints
        if isinstance(h, dict)
    }
    rare_inst = False
    for hint in hints:
        if not isinstance(hint, dict):
            continue
        if hint.get("kind") != "high_difficulty_assertions":
            continue
        rare = hint.get("rarely_instantiated") or []
        if isinstance(rare, list) and rare:
            rare_inst = True
            break

    stats = _diag_stats(data)
    skol = int(stats.get("QUANTIFIERS_SKOLEMIZE") or 0)
    inst = int(stats.get("INST_TOTAL") or 0)
    conj = int(stats.get("CONJ_TOTAL") or 0)
    em = ematching_total(stats)
    matching = skol + inst
    iom = (inst / matching) if matching > 0 else 1.0
    rewrite_scarce_stats = skol > 0 and matching > 0 and iom < INST_OF_MATCHING_MAX
    rewrite_scarce = rewrite_scarce_stats or ("need_rewrite" in kinds)
    em_per_conj = (em / conj) if conj > 0 else None
    # Diagnostic only — not part of trigger (hits successes more than failures).
    em_vs_conj_poor = em_per_conj is not None and em_per_conj < EMATCHING_PER_CONJ_MAX
    soft_em_vs_conj = em_per_conj is not None and em_per_conj < EMATCHING_PER_CONJ_SOFT
    quant_activity = skol + conj + inst + em
    em_zero = quant_activity > 0 and em == 0

    useful_timeout = False
    for group in data.get("useless_lemma_groups") or []:
        if isinstance(group, dict):
            status = str(group.get("status") or "").strip().lower()
        else:
            status = ""
        if status in _TIMEOUT_STATUSES:
            useful_timeout = True
            break

    # Instantiation-rare only. Timeout / rewrite-scarce mix are logged but not
    # used as open triggers (6-way ±pattern contrast is reserved for QI-rare).
    trigger = bool(rare_inst)
    inst_poor = bool(rare_inst or rewrite_scarce or em_zero)
    return {
        "rare_inst": rare_inst,
        "useful_timeout": useful_timeout,
        "rewrite_scarce": rewrite_scarce,
        "rewrite_scarce_stats": rewrite_scarce_stats,
        "em_vs_conj_poor": em_vs_conj_poor,
        "soft_em_vs_conj": soft_em_vs_conj,
        "em_zero": em_zero,
        "inst_poor": inst_poor,
        "ematching": em,
        "em_per_conj": em_per_conj,
        "iom": iom if matching > 0 else None,
        "search_explosion": False,
        "trigger": trigger,
    }


def should_add_cvc_patterns(
    *,
    failed_data: Optional[dict] = None,
    formulas: Sequence[str] = (),
    enabled: Optional[bool] = None,
) -> bool:
    """Whether to wrap directed equalities with ``:pattern`` on CVC axiom inject.

    Gated by ``CVC_PATTERNS`` / ``enabled`` (any strategy mode). Decision:

    ``pattern_on`` =
      patterns_enabled
      ∧ rare_inst
      ∧ has_directed_eq

    Opens only when a high-difficulty axiom had no formula-shaped instantiations.
    ``useful_timeout`` / ``rewrite_scarce`` are not triggers.
    """
    data = failed_data if isinstance(failed_data, dict) else {}
    if enabled is None and "cvc_patterns" in data:
        enabled = bool(data.get("cvc_patterns"))
    if not resolve_cvc_patterns_enabled(enabled):
        return False
    feats = v2_pattern_features(data)
    if not feats["trigger"]:
        return False
    return formulas_have_directed_equality(formulas)


def v2_should_add_cvc_patterns(
    *,
    strategy_mode: str = "",
    failed_data: Optional[dict] = None,
    formulas: Sequence[str] = (),
    enabled: Optional[bool] = None,
) -> bool:
    """Backward-compatible alias; ``strategy_mode`` no longer gates patterns."""
    del strategy_mode
    return should_add_cvc_patterns(
        failed_data=failed_data, formulas=formulas, enabled=enabled
    )


def pattern_trigger_reasons(failed_data: Optional[dict]) -> List[str]:
    feats = v2_pattern_features(failed_data)
    reasons: List[str] = []
    if feats["rare_inst"]:
        reasons.append("rare_inst")
    return reasons
