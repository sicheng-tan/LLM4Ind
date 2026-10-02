"""Normalize nullary ADT constructor applications for CVC wellformed checks.

cvc5 ``--parse-only`` rejects ``(nil)`` / ``(Nil)`` / ``(zero)`` for nullary
constructors (``Expecting function-like symbol, found 'nil'``) while accepting
the bare identifier ``nil``. Vampire 4.9 accepts both forms.

Lemma screening (shared by CVC and Vampire Mate) uses cvc5 ``--parse-only``,
so LLM lemmas that wrap nullary constructors in parentheses are false
parse_errors. Rewrite ``(Ctor)`` → ``Ctor`` for constructors declared with
arity 0 in the background SMT.
"""

from __future__ import annotations

import re
from functools import lru_cache
from typing import FrozenSet, Iterable, Set, Tuple


@lru_cache(maxsize=64)
def nullary_constructors_in_smt(smt: str) -> FrozenSet[str]:
    """Nullary ADT constructors declared in *smt* (empty if parse fails)."""
    text = smt or ""
    if "(declare-datatype" not in text and "(declare-datatypes" not in text:
        return frozenset()
    try:
        from problem_profiler.parse_smt import parse_smt_profile

        profile = parse_smt_profile(text)
    except Exception:
        return frozenset()
    arities = dict(profile.signature.get("constructor_arities") or {})
    return frozenset(
        str(name)
        for name, args in arities.items()
        if name and not list(args or [])
    )


def normalize_nullary_ctor_apps(
    formula: str,
    nullaries: Iterable[str],
) -> Tuple[str, int]:
    """Rewrite ``(Ctor)`` → ``Ctor`` for each nullary constructor name.

    Returns ``(rewritten, n_replacements)``. Does not touch ``(as Ctor Sort)``
    or applied constructors such as ``(cons x nil)``.
    """
    names = sorted({str(n) for n in nullaries if n}, key=len, reverse=True)
    if not formula or not names:
        return formula or "", 0
    out = formula
    total = 0
    for name in names:
        pattern = re.compile(rf"\(\s*{re.escape(name)}\s*\)")
        out, n = pattern.subn(name, out)
        total += n
    return out, total


def normalize_lemma_nullary_ctors(lemma: str, smt: str) -> Tuple[str, int]:
    """Normalize nullary ctor apps in *lemma* using constructors from *smt*."""
    return normalize_nullary_ctor_apps(lemma, nullary_constructors_in_smt(smt or ""))
