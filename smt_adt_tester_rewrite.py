"""Rewrite SMT-LIB2 shorthand ADT testers for Vampire.

Vampire 4.9 does not parse `(is-Cons x)` / `(is-S x)` and reports
`Unrecognized term identifier 'is-...'`. SMT-LIB2 defines the same
testers as indexed identifiers: `((_ is Cons) x)`.

This module rewrites the shorthand form to the indexed form. The two
are definitionally equivalent in SMT-LIB2 (cvc5 treats the shorthand as
sugar for the indexed tester).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Tuple

# `(is-Ctor` where Ctor is an SMT identifier. Do not match `((_ is Ctor)`.
_TESTER_HEAD = re.compile(r"\(is-([A-Za-z][A-Za-z0-9_]*)\b")
_INDEXED_TESTER = re.compile(r"\(\(_\s+is\s+[A-Za-z][A-Za-z0-9_]*\)")
_SHORTHAND_LEFT = re.compile(r"\(is-[A-Za-z][A-Za-z0-9_]*\b")


def needs_tester_rewrite(text: str) -> bool:
    """True if the SMT text still contains shorthand `(is-Ctor ...)` testers."""
    return count_shorthand_testers(text) > 0


def count_shorthand_testers(text: str) -> int:
    """Count shorthand testers, ignoring comments and indexed `((_ is C)` forms."""
    n = 0
    i = 0
    while i < len(text):
        if text[i] == ";":
            i = _skip_comment(text, i)
            continue
        if text[i] == "(" and text.startswith("(_", i):
            # skip indexed tester / other indexed ids as a unit when possible
            m = _INDEXED_TESTER.match(text, i)
            if m:
                i = m.end()
                continue
        m = _TESTER_HEAD.match(text, i)
        if m:
            n += 1
            i = m.end()
            continue
        i += 1
    return n


def rewrite_smtlib_testers(text: str) -> Tuple[str, int]:
    """Rewrite `(is-Ctor t)` into `((_ is Ctor) t)`.

    Returns (rewritten_text, number_of_rewrites).
    """
    out = []
    i = 0
    n = 0
    while i < len(text):
        if text[i] == ";":
            j = _skip_comment(text, i)
            out.append(text[i:j])
            i = j
            continue
        # Already-indexed tester: copy the head and continue.
        m_idx = _INDEXED_TESTER.match(text, i)
        if m_idx:
            out.append(m_idx.group(0))
            i = m_idx.end()
            continue
        m = _TESTER_HEAD.match(text, i)
        if m:
            ctor = m.group(1)
            j = m.end()
            j = _skip_ws(text, j)
            arg, k = _parse_one_term(text, j)
            k = _skip_ws(text, k)
            if k >= len(text) or text[k] != ")":
                # Not a well-formed tester application; copy the head char and continue.
                out.append(text[i])
                i += 1
                continue
            k += 1
            out.append(f"((_ is {ctor}) {arg})")
            n += 1
            i = k
            continue
        out.append(text[i])
        i += 1
    return "".join(out), n


def rewrite_smt_file(path: Path) -> Tuple[str, int]:
    return rewrite_smtlib_testers(Path(path).read_text(encoding="utf-8"))


def remaining_shorthand_testers(text: str) -> list:
    """Return leftover shorthand tester snippets (should be empty after rewrite)."""
    leftover = []
    i = 0
    while i < len(text):
        if text[i] == ";":
            i = _skip_comment(text, i)
            continue
        if _INDEXED_TESTER.match(text, i):
            i += 1
            continue
        m = _SHORTHAND_LEFT.match(text, i)
        if m:
            leftover.append(m.group(0))
            i = m.end()
            continue
        i += 1
    return leftover


def _skip_comment(text: str, i: int) -> int:
    while i < len(text) and text[i] != "\n":
        i += 1
    return i


def _skip_ws(text: str, i: int) -> int:
    while i < len(text) and text[i].isspace():
        i += 1
    return i


def _parse_one_term(text: str, i: int) -> Tuple[str, int]:
    """Parse one SMT term starting at i. Returns (term_text, index_after)."""
    i = _skip_ws(text, i)
    if i >= len(text):
        return "", i
    if text[i] == ";":
        i = _skip_ws(text, _skip_comment(text, i))
        if i >= len(text):
            return "", i
    if text[i] != "(":
        j = i
        while j < len(text) and not text[j].isspace() and text[j] not in "();":
            j += 1
        return text[i:j], j
    depth = 0
    j = i
    while j < len(text):
        ch = text[j]
        if ch == ";":
            j = _skip_comment(text, j)
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            j += 1
            if depth == 0:
                return text[i:j], j
            continue
        j += 1
    return text[i:], len(text)
