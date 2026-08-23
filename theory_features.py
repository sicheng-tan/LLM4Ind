"""Static theory-feature analysis for SMT-LIB2 inductive problems.

Used by Feedback-Guided solver routing to pick Vampire / CVC5 profiles
before any LLM query, and to explain routing decisions in prompts.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import List, Union


@dataclass
class TheoryFeatures:
    logic: str = ""
    has_adt: bool = False
    has_int: bool = False
    has_real: bool = False
    has_bitvec: bool = False
    has_quantifiers: bool = False
    has_linear_arithmetic: bool = False
    datatype_names: List[str] = field(default_factory=list)
    function_names: List[str] = field(default_factory=list)

    @property
    def mixed_adt_lia(self) -> bool:
        return self.has_adt and (self.has_int or self.has_linear_arithmetic)

    def to_dict(self) -> dict:
        d = asdict(self)
        d["mixed_adt_lia"] = self.mixed_adt_lia
        return d

    def summary(self) -> str:
        bits = []
        if self.logic:
            bits.append(f"logic={self.logic}")
        bits.append("ADT" if self.has_adt else "no-ADT")
        bits.append("Int" if self.has_int else "no-Int")
        if self.mixed_adt_lia:
            bits.append("mixed-ADT-LIA")
        if self.has_quantifiers:
            bits.append("quantified")
        return ", ".join(bits)


_LOGIC_RE = re.compile(r"\(set-logic\s+([A-Za-z0-9_]+)\)")
_DT_BLOCK_RE = re.compile(
    r"\(declare-datatype[s]?\s*\(?\s*\(?\s*([A-Za-z_][A-Za-z0-9_-]*)",
)
_FUN_RE = re.compile(r"\(declare-fun\s+([A-Za-z_][A-Za-z0-9_+*/<>=!?-]*)")
_FORALL_RE = re.compile(r"\(\s*forall\b")


def analyze_smt(source: Union[str, Path]) -> TheoryFeatures:
    """Parse coarse theory features from an SMT-LIB2 string or file."""
    if isinstance(source, Path):
        text = source.read_text(encoding="utf-8")
    else:
        path = Path(source)
        if "\n" not in source and path.suffix == ".smt2" and path.exists():
            text = path.read_text(encoding="utf-8")
        else:
            text = source

    features = TheoryFeatures()
    m = _LOGIC_RE.search(text)
    if m:
        features.logic = m.group(1)
        logic = features.logic.upper()
        features.has_int = features.has_int or ("LIA" in logic or logic.endswith("IA") or "IDL" in logic)
        features.has_real = features.has_real or ("LRA" in logic or "NRA" in logic or "RIA" in logic)
        features.has_bitvec = features.has_bitvec or ("BV" in logic)
        features.has_adt = features.has_adt or ("DT" in logic)

    features.datatype_names = _dedup(_DT_BLOCK_RE.findall(text))
    if features.datatype_names or "(declare-datatypes" in text or "(declare-datatype" in text:
        features.has_adt = True

    if re.search(r"\bInt\b", text):
        features.has_int = True
    if re.search(r"\bReal\b", text):
        features.has_real = True
    if "BitVec" in text or "(_ BitVec" in text:
        features.has_bitvec = True

    features.has_quantifiers = bool(_FORALL_RE.search(text))
    features.has_linear_arithmetic = features.has_int or features.has_real
    if re.search(r"\([+\-*/]|div|mod|<=|<|>=|>\b", text) and features.has_int:
        features.has_linear_arithmetic = True

    features.function_names = _dedup(_FUN_RE.findall(text))[:24]
    return features


def _dedup(items: List[str]) -> List[str]:
    seen = set()
    out: List[str] = []
    for x in items:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out
