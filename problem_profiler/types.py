"""Typed records for the deterministic Problem Profiler."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List, Literal, Optional

EvidenceLevel = Literal["explicit", "structural", "heuristic", "unknown"]
FormulaRole = Literal["definition", "axiom", "goal", "candidate", "unknown"]
RecursionKind = Literal[
    "recursive_call",
    "mutual_recursion",
    "constructor_case_split",
    "structural_recursion",
    "other_decreasing_recursion",
    "unknown_recursion",
]


@dataclass
class FormulaRecord:
    formula_id: str
    raw: str
    role: FormulaRole = "unknown"
    role_source: str = "unknown"
    symbols: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class RecursionFact:
    function: str
    kind: RecursionKind
    source_formula_ids: List[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "structural"
    detail: str = ""
    # Goal-relative association (filled in refresh_goal_dependent_facts).
    link: str = ""  # theorem-related | def-only | ""
    link_peers: List[str] = field(default_factory=list)
    # Non-structural self-call bridges (filter/bubble); not overwritten by links.
    bridge_peers: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class ObserverCandidate:
    function: str
    input_sorts: List[str] = field(default_factory=list)
    return_sort: str = ""
    source_formula_ids: List[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "heuristic"
    detail: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class GoalRelation:
    kind: str
    symbols: List[str] = field(default_factory=list)
    formula_ids: List[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "structural"
    detail: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class InductionAttempt:
    """Known / candidate induction layer vs the current goal (heuristic).

    When the goal has multiple ADT binders, attempts are ordered outer→inner
    with increasing ``nest_level`` for progressive (nested) display.
    """

    induct_var: str
    induct_sort: str = ""
    base_ctors: List[str] = field(default_factory=list)
    step_ctors: List[str] = field(default_factory=list)
    case_split: bool = False
    source_formula_ids: List[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "structural"
    detail: str = ""
    nest_level: int = 0
    status: str = "known"  # known | candidate

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class FunctionLinkFact:
    """Conservative function association vs CURRENT goal (co-occurrence heuristic)."""

    kind: str  # theorem_related | missing_bridge
    symbols: List[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "structural"
    detail: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class ProblemProfile:
    problem_id: str = ""
    goal_formula_id: Optional[str] = None
    signature: Dict[str, Any] = field(default_factory=dict)
    formulas: List[FormulaRecord] = field(default_factory=list)
    recursion_structure: List[RecursionFact] = field(default_factory=list)
    observer_candidates: List[ObserverCandidate] = field(default_factory=list)
    goal_relations: List[GoalRelation] = field(default_factory=list)
    induction_attempts: List[InductionAttempt] = field(default_factory=list)
    function_links: List[FunctionLinkFact] = field(default_factory=list)
    evidence_notes: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "problem_id": self.problem_id,
            "goal_formula_id": self.goal_formula_id,
            "signature": dict(self.signature),
            "formulas": [f.to_dict() for f in self.formulas],
            "recursion_structure": [r.to_dict() for r in self.recursion_structure],
            "observer_candidates": [o.to_dict() for o in self.observer_candidates],
            "goal_relations": [g.to_dict() for g in self.goal_relations],
            "induction_attempts": [a.to_dict() for a in self.induction_attempts],
            "function_links": [f.to_dict() for f in self.function_links],
            "evidence_notes": list(self.evidence_notes),
        }


@dataclass
class GatedProfileFacts:
    """Subset of a profile selected for prompt injection."""

    recursion: List[RecursionFact] = field(default_factory=list)
    observers: List[ObserverCandidate] = field(default_factory=list)
    relations: List[GoalRelation] = field(default_factory=list)
    induction_attempts: List[InductionAttempt] = field(default_factory=list)
    function_links: List[FunctionLinkFact] = field(default_factory=list)
    related_formula_ids: List[str] = field(default_factory=list)
    formula_snippets: List[str] = field(default_factory=list)

    def is_empty(self) -> bool:
        return not (self.recursion or self.observers)
