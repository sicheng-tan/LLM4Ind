"""Dataclasses for InductionScheme obligations and attempt ledgers."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List, Optional


@dataclass
class SchemeObligation:
    """One base@C or step@C (or later measure) obligation."""

    obl_id: str
    kind: str  # "base" | "step" | "measure"
    ctor: str
    formula: str
    induct_var: str
    induct_sort: str
    # Concrete term substituted for ``induct_var`` (e.g. ``nil``, ``(P _b0)``).
    inst_term: str = ""
    validated: bool = False
    validate_errors: List[str] = field(default_factory=list)
    status: str = "open"  # open | proved | failed | frontier | invalid
    prove_status: str = ""
    prove_elapsed: float = 0.0
    node_id: Optional[str] = None
    skip_initial: bool = False
    no_nest: bool = False
    parent_obl_id: Optional[str] = None

    def summary(self) -> str:
        tag = f"{self.kind}@{self.ctor}" if self.ctor else self.kind
        st = self.status
        if self.prove_status and self.status not in ("proved", "invalid"):
            st = f"{self.status}/{self.prove_status}"
        return f"{tag}:{st}"

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "SchemeObligation":
        known = {f.name for f in cls.__dataclass_fields__.values()}  # type: ignore[attr-defined]
        return cls(**{k: v for k, v in (data or {}).items() if k in known})


@dataclass
class SchemeAttempt:
    """One generate+prove round for a goal node."""

    goal_name: str
    induct_var: str = ""
    induct_sort: str = ""
    mode: str = "structural"
    # When mode involves measure: observer/fun used as μ : sort → Int/Nat.
    measure_fun: str = ""
    measure_ret_sort: str = ""
    # Optional SMT prelude (e.g. Nat→Int) injected before prove/gate.
    measure_prelude: str = ""
    # True when obligations are concrete descent/semantic bridges (not bare WF).
    bridge_primary: bool = False
    depth: int = 0
    nest_budget: int = 1
    validated: bool = False
    validate_errors: List[str] = field(default_factory=list)
    obligations: List[SchemeObligation] = field(default_factory=list)
    closed: bool = False
    close_reason: str = ""  # short_prove | nest | frontier | ""
    frontier_ids: List[str] = field(default_factory=list)
    had_success_child: bool = False
    skipped: bool = False
    skip_reason: str = ""
    backup_ran: bool = False
    # axioms ∧ library ∧ base ∧ step ⊢ G gate (optional soundness check).
    goal_gate_status: str = "off"  # off | skipped | proved | failed | timeout | error
    goal_gate_elapsed: float = 0.0

    def all_proved(self) -> bool:
        if not self.obligations or not self.validated:
            return False
        if any(o.validate_errors for o in self.obligations):
            return False
        return all(o.status == "proved" for o in self.obligations)

    def goal_gate_ok(self) -> bool:
        """Whether the optional G-gate allows closing (off/skipped count as ok)."""
        if self.goal_gate_status in ("off", "skipped", "proved"):
            return True
        return False

    def gate_blocks_scheme(self) -> bool:
        """Hard reject only: gate returned sat/error.

        ``timeout`` is incomplete, not a soundness reject — still allow
        obligation short-prove / NEST / prompt; only ``kind=scheme`` close
        stays blocked via ``goal_gate_ok``.
        """
        return self.goal_gate_status in ("failed", "error")

    def prompt_eligible(self) -> bool:
        """Whether the scheme ledger may appear in the next LLM prompt."""
        if self.gate_blocks_scheme():
            return False
        return True

    def open_frontier(self) -> List[SchemeObligation]:
        by_id = {o.obl_id: o for o in self.obligations}
        out: List[SchemeObligation] = []
        for fid in self.frontier_ids:
            obl = by_id.get(fid)
            if obl is not None and obl.status not in ("proved", "invalid"):
                out.append(obl)
        if out:
            return out
        return [
            o for o in self.obligations
            if o.no_nest and o.status not in ("proved", "invalid")
        ]

    def diagnosis_line(self) -> str:
        if self.skipped:
            return f"scheme skipped ({self.skip_reason or 'n/a'})"
        if not self.induct_var:
            return "scheme: empty"
        parts = [o.summary() for o in self.obligations]
        body = "; ".join(parts) if parts else "no obligations"
        extra = ""
        if self.closed:
            extra = f"; closed={self.close_reason or 'yes'}"
        elif self.frontier_ids:
            extra = f"; frontier={len(self.frontier_ids)}"
        if self.goal_gate_status and self.goal_gate_status != "off":
            extra += f"; gate={self.goal_gate_status}"
        mu = f"; μ=`{self.measure_fun}`" if self.measure_fun else ""
        br = "; bridges" if self.bridge_primary else ""
        return (
            f"scheme var=`{self.induct_var}`:`{self.induct_sort}`{mu}{br}; {body}{extra}"
        )

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        return d

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "SchemeAttempt":
        raw = dict(data or {})
        obls = [
            SchemeObligation.from_dict(o) if isinstance(o, dict) else o
            for o in (raw.pop("obligations", None) or [])
        ]
        known = {f.name for f in cls.__dataclass_fields__.values()}  # type: ignore[attr-defined]
        att = cls(**{k: v for k, v in raw.items() if k in known})
        att.obligations = obls
        return att


@dataclass
class SchemeRoundResult:
    """Outcome of one scheme round relative to the current attempt."""

    attempt: SchemeAttempt
    close_parent: bool = False
    nest_children: List[SchemeObligation] = field(default_factory=list)
    formulas_for_usefulness: List[str] = field(default_factory=list)  # always empty
    # Other axes short-proved in the same round (e.g. measure beside structural).
    side_attempts: List[SchemeAttempt] = field(default_factory=list)
