"""InductionScheme: structural induction obligations + short prove + NEST.

Lightweight v1: no accumulator generalization, no usefulness-C injection,
no child LLM. See ``exp_flags.induction_scheme_enabled``.
"""

from __future__ import annotations

from .bridges import (
    bridge_role,
    generate_bridge_obligations,
    is_bridge_primary,
    pick_or_synthesize_measure,
)
from .constants import (
    CHILD_LLM,
    DEPTH_COST,
    GOAL_GATE_TIMEOUT_S,
    MAX_VARS,
    NEST,
    PROVE_PROFILES,
    PROVE_TIMEOUT_S,
    SCHEME_ATTEMPTS_KEY,
    SCHEME_PROVE_MAX_OBLS,
    VAMPIRE_PROVE_PROFILES,
)
from .dispatch import (
    SchemeSession,
    can_afford_nest,
    consume_pending_scheme_close,
    finalize_after_attempt,
    frontier_backup_prove,
    pop_scheme_dispatch,
    run_nest_children,
    run_scheme_round,
    start_scheme_session,
)
from .generate import (
    generate_scheme,
    generate_scheme_candidates,
    peek_structural_induct_sort,
    select_induct_var,
    select_induct_var_for_measure,
    select_measure_fun,
    validate_scheme,
)
from .ledger import (
    format_scheme_prompt_block,
    harvest_scheme_proved_to_library,
    harvest_scheme_refuted_to_invalid,
    filter_library_excluding_current_scheme,
    scheme_prompt_formulas,
    latest_scheme_attempt,
    load_scheme_attempts,
    save_scheme_attempt,
    scheme_formulas_for_usefulness,
)
from .prove import (
    default_cvc_prove,
    default_vampire_prove,
    prove_goal_gate,
    prove_obligations,
    write_goal_gate_smt,
)
from .mate_glue import scheme_prove_kwargs_for_backend
from .types import SchemeAttempt, SchemeObligation, SchemeRoundResult

__all__ = [
    "CHILD_LLM",
    "DEPTH_COST",
    "GOAL_GATE_TIMEOUT_S",
    "MAX_VARS",
    "NEST",
    "PROVE_PROFILES",
    "PROVE_TIMEOUT_S",
    "SCHEME_ATTEMPTS_KEY",
    "SCHEME_PROVE_MAX_OBLS",
    "VAMPIRE_PROVE_PROFILES",
    "SchemeAttempt",
    "SchemeObligation",
    "SchemeRoundResult",
    "SchemeSession",
    "can_afford_nest",
    "consume_pending_scheme_close",
    "default_cvc_prove",
    "default_vampire_prove",
    "finalize_after_attempt",
    "format_scheme_prompt_block",
    "filter_library_excluding_current_scheme",
    "frontier_backup_prove",
    "bridge_role",
    "generate_bridge_obligations",
    "generate_scheme",
    "generate_scheme_candidates",
    "is_bridge_primary",
    "harvest_scheme_proved_to_library",
    "harvest_scheme_refuted_to_invalid",
    "latest_scheme_attempt",
    "load_scheme_attempts",
    "pick_or_synthesize_measure",
    "peek_structural_induct_sort",
    "pop_scheme_dispatch",
    "prove_goal_gate",
    "prove_obligations",
    "run_nest_children",
    "run_scheme_round",
    "save_scheme_attempt",
    "scheme_formulas_for_usefulness",
    "scheme_prompt_formulas",
    "scheme_prove_kwargs_for_backend",
    "select_induct_var",
    "select_induct_var_for_measure",
    "select_measure_fun",
    "start_scheme_session",
    "validate_scheme",
    "write_goal_gate_smt",
]
