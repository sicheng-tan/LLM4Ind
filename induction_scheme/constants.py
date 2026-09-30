"""Hard-wired InductionScheme defaults (not exposed as env knobs)."""

from __future__ import annotations

# Short prove budget per obligation (seconds).
PROVE_TIMEOUT_S = 10

# Same budget for optional axioms∧base∧step ⊢ G gate.
GOAL_GATE_TIMEOUT_S = 10

# CVC profiles for scheme short prove / frontier re-prove / goal gate.
# Single profile: both-axes prove already doubles work; cvc4 overlap was low.
PROVE_PROFILES = ("cvc5_inductive",)

# At most one induct variable per node (sequential nesting picks another
# binder on the child goal — not simultaneous multi-var induction).
MAX_VARS = 1

# Each nested scheme child costs this many depth units vs MAX_RECURSION_DEPTH.
# Scheme nesting shares the lemma-tree depth budget: a node may still
# generate base/step and short-prove at the last usable depth; it just cannot
# spawn another scheme child when ``depth + DEPTH_COST >= max_depth``.
DEPTH_COST = 1

# Soft enable for scheme→child nesting (``>0`` allows nest while depth permits).
# Multi-hop nested induction (e.g. xs → ys → zs) is limited by shared
# ``max_depth``, not by burning this to zero after one hop.
NEST = 1

# Cap short-prove obligations per scheme axis (priority order; rest → frontier).
SCHEME_PROVE_MAX_OBLS = 8

# Child nodes never call an LLM in the lightweight plan.
CHILD_LLM = False

SCHEME_ATTEMPTS_KEY = "scheme_attempts"
SCHEME_PENDING_KEY = "scheme_pending_close"
SCHEME_DISPATCH_KEY = "scheme_dispatch"
