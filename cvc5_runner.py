"""
CVC5/CVC4 runner with rich feedback for solver-guided lemma repair.

Design notes vs Vampire:
- Main prove path: multi-strategy portfolio. Optional --stats / difficulty
  hang on that same process (no extra 3s diagnostic before the 60s prove).
- Diagnostic path: short single-strategy run for usefulness-failure sidecars.
- Difficulty: CVC5 ``--produce-difficulty --dump-difficulty`` dumps scores after
  check-sat (no SMT ``(get-difficulty)``). Still needs ``--tlimit-per`` to end
  check-sat cleanly, plus a short wall-clock grace before hard-kill.
- Unsat cores on inductive problems are unreliable; we do NOT depend on them
  for lemma pruning (unlike Vampire, which also no longer prunes via ucore).
"""

import subprocess
import logging
import time
import os
import re
import signal
import math
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from llm_time_budget import remaining_task_s
from solver_routing import (
    CVC5_FALLBACK_PROFILES,
    GoalSearchState,
    fallback_enabled,
    fallback_fraction,
    fallback_min_timeout,
    routing_enabled,
)
from solver_relative_metrics import (
    EXPLOSION_LOG_GAIN,
    INST_OF_MATCHING_MAX,
    LOG_GAIN_MIN,
    SKOLEM_PER_CONJ_MAX,
    gate_overshoot,
    activity_rate,
    gain_score,
    in_problem_hard_cutoff,
    is_relative_drop,
    is_relative_gain,
    log_gain,
    pct_label,
    relative_drop,
)

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

try:
    import psutil
except ImportError:
    psutil = None


def _cvc5_binary() -> str:
    return os.getenv("CVC5_BINARY", "./cvc/cvc5-Linux-x86_64-static/bin/cvc5")


def _cvc4_binary() -> str:
    return os.getenv("CVC4_BINARY", "./cvc/cvc4_binary/cvc4-1.6-x86_64-linux-opt")


# Extra ±pattern arms: only E-matching profiles. no_ematching / cvc4 stay bare.
PATTERN_CONTRAST_PROFILES = ("cvc5_simple", "cvc5_inductive")


def cvc_portfolio_jobs(
    names: Sequence[str],
    smt2_path,
    pattern_smt2_path=None,
) -> List[Tuple[str, str, Path]]:
    """Bare portfolio jobs, plus ``simple``/``inductive`` +pattern when gated.

    Each item is ``(result_name, spec_name, smt_path)``. Pattern arms are
    added only when ``pattern_smt2_path`` is set *and* that spec is already
    in this wave (default 4-way → 6-way).
    """
    smt2_path = Path(smt2_path)
    specs = cvc_profile_specs()
    jobs: List[Tuple[str, str, Path]] = []
    seen_specs = set()
    for name in names:
        if name not in specs:
            continue
        jobs.append((name, name, smt2_path))
        seen_specs.add(name)
    if pattern_smt2_path:
        pat = Path(pattern_smt2_path)
        for spec_name in PATTERN_CONTRAST_PROFILES:
            if spec_name in seen_specs:
                jobs.append((f"{spec_name}+pattern", spec_name, pat))
    return jobs


# After --tlimit-per ends check-sat, allow this many seconds for --dump-difficulty
# / stats flush before the portfolio wall-clock kill. Override with CVC_DIFFICULTY_GRACE_S.
# Empirically: 2s still loses dumps on some 20–60s portfolio timeouts; 5s is safer.
_DEFAULT_DIFFICULTY_GRACE_S = 5.0
_MIN_DIFFICULTY_GRACE_S = 0.5


def _difficulty_grace_cap_s() -> float:
    raw = os.getenv("CVC_DIFFICULTY_GRACE_S", "").strip()
    if raw:
        try:
            return max(0.0, float(raw))
        except ValueError:
            pass
    return _DEFAULT_DIFFICULTY_GRACE_S


def cvc_time_budget(
    prove_timeout_s: float,
    *,
    collect_difficulty: bool,
) -> Tuple[float, float]:
    """Return ``(tlimit_s, wall_s)`` for one CVC prove.

    ``tlimit_s`` drives ``--tlimit-per`` (ends check-sat). ``wall_s`` is the
    process wait before hard-kill. When collecting difficulty, ``wall_s`` is
    ``tlimit_s + grace`` so ``--dump-difficulty`` can flush; grace shrinks near
    the task deadline (``remaining_task_s``).
    """
    prove = max(0.5, float(prove_timeout_s))
    if not collect_difficulty:
        return prove, prove

    grace_cap = _difficulty_grace_cap_s()
    rem = remaining_task_s()
    if rem is None:
        return prove, prove + grace_cap

    wall_cap = max(0.5, float(rem))
    if prove + grace_cap <= wall_cap:
        return prove, prove + grace_cap
    if prove + _MIN_DIFFICULTY_GRACE_S <= wall_cap:
        return prove, wall_cap
    if prove <= wall_cap:
        # No room for grace: prefer keeping the prove slice; may lose difficulty.
        return prove, wall_cap
    # Task nearly exhausted: shrink both.
    return wall_cap, wall_cap


@dataclass
class CvcResult:
    """Rich CVC5/CVC4 outcome for usefulness scoring and repair feedback."""
    proved: bool = False
    status: str = "unknown"  # unsat | timeout | unknown | error | sat
    elapsed: float = 0.0
    strategy: str = ""
    stats: Dict[str, int] = field(default_factory=dict)
    # List of (assertion_snippet, difficulty_score), sorted desc by score.
    difficulty: List[Tuple[str, int]] = field(default_factory=list)
    used_lemma_names: List[str] = field(default_factory=list)  # usually empty for cvc5
    stdout: str = ""
    stderr: str = ""
    error: Optional[str] = None
    portfolio_results: Dict[str, dict] = field(default_factory=dict)
    # Proof-goal assertion body from the SMT script, when known.
    goal_term: Optional[str] = None
    # (-o inst) per-quantifier instantiation counts: (term_or_qid, count).
    instantiations: List[Tuple[str, int]] = field(default_factory=list)
    # Compact ``(get-model)`` text when status is sat (optional).
    model_text: Optional[str] = None

    def to_dict(self) -> dict:
        return asdict(self)


# Prompt / invalid-reason budget for solver counterexamples (longer than LLM tag).
MAX_CEX_REASON_CHARS = 400
_CEX_TIMEOUT_S = 2


def run_cvc_solver_with_timeout(smt2_path, timeout=60) -> bool:
    """Backward-compatible boolean wrapper (True iff unsat)."""
    return run_cvc(smt2_path, timeout=timeout).proved


def cvc_profile_specs() -> Dict[str, dict]:
    cvc5 = _cvc5_binary()
    cvc4 = _cvc4_binary()
    return {
        "cvc5_simple": {
            "binary": cvc5,
            "options": ["--lang=smt2", "--full-saturate-quant"],
            "type": "CVC5",
        },
        "cvc5_inductive": {
            "binary": cvc5,
            "options": [
                "--lang=smt2",
                "--full-saturate-quant",
                "--quant-ind",
                "--conjecture-gen",
            ],
            "type": "CVC5",
        },
        "cvc5_inductive_no_ematching": {
            "binary": cvc5,
            "options": [
                "--lang=smt2",
                "--full-saturate-quant",
                "--quant-ind",
                "--conjecture-gen",
                "--no-e-matching",
            ],
            "type": "CVC5",
        },
        "cvc4_default": {
            "binary": cvc4,
            "options": [
                "--quant-ind",
                "--quant-cf",
                "--conjecture-gen",
                "--full-saturate-quant",
                "--lang=smt2.6",
            ],
            "type": "CVC4",
        },
        "adt_structural": {
            "binary": cvc5,
            "options": [
                "--lang=smt2",
                "--full-saturate-quant",
                "--quant-ind",
                "--dt-stc-ind",
            ],
            "type": "CVC5",
        },
        "integer_recursive": {
            "binary": cvc5,
            "options": [
                "--lang=smt2",
                "--full-saturate-quant",
                "--quant-ind",
                "--int-wf-ind",
            ],
            "type": "CVC5",
        },
        "controlled_conjecture": {
            "binary": cvc5,
            "options": [
                "--lang=smt2",
                "--full-saturate-quant",
                "--quant-ind",
                "--conjecture-gen",
                "--conjecture-gen-max-depth=2",
                "--conjecture-gen-per-round=5",
            ],
            "type": "CVC5",
        },
    }


def _compact_cvc(result: CvcResult) -> dict:
    return {
        "proved": result.proved,
        "status": result.status,
        "elapsed": round(result.elapsed, 3),
        "strategy": result.strategy,
        "stats": result.stats,
        "error": result.error,
    }


def run_cvc(
    smt2_path,
    timeout: int = 60,
    *,
    collect_stats: bool = False,
    collect_difficulty: bool = False,
    profiles: Optional[List[str]] = None,
    pattern_smt2_path=None,
) -> CvcResult:
    """
    Portfolio prove: named CVC5/CVC4 strategies in parallel.
    Default profiles match the paper (simple / inductive / no-ematching / cvc4).
    First unsat wins.

    ``pattern_smt2_path``: when set, also race ``cvc5_simple+pattern`` and
    ``cvc5_inductive+pattern`` on that SMT (6-way if the default 4 names run).
    """
    names = profiles or list(CVC5_FALLBACK_PROFILES)
    extra = {}
    if pattern_smt2_path:
        extra["pattern_smt2_path"] = pattern_smt2_path
    return _run_cvc_parallel(
        smt2_path,
        timeout,
        names,
        collect_stats=collect_stats,
        collect_difficulty=collect_difficulty,
        **extra,
    )


def cvc_probeable_profiles(names: List[str]) -> List[str]:
    """Keep CVC5 names only. CVC4 has no --stats / produce-difficulty."""
    specs = cvc_profile_specs()
    return [n for n in names if specs.get(n, {}).get("type") == "CVC5"]


def run_cvc_probe(
    smt2_path,
    profiles: List[str],
    timeout: int = 2,
) -> Dict[str, CvcResult]:
    """Short sequential diagnostic probes for routing (CVC5 only)."""
    out: Dict[str, CvcResult] = {}
    for name in cvc_probeable_profiles(list(profiles)):
        out[name] = _run_named_cvc_profile(
            smt2_path,
            timeout,
            name,
            collect_stats=True,
            collect_difficulty=False,
        )
    return out


def run_cvc_routed(
    smt2_path,
    timeout: int = 60,
    *,
    state: Optional[GoalSearchState] = None,
    collect_stats: bool = False,
    collect_difficulty: bool = False,
    pattern_smt2_path=None,
) -> CvcResult:
    """Prove with recommended profiles first, then the paper 4-way portfolio."""
    extra = {}
    if pattern_smt2_path:
        extra["pattern_smt2_path"] = pattern_smt2_path
    if not routing_enabled() or state is None or not state.candidate_profiles:
        return run_cvc(
            smt2_path,
            timeout,
            collect_stats=collect_stats,
            collect_difficulty=collect_difficulty,
            **extra,
        )

    start = time.time()
    specs = cvc_profile_specs()
    primary = [p for p in state.candidate_profiles if p in specs]
    fallback = [
        p for p in (state.fallback_profiles or CVC5_FALLBACK_PROFILES)
        if p in specs and p not in primary
    ]
    reserve = 0
    if fallback_enabled() and fallback:
        reserve = max(fallback_min_timeout(), int(timeout * fallback_fraction()))
        reserve = min(reserve, max(0, timeout - 1))
    primary_timeout = max(1, timeout - reserve)
    result = _run_cvc_parallel(
        smt2_path,
        primary_timeout,
        primary,
        collect_stats=collect_stats,
        collect_difficulty=collect_difficulty,
        **extra,
    )
    summaries = dict(result.portfolio_results)
    if result.proved:
        result.portfolio_results = summaries
        return result

    remaining = timeout - (time.time() - start)
    if fallback_enabled() and fallback and remaining >= 0.5:
        fb = _run_cvc_parallel(
            smt2_path,
            max(1, min(timeout, math.ceil(remaining))),
            fallback,
            collect_stats=collect_stats,
            collect_difficulty=collect_difficulty,
            **extra,
        )
        summaries.update(fb.portfolio_results)
        fb.portfolio_results = summaries
        return fb
    result.portfolio_results = summaries
    return result


def _cvc_prove_cmd(
    cfg: dict,
    input_path: Path,
    timeout: int,
    *,
    collect_stats: bool,
    collect_difficulty: bool,
    tlimit_s: Optional[float] = None,
) -> List[str]:
    """Build a CVC command. ``tlimit_s`` overrides ``timeout`` for ``--tlimit-per``."""
    cmd = [cfg["binary"]] + list(cfg["options"])
    limit = float(timeout if tlimit_s is None else tlimit_s)
    tlimit_ms = max(1, int(round(limit * 1000)))
    if cfg.get("type") == "CVC5" and (collect_stats or collect_difficulty):
        cmd.append("--stats")
        cmd.append("-o")
        cmd.append("inst")
        cmd.append(f"--tlimit-per={tlimit_ms}")
        if collect_difficulty:
            cmd.append("--produce-difficulty")
            cmd.append("--dump-difficulty")
            cmd.append("--difficulty-mode=lemma-literal-all")
    elif cfg.get("type") == "CVC4" and tlimit_s is not None:
        # Stop CVC4 at the prove slice so portfolio grace is reserved for CVC5
        # difficulty dump (CVC4 has no difficulty output).
        cmd.append(f"--tlimit-per={tlimit_ms}")
    cmd.append(str(input_path))
    return cmd


def _run_named_cvc_profile(
    smt2_path,
    timeout: int,
    profile: str,
    *,
    collect_stats: bool = True,
    collect_difficulty: bool = False,
) -> CvcResult:
    """Run one named CVC5/CVC4 profile as-is (no sidecar remapping)."""
    smt2_path = Path(smt2_path)
    specs = cvc_profile_specs()
    if profile not in specs:
        return CvcResult(
            status="error",
            strategy=profile,
            error=f"unknown profile: {profile}",
        )
    cfg = specs[profile]
    if collect_difficulty and cfg.get("type") != "CVC5":
        collect_difficulty = False
    tlimit_s, wall_s = cvc_time_budget(
        timeout, collect_difficulty=collect_difficulty,
    )
    try:
        content = smt2_path.read_text(encoding="utf-8")
    except OSError:
        content = ""
    goal_term = extract_proof_goal_term(content) if content else None
    cmd = _cvc_prove_cmd(
        cfg,
        smt2_path,
        timeout,
        collect_stats=collect_stats,
        collect_difficulty=collect_difficulty,
        tlimit_s=tlimit_s,
    )
    result = _execute_single(cmd, int(math.ceil(wall_s)), strategy=profile)
    result.goal_term = goal_term
    if collect_difficulty:
        result.difficulty = parse_cvc_difficulty(
            result.stdout + "\n" + result.stderr
        )
    return result


def _cvc_result_from_output(
    name: str,
    stdout: str,
    stderr: str,
    elapsed: float,
    *,
    collect_stats: bool,
    collect_difficulty: bool,
    timed_out: bool = False,
    goal_term: Optional[str] = None,
) -> CvcResult:
    stdout = stdout or ""
    stderr = stderr or ""
    text = stdout + "\n" + stderr
    if timed_out:
        status = "timeout"
        proved = False
    elif _stdout_is_unsat(stdout):
        status = "unsat"
        proved = True
    elif re.search(r"(?m)^sat\s*$", stdout.lower()):
        status = "sat"
        proved = False
    else:
        status = "unknown"
        proved = False
    result = CvcResult(
        proved=proved,
        status=status,
        elapsed=elapsed,
        strategy=name,
        stdout=stdout,
        stderr=stderr,
    )
    if collect_stats:
        result.stats = parse_cvc_stats(text)
        result.instantiations = parse_cvc_instantiations(text)
    if collect_difficulty:
        result.difficulty = parse_cvc_difficulty(text)
    if goal_term:
        result.goal_term = goal_term
    return result


def _richest_cvc(results: List[CvcResult]) -> Optional[CvcResult]:
    if not results:
        return None
    return max(
        results,
        key=lambda r: (
            len(r.stats or {}),
            len(r.difficulty or []),
            len(r.instantiations or []),
            len(r.stdout or ""),
        ),
    )


def _harvest_proc_output(proc) -> Tuple[str, str]:
    if proc.poll() is None:
        _kill_proc(proc)
    try:
        stdout, stderr = proc.communicate(timeout=1)
    except Exception:
        return "", ""
    return stdout or "", stderr or ""


def _run_cvc_parallel(
    smt2_path,
    timeout: int,
    names: List[str],
    *,
    collect_stats: bool,
    collect_difficulty: bool = False,
    pattern_smt2_path=None,
) -> CvcResult:
    smt2_path = Path(smt2_path)
    specs = cvc_profile_specs()
    jobs = cvc_portfolio_jobs(names, smt2_path, pattern_smt2_path)
    if not jobs:
        return CvcResult(status="error", error="no known cvc profiles requested")
    spec_by_result = {result_name: spec_name for result_name, spec_name, _path in jobs}

    tlimit_s, wall_s = cvc_time_budget(
        timeout, collect_difficulty=collect_difficulty,
    )
    processes = {}
    start = time.time()
    summaries: Dict[str, dict] = {}
    full_results: Dict[str, CvcResult] = {}
    try:
        try:
            smt_content = smt2_path.read_text(encoding="utf-8")
        except OSError:
            smt_content = ""
        goal_term = extract_proof_goal_term(smt_content) if smt_content else None

        for result_name, spec_name, job_path in jobs:
            cfg = specs[spec_name]
            cmd = _cvc_prove_cmd(
                cfg,
                job_path,
                timeout,
                collect_stats=collect_stats,
                collect_difficulty=collect_difficulty,
                tlimit_s=tlimit_s,
            )
            try:
                proc = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    preexec_fn=os.setsid,
                )
                processes[result_name] = proc
            except FileNotFoundError:
                logging.error("%s binary not found: %s", cfg["type"], cfg["binary"])
                summaries[result_name] = {
                    "status": "error",
                    "error": "binary not found",
                    "strategy": result_name,
                }
            except Exception as e:
                logging.error("Failed to start %s: %s", result_name, e)
                summaries[result_name] = {
                    "status": "error",
                    "error": str(e),
                    "strategy": result_name,
                }

        if not processes:
            return CvcResult(status="error", error="no solver process started", portfolio_results=summaries)

        completed = set()
        while time.time() - start < wall_s:
            for name, proc in processes.items():
                if name in completed:
                    continue
                if proc.poll() is None:
                    continue
                completed.add(name)
                try:
                    stdout, stderr = proc.communicate(timeout=1)
                except Exception as e:
                    logging.error("communicate %s failed: %s", name, e)
                    summaries[name] = {
                        "proved": False,
                        "status": "error",
                        "elapsed": round(time.time() - start, 3),
                        "strategy": name,
                        "error": str(e),
                    }
                    continue

                elapsed = time.time() - start
                result = _cvc_result_from_output(
                    name,
                    stdout or "",
                    stderr or "",
                    elapsed,
                    collect_stats=collect_stats,
                    collect_difficulty=collect_difficulty,
                    goal_term=goal_term,
                )
                full_results[name] = result
                if result.proved:
                    _cleanup_processes(processes, exclude=name)
                    logging.info(
                        "%s验证成功: unsat (策略: %s, %.2fs)",
                        specs[spec_by_result[name]]["type"], name, elapsed,
                    )
                    summaries[name] = _compact_cvc(result)
                    result.portfolio_results = summaries
                    return result
                summaries[name] = _compact_cvc(result)

            if len(completed) == len(processes):
                break
            time.sleep(0.05)

        elapsed = time.time() - start
        timed_out = len(completed) < len(processes)
        for name, proc in processes.items():
            if name in summaries:
                continue
            stdout, stderr = _harvest_proc_output(proc)
            result = _cvc_result_from_output(
                name,
                stdout,
                stderr,
                elapsed,
                collect_stats=collect_stats,
                collect_difficulty=collect_difficulty,
                timed_out=True,
                goal_term=goal_term,
            )
            full_results[name] = result
            summaries[name] = _compact_cvc(result)
        for result_name, _spec_name, _path in jobs:
            if result_name not in summaries:
                summaries[result_name] = {
                    "status": "timeout",
                    "elapsed": round(elapsed, 3),
                    "strategy": result_name,
                }
        logging.warning("CVC5/CVC4验证超时或失败 (耗时: %.2f秒)", elapsed)
        statuses = [item.get("status") for item in summaries.values()]
        if timed_out:
            final_status = "timeout"
        elif statuses and all(status == "error" for status in statuses):
            final_status = "error"
        elif "unknown" in statuses:
            final_status = "unknown"
        elif "sat" in statuses:
            final_status = "sat"
        else:
            final_status = "unknown"
        richest = _richest_cvc(list(full_results.values()))
        return CvcResult(
            proved=False,
            status=final_status,
            elapsed=elapsed,
            strategy=richest.strategy if richest else jobs[0][0],
            stats=dict(richest.stats) if richest else {},
            difficulty=list(richest.difficulty) if richest else [],
            stdout=richest.stdout if richest else "",
            stderr=richest.stderr if richest else "",
            portfolio_results=summaries,
            goal_term=goal_term or (richest.goal_term if richest else None),
            instantiations=list(richest.instantiations) if richest else [],
        )

    finally:
        _cleanup_processes(processes)


def cvc_diagnostic_profile(profile: Optional[str]) -> str:
    """Sidecar 3s strategy. CVC4 cannot produce-difficulty, so it maps to cvc5_inductive.

    Probes use `_run_named_cvc_profile` and do not go through this remap.
    """
    specs = cvc_profile_specs()
    if profile in specs and specs[profile]["type"] == "CVC5":
        return profile
    return "cvc5_inductive"


def run_cvc_diagnostic(
    smt2_path,
    timeout: int = 3,
    *,
    collect_difficulty: bool = True,
    profile: Optional[str] = None,
) -> CvcResult:
    """
    Single-strategy cvc5 run with --stats (+ optional difficulty on the same process).
    Used for progress comparison / repair hints, not as portfolio prover.
    """
    smt2_path = Path(smt2_path)
    name = cvc_diagnostic_profile(profile)
    cfg = cvc_profile_specs()[name]
    tlimit_s, wall_s = cvc_time_budget(timeout, collect_difficulty=collect_difficulty)
    try:
        content = smt2_path.read_text(encoding="utf-8")
    except OSError:
        content = ""
    goal_term = extract_proof_goal_term(content) if content else None
    cmd = _cvc_prove_cmd(
        cfg,
        smt2_path,
        timeout,
        collect_stats=True,
        collect_difficulty=collect_difficulty,
        tlimit_s=tlimit_s,
    )
    result = _execute_single(cmd, int(math.ceil(wall_s)), strategy=name)
    result.goal_term = goal_term
    if collect_difficulty:
        result.difficulty = parse_cvc_difficulty(result.stdout + "\n" + result.stderr)
    return result


def run_cvc_difficulty(smt2_path, timeout: int = 3, *, profile: Optional[str] = None) -> CvcResult:
    """
    Run cvc5 with ``--produce-difficulty --dump-difficulty`` (same process as prove).
    """
    return run_cvc_diagnostic(
        smt2_path, timeout=timeout, collect_difficulty=True, profile=profile,
    )


def parse_cvc_stats(text: str) -> Dict[str, int]:
    """Parse --stats counters into a flat int dict."""
    stats: Dict[str, int] = {}
    # Also parse compact "KEY: n" forms inside braces by scanning all KEY: n
    for key in (
        "QUANTIFIERS_INST_E_MATCHING",
        "QUANTIFIERS_INST_E_MATCHING_SIMPLE",
        "QUANTIFIERS_INST_CBQI_PROP",
        "QUANTIFIERS_INST_CBQI_CONFLICT",
        "QUANTIFIERS_SKOLEMIZE",
        "QUANTIFIERS_CONJ_GEN_GT_ENUM",
        "QUANTIFIERS_CONJ_GEN_SPLIT",
        "DATATYPES_INST",
        "DATATYPES_SPLIT",
        "DATATYPES_UNIF",
        "DATATYPES_LABEL_EXH",
        "DATATYPES_COLLAPSE_SEL",
    ):
        matches = re.findall(rf"{re.escape(key)}\s*:\s*(\d+)", text)
        if matches:
            # Sum if multiple blocks; usually one
            stats[key] = sum(int(x) for x in matches)

    # Derived aggregates for scoring
    stats["INST_TOTAL"] = (
        stats.get("QUANTIFIERS_INST_E_MATCHING", 0)
        + stats.get("QUANTIFIERS_INST_E_MATCHING_SIMPLE", 0)
        + stats.get("QUANTIFIERS_INST_CBQI_PROP", 0)
    )
    stats["CONJ_TOTAL"] = (
        stats.get("QUANTIFIERS_CONJ_GEN_GT_ENUM", 0)
        + stats.get("QUANTIFIERS_CONJ_GEN_SPLIT", 0)
    )
    stats["DT_TOTAL"] = (
        stats.get("DATATYPES_INST", 0)
        + stats.get("DATATYPES_SPLIT", 0)
        + stats.get("DATATYPES_UNIF", 0)
    )
    m = re.search(r"global::totalTime\s*=\s*(\d+)ms", text)
    if m:
        stats["TOTAL_TIME_MS"] = int(m.group(1))
    return stats


def parse_cvc_instantiations(text: str) -> List[Tuple[str, int]]:
    """Parse `-o inst` lines: (num-instantiations <qid-or-formula> N)."""
    items: List[Tuple[str, int]] = []
    i = 0
    needle = "(num-instantiations"
    while True:
        j = (text or "").find(needle, i)
        if j < 0:
            break
        expr, nxt = _read_sexpr(text, j)
        if not expr:
            i = j + len(needle)
            continue
        kids = _sexpr_children(expr)
        if len(kids) >= 3 and kids[0] == "num-instantiations":
            term = kids[1]
            try:
                count = int(kids[-1])
            except ValueError:
                i = nxt
                continue
            if term.startswith("("):
                term = normalize_smt_term(term)
            if count >= 0 and term:
                items.append((term, count))
        i = nxt if nxt > j else j + len(needle)

    best: Dict[str, int] = {}
    out: List[Tuple[str, int]] = []
    seen = set()
    for term, count in items:
        key = canonical_smt_term(term) if str(term).startswith("(") else term
        best[key] = max(best.get(key, 0), count)
    for term, count in sorted(items, key=lambda x: -x[1]):
        key = canonical_smt_term(term) if str(term).startswith("(") else term
        if key in seen:
            continue
        seen.add(key)
        out.append((term, best[key]))
    return out[:12]



def _skip_ws_and_comments(text: str, i: int) -> int:
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
            continue
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        break
    return i


def _read_sexpr(text: str, i: int):
    """Return (lexeme, next_index) or (None, i) at EOF / closing paren."""
    i = _skip_ws_and_comments(text, i)
    n = len(text)
    if i >= n or text[i] == ")":
        return None, i
    if text[i] == "(":
        start = i
        i += 1
        depth = 1
        while i < n and depth:
            c = text[i]
            if c == ";":
                while i < n and text[i] != "\n":
                    i += 1
                continue
            if c == "|":
                i += 1
                while i < n and text[i] != "|":
                    i += 1
                i = min(i + 1, n)
                continue
            if c == '"':
                i += 1
                while i < n:
                    if text[i] == "\\":
                        i += 2
                        continue
                    if text[i] == '"':
                        i += 1
                        break
                    i += 1
                continue
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            i += 1
        return text[start:i], i
    start = i
    if text[i] == "|":
        i += 1
        while i < n and text[i] != "|":
            i += 1
        i = min(i + 1, n)
        return text[start:i], i
    if text[i] == '"':
        i += 1
        while i < n:
            if text[i] == "\\":
                i += 2
                continue
            if text[i] == '"':
                i += 1
                break
            i += 1
        return text[start:i], i
    while i < n and text[i] not in " \t\r\n();|\"":
        i += 1
    return text[start:i], i


def _sexpr_children(expr: str) -> List[str]:
    expr = expr.strip()
    if not expr.startswith("("):
        return []
    inner = expr[1:-1] if expr.endswith(")") else expr[1:]
    kids: List[str] = []
    i = 0
    while True:
        kid, i = _read_sexpr(inner, i)
        if kid is None:
            break
        kids.append(kid)
    return kids


def normalize_smt_term(term: str) -> str:
    return re.sub(r"\s+", " ", (term or "").strip())


def strip_named_annotation(term: str) -> str:
    kids = _sexpr_children(term)
    if kids and kids[0] == "!" and len(kids) >= 2:
        return strip_named_annotation(kids[1])
    return term


def _unwrap_assert(term: str) -> str:
    kids = _sexpr_children(term)
    if kids and kids[0] == "assert" and len(kids) >= 2:
        return kids[1]
    return term


def _sorted_vars(expr: str) -> List[Tuple[str, str]]:
    kids = _sexpr_children(expr)
    if not kids:
        return []
    if not kids[0].startswith("(") and len(kids) >= 2:
        return [(kids[0], kids[1])]
    out: List[Tuple[str, str]] = []
    for kid in kids:
        parts = _sexpr_children(kid)
        if len(parts) >= 2:
            out.append((parts[0], parts[1]))
    return out


def _alpha_normalize(expr: str, env=None, nxt=None) -> str:
    env = dict(env or {})
    nxt = nxt if nxt is not None else [0]
    expr = expr.strip()
    if not expr.startswith("("):
        return env.get(expr, expr)
    kids = _sexpr_children(expr)
    if not kids:
        return "()"
    head = kids[0]
    if head in ("forall", "exists") and len(kids) >= 3:
        binders = _sorted_vars(kids[1])
        new_env = dict(env)
        bind_parts = []
        for name, sort in binders:
            fresh = f"_b{nxt[0]}"
            nxt[0] += 1
            new_env[name] = fresh
            bind_parts.append(f"({fresh} {_alpha_normalize(sort, env, nxt)})")
        body = _alpha_normalize(kids[2], new_env, nxt)
        extra = " ".join(_alpha_normalize(k, new_env, nxt) for k in kids[3:])
        core = f"({head} ({' '.join(bind_parts)}) {body}"
        return core + (f" {extra})" if extra else ")")
    return "(" + " ".join(_alpha_normalize(k, env, nxt) for k in kids) + ")"


def canonical_smt_term(term: str) -> str:
    body = _unwrap_assert(strip_named_annotation(normalize_smt_term(term)))
    return _alpha_normalize(normalize_smt_term(body))


def terms_match(a: str, b: str) -> bool:
    if not a or not b:
        return False
    return canonical_smt_term(a) == canonical_smt_term(b)


def _head_symbol(term: str) -> str:
    kids = _sexpr_children(term)
    if kids:
        return kids[0]
    return term.strip()


def classify_difficulty_term(term: str, goal_term: Optional[str] = None) -> str:
    """Return 'goal', 'axiom', or 'other'."""
    body = _unwrap_assert(strip_named_annotation(term))
    if goal_term and terms_match(body, goal_term):
        return "goal"
    head = _head_symbol(body)
    if head == "not":
        kids = _sexpr_children(body)
        inner = kids[1] if len(kids) > 1 else ""
        inner_head = _head_symbol(inner)
        if goal_term:
            # A negated formula that is not the proof goal is still an axiom/lemma.
            return "axiom" if inner_head in ("forall", "exists") else "other"
        if inner_head in ("forall", "exists"):
            return "goal"
        return "other"
    if head in ("forall", "exists"):
        return "axiom"
    return "other"


_PROOF_GOAL_BLOCK = re.compile(
    r";\s*proof goal\b[^\n]*\n(?P<body>.*?);\s*proof goal end\b",
    re.IGNORECASE | re.DOTALL,
)


def _assert_bodies(smt: str) -> List[str]:
    bodies: List[str] = []
    i = 0
    while True:
        expr, i = _read_sexpr(smt, i)
        if expr is None:
            break
        kids = _sexpr_children(expr)
        if kids and kids[0] == "assert" and len(kids) >= 2:
            bodies.append(kids[1])
    return bodies


def extract_proof_goal_term(smt: str) -> Optional[str]:
    """Proof-goal assertion body from `; proof goal` markers, else last negated quantifier."""
    if not smt:
        return None
    m = _PROOF_GOAL_BLOCK.search(smt)
    if m:
        bodies = _assert_bodies(m.group("body"))
        if bodies:
            return normalize_smt_term(strip_named_annotation(bodies[0]))
    for body in reversed(_assert_bodies(smt)):
        if classify_difficulty_term(body, None) == "goal":
            return normalize_smt_term(strip_named_annotation(body))
    return None


def prepare_smt_for_get_model(smt: str) -> str:
    """Ensure ``:produce-models`` and a trailing ``(get-model)`` after ``(check-sat)``."""
    text = smt or ""
    if "produce-models" not in text:
        text = "(set-option :produce-models true)\n" + text
    if "(get-model)" not in text:
        if re.search(r"\(check-sat\)", text):
            text = re.sub(
                r"\(check-sat\)",
                "(check-sat)\n(get-model)",
                text,
                count=1,
            )
        else:
            text = text.rstrip() + "\n(check-sat)\n(get-model)\n"
    return text


def smt_negate_proof_goal_assert(smt: str) -> str:
    """Rewrite ``; proof goal (assert φ)`` into ``(assert (not φ))`` for cex search.

    Validation files assert φ positively; after unsat we seek a model of ¬φ.
    If the body is already ``(not ...)``, leave it unchanged.
    """
    def _repl(match: re.Match) -> str:
        body = (match.group(1) or "").strip()
        stripped = body
        if stripped.startswith("(not ") or stripped.startswith("(not\n"):
            return match.group(0)
        return f"; proof goal\n(assert (not {body}))\n; proof goal end"

    return re.sub(
        r";\s*proof goal\s*\(assert\s+(.+?)\)\s*;\s*proof goal end",
        _repl,
        smt,
        count=1,
        flags=re.DOTALL | re.IGNORECASE,
    )


def parse_cvc_model(text: str) -> Optional[str]:
    """Extract a compact model block from cvc5 stdout after ``(get-model)``.

    Accepts ``sat`` or ``unknown`` followed by a ``define-fun`` model — some
    quantifier problems report unknown while still printing a witness.
    """
    raw = text or ""
    # Prefer a top-level s-expression that contains define-fun (standard get-model).
    best: Optional[str] = None
    best_len = 0
    i = 0
    while i < len(raw):
        if raw[i] != "(":
            i += 1
            continue
        expr, nxt = _read_sexpr(raw, i)
        if expr is None:
            break
        if "define-fun" in expr or "define-funs-rec" in expr:
            if len(expr) > best_len:
                best = expr
                best_len = len(expr)
        i = nxt if nxt > i else i + 1
    if best:
        return re.sub(r"\s+", " ", best).strip()
    # Fallback: lines after sat/unknown until blank.
    lines = []
    seen_status = False
    for line in raw.splitlines():
        if re.match(r"(?i)^(sat|unknown)\s*$", line.strip()):
            seen_status = True
            continue
        if not seen_status:
            continue
        if re.match(r"(?i)^(unsat|timeout)\b", line.strip()):
            break
        if line.strip().startswith("(") or lines:
            lines.append(line.rstrip())
        if lines and not line.strip():
            break
    blob = " ".join(x.strip() for x in lines if x.strip())
    return re.sub(r"\s+", " ", blob).strip() or None


def format_counterexample_reason(
    model_text: Optional[str],
    *,
    fallback: str = "solver:sat",
    limit: int = MAX_CEX_REASON_CHARS,
) -> str:
    """Build an invalid/node reason that includes the solver model when available."""
    model = (model_text or "").strip()
    if not model:
        return fallback
    body = model if len(model) <= limit - len("Counterexample: ") else (
        model[: max(0, limit - len("Counterexample: ") - 3)] + "..."
    )
    return f"Counterexample: {body}"


def run_cvc_counterexample(
    smt2_path,
    timeout: int = _CEX_TIMEOUT_S,
    *,
    profile: str = "cvc5_simple",
    negate_proof_goal: bool = False,
) -> CvcResult:
    """Short CVC5 run that asks for a model on sat (for invalid / refutation reasons).

    ``negate_proof_goal``: flip validation-style ``(assert φ)`` to ``(assert (not φ))``
    so a lemma that contradicted axioms can still yield a concrete witness.
    """
    import tempfile

    src = Path(smt2_path)
    try:
        content = src.read_text(encoding="utf-8")
    except OSError as exc:
        return CvcResult(status="error", error=str(exc), strategy=profile)

    if negate_proof_goal:
        content = smt_negate_proof_goal_assert(content)
    content = prepare_smt_for_get_model(content)

    specs = cvc_profile_specs()
    cfg = specs.get(profile) or specs.get("cvc5_simple")
    if not cfg or cfg.get("type") != "CVC5":
        return CvcResult(status="error", error="no CVC5 profile for model query", strategy=profile)

    with tempfile.TemporaryDirectory(prefix="cvc_cex_") as tmp:
        cex_path = Path(tmp) / "cex.smt2"
        cex_path.write_text(content, encoding="utf-8")
        cmd = [cfg["binary"]] + list(cfg["options"]) + [str(cex_path)]
        # Prefer a light quantifier schedule; models only need a sat witness.
        if "--full-saturate-quant" not in cmd:
            pass
        result = _execute_single(cmd, max(1, int(timeout)), strategy=profile)
        result.goal_term = extract_proof_goal_term(content)
        result.model_text = parse_cvc_model(result.stdout + "\n" + result.stderr)
        # A printed model is a usable witness even when the solver says unknown.
        if result.model_text and result.status in ("unknown", "timeout", ""):
            result.status = "sat"
        return result


def counterexample_reason_for_smt(
    smt2_path,
    *,
    timeout: int = _CEX_TIMEOUT_S,
    negate_proof_goal: bool = False,
    fallback: str = "solver:sat",
) -> str:
    """Return ``Counterexample: …`` or ``fallback`` after a short model query."""
    result = run_cvc_counterexample(
        smt2_path,
        timeout=timeout,
        negate_proof_goal=negate_proof_goal,
    )
    if result.model_text:
        return format_counterexample_reason(result.model_text, fallback=fallback)
    if result.status == "sat":
        return fallback
    return fallback


def _parse_difficulty_entry(expr: str) -> Optional[Tuple[str, int]]:
    kids = _sexpr_children(expr)
    if len(kids) != 2:
        return None
    term, score_tok = kids
    if not re.fullmatch(r"-?\d+", score_tok):
        return None
    if not term.startswith("("):
        return None
    return normalize_smt_term(term), int(score_tok)


def _parse_difficulty_list(expr: str) -> List[Tuple[str, int]]:
    items: List[Tuple[str, int]] = []
    for kid in _sexpr_children(expr):
        parsed = _parse_difficulty_entry(kid)
        if parsed is None:
            return []
        items.append(parsed)
    return items


def parse_cvc_difficulty(text: str) -> List[Tuple[str, int]]:
    """
    Parse ``--dump-difficulty`` (or legacy ``(get-difficulty)``) output with a
    balanced s-expr scan.

    Each entry is `( <s-expr> <int> )`. Nested SMT such as
    `(plus (succ n) m)` is allowed; a one-level parenthesis regex is not.
    """
    items: List[Tuple[str, int]] = []
    i = 0
    while True:
        expr, i = _read_sexpr(text, i)
        if expr is None:
            break
        if not expr.startswith("("):
            continue
        as_entry = _parse_difficulty_entry(expr)
        if as_entry is not None:
            items.append(as_entry)
            continue
        items.extend(_parse_difficulty_list(expr))

    items = [(t, s) for t, s in items if s > 0]
    items.sort(key=lambda x: -x[1])
    seen = set()
    out: List[Tuple[str, int]] = []
    for t, s in items:
        if t not in seen:
            seen.add(t)
            out.append((t, s))
    return out



def _cvc_stat_rate(stats: Dict[str, int], elapsed: float, key: str) -> float:
    count = int(stats.get(key, 0))
    time_s = elapsed
    ms = stats.get("TOTAL_TIME_MS", 0)
    if ms:
        time_s = max(time_s, ms / 1000.0)
    return activity_rate(count, time_s)


def difficulty_dump_complete(difficulty: Optional[List[Tuple[str, int]]]) -> bool:
    """True when CVC returned at least one positive score.

    Official dumps omit difficulty-0 assertions. Our former top-12 cap is gone,
    so a non-empty dump may treat unlisted assertions as 0. An empty list means
    the dump is missing (timeout/no flush), not that everything is 0.
    """
    return bool(difficulty)


def compute_progress_score(
    baseline: CvcResult,
    candidate: CvcResult,
    *,
    control: Optional[CvcResult] = None,
) -> Tuple[float, List[str]]:
    """
    Score whether lemmas made cvc5 less stuck, using relative stats deltas.

    Gains are log1p relative increases of per-second rates vs the control
    (or baseline) run. Difficulty uses in-problem relative drops, not a
    fixed point cutoff.
    """
    if candidate.proved:
        return 100.0, ["proved_goal"]
    if candidate.status == "error":
        return -10.0, ["solver_error"]

    c = candidate.stats
    ref_stats = control.stats if control is not None else baseline.stats
    ref_elapsed = control.elapsed if control is not None else baseline.elapsed
    cand_elapsed = candidate.elapsed
    signals: List[str] = []
    score = 0.0

    conj_c = _cvc_stat_rate(c, cand_elapsed, "CONJ_TOTAL")
    conj_r = _cvc_stat_rate(ref_stats, ref_elapsed, "CONJ_TOTAL")
    inst_c = _cvc_stat_rate(c, cand_elapsed, "INST_TOTAL")
    inst_r = _cvc_stat_rate(ref_stats, ref_elapsed, "INST_TOTAL")
    skol_c = _cvc_stat_rate(c, cand_elapsed, "QUANTIFIERS_SKOLEMIZE")
    skol_r = _cvc_stat_rate(ref_stats, ref_elapsed, "QUANTIFIERS_SKOLEMIZE")
    dt_c = _cvc_stat_rate(c, cand_elapsed, "DT_TOTAL")
    dt_r = _cvc_stat_rate(ref_stats, ref_elapsed, "DT_TOTAL")
    matching_c = conj_c + inst_c
    matching_r = conj_r + inst_r
    strong = 0

    if is_relative_gain(matching_c, matching_r):
        score += gain_score(matching_c, matching_r, 2.5)
        if log_gain(inst_c, inst_r) >= log_gain(conj_c, conj_r):
            signals.append(f"more_instantiations(+{pct_label(inst_c, inst_r)}%)")
        else:
            signals.append(f"more_conjecture_gen(+{pct_label(conj_c, conj_r)}%)")
        strong += 1
    if is_relative_gain(skol_c, skol_r, rare=True):
        score += min(2.0, 0.4 + gain_score(skol_c, skol_r, 1.6))
        signals.append(f"more_skolemize(+{pct_label(skol_c, skol_r)}%)")
        strong += 1
    if is_relative_gain(dt_c, dt_r, rare=True):
        score += gain_score(dt_c, dt_r, 1.5)
        signals.append(f"more_datatype_inference(+{pct_label(dt_c, dt_r)}%)")
        strong += 1

    goal_term = candidate.goal_term or baseline.goal_term
    if control is not None and not goal_term:
        goal_term = control.goal_term

    def goal_diff(res: CvcResult) -> Optional[int]:
        g = goal_term or res.goal_term
        for term, s in res.difficulty:
            if classify_difficulty_term(term, g) == "goal":
                return s
        return None

    gb, gc = goal_diff(baseline), goal_diff(candidate)
    if gb is not None and gc is not None and is_relative_drop(gb, gc):
        drop = relative_drop(gb, gc)
        score += 1.5 * min(drop / 0.5, 1.0)
        signals.append(f"goal_difficulty_drop({gb}->{gc},{int(round(100 * drop))}%)")
        strong += 1

    if (
        difficulty_dump_complete(baseline.difficulty)
        and difficulty_dump_complete(candidate.difficulty)
    ):
        def axiom_map(res: CvcResult) -> dict:
            g = goal_term or res.goal_term
            out = {}
            for t, s in res.difficulty:
                if classify_difficulty_term(t, g) == "axiom":
                    out[canonical_smt_term(t)] = s
            return out

        b_ax = axiom_map(baseline)
        c_ax = axiom_map(candidate)
        dropped = 0
        for key, old_s in b_ax.items():
            if key not in c_ax:
                dropped += 1
            elif is_relative_drop(old_s, c_ax[key]):
                dropped += 1
        if dropped >= 1:
            score += min(dropped * 0.75, 2.0)
            signals.append(f"axiom_difficulty_drop(x{dropped})")
            strong += 1

    product = any(
        s.startswith("more_skolemize")
        or s.startswith("goal_difficulty")
        or s.startswith("axiom_difficulty")
        or s.startswith("more_datatype")
        for s in signals
    )
    if log_gain(conj_c, conj_r) >= EXPLOSION_LOG_GAIN and not product:
        score -= min(gain_score(conj_c, conj_r, 1.5), 1.5)
        signals.append(f"search_explosion(+{pct_label(conj_c, conj_r)}%)")
    if (
        log_gain(inst_c, inst_r) >= EXPLOSION_LOG_GAIN
        and log_gain(conj_c, conj_r) >= LOG_GAIN_MIN
        and not product
    ):
        score -= min(gain_score(inst_c, inst_r, 1.5), 1.5)
        signals.append(f"search_explosion(+{pct_label(inst_c, inst_r)}%)")

    if strong < 2 and "more_skolemize" not in "".join(signals) and "goal_difficulty" not in "".join(signals):
        if score > 0:
            score *= 0.4
            signals.append("weak_single_signal")

    if not signals:
        signals.append("no_measurable_progress")
    return score, signals


def rarely_instantiated_axioms(
    hard_axioms: List[str],
    instantiations: Optional[List[Tuple[str, int]]],
    *,
    limit: int = 3,
) -> List[str]:
    """Hard axioms with formula-shaped inst traces but zero matching counts.

    If `-o inst` only printed qids (no formulas), return empty — we cannot tell.
    """
    if not hard_axioms or not instantiations:
        return []
    formula_shaped = [t for t, _ in instantiations if str(t).startswith("(")]
    if not formula_shaped:
        return []
    rare: List[str] = []
    for axiom in hard_axioms:
        count = _inst_count_for_axiom(axiom, instantiations)
        if count == 0:
            rare.append(axiom)
        if len(rare) >= limit:
            break
    return rare


def _inst_count_for_axiom(
    axiom: str,
    instantiations: List[Tuple[str, int]],
) -> Optional[int]:
    """Attributed inst count, or 0 if formulas were dumped but this axiom never matched."""
    can = canonical_smt_term(axiom)
    best: Optional[int] = None
    for term, n in instantiations:
        if not str(term).startswith("("):
            continue
        if canonical_smt_term(term) == can:
            best = n if best is None else max(best, n)
    return 0 if best is None else best


def hard_axioms_from_difficulty(
    difficulty: Optional[List[Tuple[str, int]]],
    goal_term: Optional[str] = None,
    *,
    limit: int = 4,
) -> List[str]:
    """Hard axioms for LLM prompts: same goal/axiom split as derive_repair_hints."""
    axiom_scores = [
        s
        for t, s in (difficulty or [])
        if s > 0 and classify_difficulty_term(t, goal_term) == "axiom"
    ]
    cutoff = in_problem_hard_cutoff(axiom_scores)
    return [
        t
        for t, s in (difficulty or [])
        if s > 0
        and classify_difficulty_term(t, goal_term) == "axiom"
        and s >= cutoff
    ][:limit]


def derive_repair_hints(result: CvcResult, context: str = "goal") -> List[dict]:
    """Turn cvc5 failure signals into structured repair hints for the LLM.

    Emits high_difficulty_assertions. need_rewrite / need_stronger_lemma and
    generic timeout are intentionally disabled (commented) as noisy for the LLM;
    rewrite-scarce mix is still available to the ``:pattern`` gate via stats.
    """
    if result.proved:
        return []

    hints: List[dict] = []
    stats = result.stats

    roles = [
        (t, s, classify_difficulty_term(t, result.goal_term))
        for t, s in result.difficulty
        if s > 0
    ]
    hard_axioms = hard_axioms_from_difficulty(result.difficulty, result.goal_term)
    goal_bits = [t for t, s, role in roles if role == "goal"][:2]
    rare = rarely_instantiated_axioms(hard_axioms, result.instantiations)

    if hard_axioms or goal_bits:
        hints.append({
            "kind": "high_difficulty_assertions",
            "context": context,
            "detail": (
                "CVC5 difficulty marks these input assertions as runtime hotspots "
                "(lemma-literal-all), not proof dependencies or instantiation counts."
            ),
            "hard_axioms": hard_axioms,
            "rarely_instantiated": rare,
            "goal_fragments": goal_bits,
            "suggested_actions": [
                "Propose a lemma using functions from a hotspot axiom and the CURRENT goal",
            ],
        })
        if rare:
            hints[-1]["detail"] += (
                " Some hotspot axioms had no matching instantiations; "
                "a rewrite whose LHS matches them or the goal may help triggering."
            )

    conj = stats.get("CONJ_TOTAL", 0)
    skol = stats.get("QUANTIFIERS_SKOLEMIZE", 0)
    inst = stats.get("INST_TOTAL", 0)
    q_activity = conj + skol + inst

    if q_activity > 0:
        matching = skol + inst
        inst_of_matching = inst / max(matching, 1)
        # Disabled: need_stronger_lemma — skolem/conj low is often "not instantiating"
        # (bridge already present / needs :pattern), but the prompt text pushes the
        # LLM to strengthen/generalize the whole goal and misleads retarget.
        # skol_per_conj = skol / max(conj, 1)
        # if conj > 0 and skol_per_conj <= SKOLEM_PER_CONJ_MAX:
        #     hints.append({
        #         "kind": "need_stronger_lemma",
        #         "priority": 1,
        #         "context": context,
        #         "detail": (
        #             "Skolem/induction strengthening is low relative to conjecture-gen "
        #             "(skolem/conj ≤ 0.05). Likely missing a stronger inductive lemma."
        #         ),
        #         "strength": round(gate_overshoot(skol_per_conj, SKOLEM_PER_CONJ_MAX), 4),
        #         "suggested_actions": [
        #             "Strengthen or generalize the goal into an inductive lemma",
        #             "Try associativity/commutativity/distributivity style facts",
        #         ],
        #     })
        # Disabled: need_rewrite — mix ratio (inst/(skol+inst) < 0.75) mainly
        # tells the LLM to emit equational/rewrite lemmas; it is laggy when C
        # changes and is a weaker prompt signal than high-difficulty axioms.
        # The same stats still feed rewrite_scarce_stats in smt_patterns.
        # if skol > 0 and inst_of_matching < INST_OF_MATCHING_MAX:
        #     hints.append({
        #         "kind": "need_rewrite",
        #         "priority": 2,
        #         "context": context,
        #         "detail": (
        #             "cvc5 skolemized but instantiations are not the majority of "
        #             "skolem+matching activity. Missing rewrite-oriented lemmas "
        #             "may be blocking matching."
        #         ),
        #         "strength": round(gate_overshoot(inst_of_matching, INST_OF_MATCHING_MAX), 4),
        #         "suggested_actions": [
        #             "Propose rewrite lemmas whose LHS matches a subterm of the goal",
        #             "Unfold recursive definitions one step in a lemma",
        #         ],
        #     })

    # Disabled: generic timeout hint — low information; success/fail both emit it often.
    # if result.status in ("timeout", "unknown") and not hints:
    #     hints.append({
    #         "kind": "timeout",
    #         "context": context,
    #         "detail": "cvc5 timed out / returned unknown without clear difficulty signal.",
    #         "suggested_actions": [
    #             "Generate simpler lemmas close to the recursive definitions",
    #             "Split the goal into smaller equational facts",
    #         ],
    #     })

    return hints


# ---------------------------------------------------------------------------
# Internals
# ---------------------------------------------------------------------------

def _stdout_is_unsat(stdout: str) -> bool:
    for line in stdout.splitlines():
        s = line.strip().lower()
        if s == "unsat":
            return True
        if s == "sat":
            return False
    return "unsat" in stdout.lower() and not re.search(
        r"(?m)^(sat)\s*$", stdout.lower()
    )


def _execute_single(cmd: List[str], timeout: int, strategy: str) -> CvcResult:
    result = CvcResult(strategy=strategy)
    try:
        logging.debug("启动CVC诊断: %s", " ".join(cmd))
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            preexec_fn=os.setsid,
        )
        start = time.time()
        timed_out = False
        try:
            # Keep collection overhead bounded; routed calls reserve time for
            # the paper fallback.
            stdout, stderr = proc.communicate(timeout=timeout + 1)
        except subprocess.TimeoutExpired:
            timed_out = True
            _kill_proc(proc)
            stdout, stderr = "", ""
            try:
                stdout, stderr = proc.communicate(timeout=1)
            except Exception:
                pass

        result.elapsed = time.time() - start
        result.stdout = stdout or ""
        result.stderr = stderr or ""
        text = result.stdout + "\n" + result.stderr
        result.stats = parse_cvc_stats(text)
        result.instantiations = parse_cvc_instantiations(text)

        if timed_out:
            result.status = "timeout"
        elif _stdout_is_unsat(result.stdout):
            result.status = "unsat"
            result.proved = True
        elif re.search(r"(?m)^sat\s*$", result.stdout.lower()):
            result.status = "sat"
        elif "unknown" in result.stdout.lower():
            result.status = "unknown"
        else:
            result.status = "timeout" if "interrupted" in text.lower() else "unknown"

        return result
    except FileNotFoundError:
        return CvcResult(status="error", error=f"binary not found: {cmd[0]}", strategy=strategy)
    except Exception as e:
        return CvcResult(status="error", error=str(e), strategy=strategy)


def _kill_proc(proc):
    if proc.poll() is not None:
        return
    try:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        except (OSError, ProcessLookupError):
            proc.terminate()
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (OSError, ProcessLookupError):
                proc.kill()
            proc.wait()
    except Exception as e:
        logging.error("kill cvc process failed: %s", e)


def _cleanup_processes(processes, exclude=None):
    for name, proc in processes.items():
        if exclude and name == exclude:
            continue
        if proc.poll() is None:
            _kill_proc(proc)
            if psutil is not None:
                try:
                    if psutil.pid_exists(proc.pid):
                        parent = psutil.Process(proc.pid)
                        for child in parent.children(recursive=True):
                            try:
                                child.kill()
                            except psutil.NoSuchProcess:
                                pass
                        try:
                            parent.kill()
                        except psutil.NoSuchProcess:
                            pass
                except Exception:
                    pass
