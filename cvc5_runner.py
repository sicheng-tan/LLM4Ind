"""
CVC5/CVC4 runner with rich feedback for solver-guided lemma repair.

Design notes vs Vampire:
- Main prove path: multi-strategy portfolio. Optional --stats / get-difficulty
  hang on that same process (no extra 3s diagnostic before the 60s prove).
- Diagnostic path: short single-strategy run for usefulness-failure sidecars.
- Difficulty: SMT-LIB produce-difficulty / get-difficulty (cvc5-specific).
- Unsat cores on inductive problems are unreliable; we do NOT depend on them
  for lemma pruning (unlike Vampire ucore).
"""

import subprocess
import logging
import time
import os
import re
import signal
import tempfile
import math
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from solver_routing import (
    CVC5_FALLBACK_PROFILES,
    GoalSearchState,
    fallback_enabled,
    fallback_fraction,
    fallback_min_timeout,
    routing_enabled,
)
from solver_relative_metrics import (
    CONJ_SHARE_MIN,
    EXPLOSION_LOG_GAIN,
    INST_PER_SKOLEM_MAX,
    SKOLEM_PER_CONJ_MAX,
    SKOLEM_SHARE_MIN,
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

    def to_dict(self) -> dict:
        return asdict(self)


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
) -> CvcResult:
    """
    Portfolio prove: named CVC5/CVC4 strategies in parallel.
    Default profiles match the paper (simple / inductive / no-ematching / cvc4).
    First unsat wins.

    When collect_stats / collect_difficulty are set, CVC5 strategies get --stats
    and --tlimit-per so a timeout still yields counters / get-difficulty.
    """
    names = profiles or list(CVC5_FALLBACK_PROFILES)
    return _run_cvc_parallel(
        smt2_path,
        timeout,
        names,
        collect_stats=collect_stats,
        collect_difficulty=collect_difficulty,
    )


def run_cvc_probe(
    smt2_path,
    profiles: List[str],
    timeout: int = 2,
) -> Dict[str, CvcResult]:
    """Short sequential diagnostic probes for routing."""
    out: Dict[str, CvcResult] = {}
    for name in profiles:
        if name not in cvc_profile_specs():
            continue
        out[name] = run_cvc_diagnostic(
            smt2_path,
            timeout=timeout,
            collect_difficulty=False,
            profile=name,
        )
    return out


def run_cvc_routed(
    smt2_path,
    timeout: int = 60,
    *,
    state: Optional[GoalSearchState] = None,
    collect_stats: bool = False,
    collect_difficulty: bool = False,
) -> CvcResult:
    """Prove with recommended profiles first, then the paper 4-way portfolio."""
    if not routing_enabled() or state is None or not state.candidate_profiles:
        return run_cvc(
            smt2_path,
            timeout,
            collect_stats=collect_stats,
            collect_difficulty=collect_difficulty,
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
) -> List[str]:
    cmd = [cfg["binary"]] + list(cfg["options"])
    if cfg.get("type") == "CVC5" and (collect_stats or collect_difficulty):
        cmd.append("--stats")
        cmd.append(f"--tlimit-per={max(1, int(timeout * 1000))}")
    cmd.append(str(input_path))
    return cmd


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
        key=lambda r: (len(r.stats or {}), len(r.difficulty or []), len(r.stdout or "")),
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
) -> CvcResult:
    smt2_path = Path(smt2_path)
    specs = cvc_profile_specs()
    strategies = {n: specs[n] for n in names if n in specs}
    if not strategies:
        return CvcResult(status="error", error="no known cvc profiles requested")

    processes = {}
    start = time.time()
    summaries: Dict[str, dict] = {}
    full_results: Dict[str, CvcResult] = {}
    injected_path = None
    try:
        try:
            smt_content = smt2_path.read_text(encoding="utf-8")
        except OSError:
            smt_content = ""
        goal_term = extract_proof_goal_term(smt_content) if smt_content else None
        if collect_difficulty:
            script = _inject_difficulty_script(smt_content or smt2_path.read_text(encoding="utf-8"))
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".smt2", delete=False, encoding="utf-8"
            ) as tf:
                tf.write(script)
                injected_path = Path(tf.name)

        for name, cfg in strategies.items():
            input_path = (
                injected_path
                if collect_difficulty and cfg.get("type") == "CVC5" and injected_path is not None
                else smt2_path
            )
            cmd = _cvc_prove_cmd(
                cfg,
                input_path,
                timeout,
                collect_stats=collect_stats,
                collect_difficulty=collect_difficulty,
            )
            try:
                proc = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    preexec_fn=os.setsid,
                )
                processes[name] = proc
            except FileNotFoundError:
                logging.error("%s binary not found: %s", cfg["type"], cfg["binary"])
                summaries[name] = {"status": "error", "error": "binary not found", "strategy": name}
            except Exception as e:
                logging.error("Failed to start %s: %s", name, e)
                summaries[name] = {"status": "error", "error": str(e), "strategy": name}

        if not processes:
            return CvcResult(status="error", error="no solver process started", portfolio_results=summaries)

        completed = set()
        while time.time() - start < timeout:
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
                        strategies[name]["type"], name, elapsed,
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
        for name in strategies:
            if name not in summaries:
                summaries[name] = {"status": "timeout", "elapsed": round(elapsed, 3), "strategy": name}
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
            strategy=richest.strategy if richest else next(iter(strategies)),
            stats=dict(richest.stats) if richest else {},
            difficulty=list(richest.difficulty) if richest else [],
            stdout=richest.stdout if richest else "",
            stderr=richest.stderr if richest else "",
            portfolio_results=summaries,
            goal_term=goal_term or (richest.goal_term if richest else None),
        )

    finally:
        _cleanup_processes(processes)
        if injected_path is not None:
            try:
                injected_path.unlink()
            except OSError:
                pass


def run_cvc_diagnostic(
    smt2_path,
    timeout: int = 3,
    *,
    collect_difficulty: bool = True,
    profile: Optional[str] = None,
) -> CvcResult:
    """
    Single-strategy cvc5 run with --stats (+ optional difficulty).
    Used for progress comparison / repair hints, not as portfolio prover.
    """
    smt2_path = Path(smt2_path)
    specs = cvc_profile_specs()
    name = profile if profile in specs and specs[profile]["type"] == "CVC5" else "cvc5_inductive"
    cfg = specs[name]
    ms = max(1, int(timeout * 1000))
    cmd = [cfg["binary"]] + list(cfg["options"]) + [f"--tlimit-per={ms}", "--stats", str(smt2_path)]
    result = _execute_single(cmd, timeout + 2, strategy=name)
    try:
        result.goal_term = extract_proof_goal_term(smt2_path.read_text(encoding="utf-8"))
    except OSError:
        result.goal_term = None
    if collect_difficulty:
        diff = run_cvc_difficulty(smt2_path, timeout=min(timeout, 3), profile=name)
        result.difficulty = diff.difficulty
        if not result.goal_term:
            result.goal_term = diff.goal_term
    return result


def run_cvc_difficulty(smt2_path, timeout: int = 3, *, profile: Optional[str] = None) -> CvcResult:
    """
    Run cvc5 on a rewritten SMT script that enables produce-difficulty and
    calls (get-difficulty) after check-sat.
    """
    smt2_path = Path(smt2_path)
    specs = cvc_profile_specs()
    name = profile if profile in specs and specs[profile]["type"] == "CVC5" else "cvc5_inductive"
    cfg = specs[name]
    content = smt2_path.read_text(encoding="utf-8")
    script = _inject_difficulty_script(content)
    ms = max(1, int(timeout * 1000))

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(script)
        tmp_path = tf.name

    try:
        cmd = [cfg["binary"]] + list(cfg["options"]) + [f"--tlimit-per={ms}", tmp_path]
        result = _execute_single(cmd, timeout + 2, strategy=f"{name}_difficulty")
        result.difficulty = parse_cvc_difficulty(result.stdout)
        result.goal_term = extract_proof_goal_term(content)
        return result
    finally:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass


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
    Parse (get-difficulty) output with a balanced s-expr scan.

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
    return out[:12]



def _cvc_stat_rate(stats: Dict[str, int], elapsed: float, key: str) -> float:
    count = int(stats.get(key, 0))
    time_s = elapsed
    ms = stats.get("TOTAL_TIME_MS", 0)
    if ms:
        time_s = max(time_s, ms / 1000.0)
    return activity_rate(count, time_s)


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
    strong = 0

    if is_relative_gain(conj_c, conj_r):
        score += gain_score(conj_c, conj_r, 2.5)
        signals.append(f"more_conjecture_gen(+{pct_label(conj_c, conj_r)}%)")
        strong += 1
    if is_relative_gain(skol_c, skol_r, rare=True):
        score += min(2.0, 0.4 + gain_score(skol_c, skol_r, 1.6))
        signals.append(f"more_skolemize(+{pct_label(skol_c, skol_r)}%)")
        strong += 1
    if is_relative_gain(inst_c, inst_r):
        score += gain_score(inst_c, inst_r, 2.0)
        signals.append(f"more_instantiations(+{pct_label(inst_c, inst_r)}%)")
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

    if baseline.difficulty and candidate.difficulty:
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

    productive = any(
        s.startswith("more_skolemize")
        or s.startswith("goal_difficulty")
        or s.startswith("axiom_difficulty")
        or s.startswith("more_datatype")
        or s.startswith("more_instantiations")
        for s in signals
    )
    # Conjecture-gen is the enumeration-volume proxy; do not treat INST_TOTAL
    # growth itself as explosion (that is also the matching-progress signal).
    if log_gain(conj_c, conj_r) >= EXPLOSION_LOG_GAIN and not productive:
        score -= min(gain_score(conj_c, conj_r, 1.5), 1.5)
        signals.append(f"search_explosion(+{pct_label(conj_c, conj_r)}%)")

    if strong < 2 and "more_skolemize" not in "".join(signals) and "goal_difficulty" not in "".join(signals):
        if score > 0:
            score *= 0.4
            signals.append("weak_single_signal")

    if not signals:
        signals.append("no_measurable_progress")
    return score, signals


def derive_repair_hints(result: CvcResult, context: str = "goal") -> List[dict]:
    """Turn cvc5 failure signals into structured repair hints for the LLM."""
    if result.proved:
        return []

    hints: List[dict] = []
    stats = result.stats

    roles = [
        (t, s, classify_difficulty_term(t, result.goal_term))
        for t, s in result.difficulty
        if s > 0
    ]
    axiom_items = [(t, s) for t, s, role in roles if role == "axiom"]
    cutoff = in_problem_hard_cutoff([s for _, s in axiom_items])
    hard_axioms = [t for t, s in axiom_items if s >= cutoff][:4]
    goal_bits = [t for t, s, role in roles if role == "goal"][:2]

    if hard_axioms or goal_bits:
        hints.append({
            "kind": "high_difficulty_assertions",
            "context": context,
            "detail": (
                "cvc5 difficulty tracking shows these assertions were frequently "
                "involved without finishing the proof. Prefer lemmas that bridge "
                "high-difficulty recursive definitions to the goal."
            ),
            "hard_axioms": hard_axioms,
            "goal_fragments": goal_bits,
            "suggested_actions": [
                "Generate equational lemmas about functions appearing in hard axioms",
                "If a recursive function appears in both hard axioms and the goal, "
                "propose a generalized inductive lemma",
                "Avoid repeating lemmas already marked invalid or useless",
            ],
        })

    conj = stats.get("CONJ_TOTAL", 0)
    skol = stats.get("QUANTIFIERS_SKOLEMIZE", 0)
    inst = stats.get("INST_TOTAL", 0)
    q_activity = conj + skol + inst

    if q_activity > 0:
        conj_share = conj / q_activity
        skol_share = skol / q_activity
        skol_per_conj = skol / max(conj, 1)
        inst_per_skol = inst / max(skol, 1)
        if conj_share >= CONJ_SHARE_MIN and skol_per_conj <= SKOLEM_PER_CONJ_MAX:
            hints.append({
                "kind": "need_stronger_lemma",
                "context": context,
                "detail": (
                    "cvc5 conjecture-gen is a large share of quantifier activity "
                    "but skolem/induction strengthening stays relatively low. "
                    "Likely missing a stronger inductive lemma (generalization)."
                ),
                "suggested_actions": [
                    "Strengthen or generalize the goal into an inductive lemma",
                    "Try associativity/commutativity/distributivity style facts",
                ],
            })
        elif skol_share >= SKOLEM_SHARE_MIN and inst_per_skol < INST_PER_SKOLEM_MAX:
            hints.append({
                "kind": "need_rewrite",
                "context": context,
                "detail": (
                    "cvc5 skolemized (induction-like) but instantiations are sparse "
                    "relative to that skolemization. Missing rewrite-oriented lemmas "
                    "may be blocking matching."
                ),
                "suggested_actions": [
                    "Propose rewrite lemmas whose LHS matches a subterm of the goal",
                    "Unfold recursive definitions one step in a lemma",
                ],
            })

    if result.status in ("timeout", "unknown") and not hints:
        hints.append({
            "kind": "timeout",
            "context": context,
            "detail": "cvc5 timed out / returned unknown without clear difficulty signal.",
            "suggested_actions": [
                "Generate simpler lemmas close to the recursive definitions",
                "Split the goal into smaller equational facts",
            ],
        })

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


def _inject_difficulty_script(content: str) -> str:
    lines = content.splitlines()
    out: List[str] = []
    injected = False
    for line in lines:
        out.append(line)
        if not injected and line.strip().startswith("(set-logic"):
            out.append("(set-option :produce-difficulty true)")
            injected = True
    text = "\n".join(out)
    if "(check-sat)" in text:
        text = text.replace(
            "(check-sat)",
            "(check-sat)\n(get-difficulty)",
            1,
        )
    else:
        text += "\n(check-sat)\n(get-difficulty)\n"
    return text


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
