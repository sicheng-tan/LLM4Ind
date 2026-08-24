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

from smt_adt_tester_rewrite import needs_tester_rewrite, rewrite_smtlib_testers
from solver_routing import (
    VAMPIRE_FALLBACK_PROFILE,
    GoalSearchState,
    fallback_enabled,
    fallback_fraction,
    fallback_min_timeout,
    profile_utility_from_stats,
    routing_enabled,
)
from solver_relative_metrics import (
    EXPLOSION_LOG_GAIN,
    INDUCTION_PER_REWRITE_MAX,
    INDUCTION_SHARE_MIN,
    INTEGER_INDUCTION_SHARE_MIN,
    REWRITE_PER_INDUCTION_MAX,
    REWRITE_SHARE_MIN,
    activity_rate,
    gain_score,
    is_relative_gain,
    log_gain,
    pct_label,
)

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass


def _vampire_binary() -> str:
    return os.getenv("VAMPIRE_BINARY", "./vampire/vampire")


# Stats keys that signal rewrite / induction "progress" (CCLemma-inspired).
PROGRESS_STAT_KEYS = (
    "Fw demodulations",
    "Bw demodulations",
    "Fw demodulations to eq. taut.",
    "Forward superposition",
    "Backward superposition",
    "StructuralInduction",
    "InductionApplications",
    "GeneralizedInductionApplications",
    "IntegerInfiniteIntervalInduction",
    "IntegerFiniteIntervalInduction",
)


@dataclass
class VampireResult:
    """Rich Vampire run outcome for usefulness scoring and repair feedback."""
    proved: bool = False
    status: str = "unknown"  # unsat | timeout | unknown | error | incomplete | sat
    elapsed: float = 0.0
    strategy: str = ""
    stats: Dict[str, int] = field(default_factory=dict)
    induction_focus: List[str] = field(default_factory=list)
    induction_formulas: List[str] = field(default_factory=list)
    used_lemma_names: List[str] = field(default_factory=list)
    stdout: str = ""
    stderr: str = ""
    error: Optional[str] = None
    portfolio_results: Dict[str, dict] = field(default_factory=dict)

    def to_dict(self) -> dict:
        return asdict(self)


# Named theory profiles. The paper default is induction_portfolio.
# alasca_arith approximates ALASCA-style arithmetic superposition on this
# Vampire binary (UWA + theory instantiation + arithmetic generalization).
VAMPIRE_PROFILES: Dict[str, dict] = {
    "induction_portfolio": {
        "kind": "portfolio",
        "schedule": "induction",
        "diag": "struct_single",
        "label": "mixed structural/integer induction portfolio (paper default)",
    },
    "struct_induction": {
        "kind": "portfolio",
        "schedule": "struct_induction",
        "diag": "struct_single",
        "label": "structural induction schedule",
    },
    "struct_induction_tip": {
        "kind": "portfolio",
        "schedule": "struct_induction_tip",
        "diag": "struct_single",
        "label": "TIP-oriented structural induction",
    },
    "integer_induction": {
        "kind": "portfolio",
        "schedule": "integer_induction",
        "diag": "int_single",
        "label": "integer induction schedule",
    },
    "smtcomp": {
        "kind": "portfolio",
        "schedule": "smtcomp",
        "diag": "alasca_arith",
        "label": "SMT-COMP schedule (arithmetic / mixed theories)",
    },
    "struct_single": {
        "kind": "vampire",
        "extra": [
            "--induction", "struct",
            "--induction_gen", "on",
            "--induction_on_complex_terms", "on",
            "--avatar", "off",
        ],
        "diag": "struct_single",
        "label": "single-strategy structural induction",
    },
    "int_single": {
        "kind": "vampire",
        "extra": [
            "--induction", "int",
            "--induction_gen", "on",
            "--avatar", "off",
        ],
        "diag": "int_single",
        "label": "single-strategy integer induction",
    },
    "alasca_arith": {
        "kind": "vampire",
        "extra": [
            "--induction", "both",
            "--theory_instantiation", "all",
            "--unification_with_abstraction", "interpreted_only",
            "--arithmetic_subterm_generalizations", "cautious",
            "--avatar", "off",
        ],
        "diag": "alasca_arith",
        "label": "ALASCA-style arithmetic superposition (UWA + theory instantiation)",
    },
}


def run_vampire_with_timeout(smt2_path, timeout=60) -> bool:
    """Backward-compatible boolean wrapper (True iff unsat)."""
    return run_vampire(smt2_path, timeout=timeout).proved


def _vampire_rewrite_enabled() -> bool:
    val = os.getenv("VAMPIRE_REWRITE_TESTERS", "on").strip().lower()
    return val not in ("0", "off", "false", "no")


def prepare_vampire_smt_input(smt2_path: Path) -> Tuple[Path, Optional[Path]]:
    """Return (path_to_feed_vampire, temp_file_to_delete_or_None).

    AutoProofBM `standard/` uses SMT-LIB2 shorthand testers `(is-Cons x)` that
    Vampire 4.9 cannot parse. Rewrite them to `((_ is Cons) x)` in a temp file.
    """
    smt2_path = Path(smt2_path)
    if not _vampire_rewrite_enabled():
        return smt2_path, None
    text = smt2_path.read_text(encoding="utf-8")
    if not needs_tester_rewrite(text):
        return smt2_path, None
    rewritten, n = rewrite_smtlib_testers(text)
    tmp = tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".smt2",
        prefix="vamp_tester_rw_",
        delete=False,
        encoding="utf-8",
    )
    try:
        tmp.write(rewritten)
    finally:
        tmp.close()
    logging.debug(
        "Rewrote %d SMT-LIB2 ADT testers for Vampire: %s -> %s",
        n, smt2_path, tmp.name,
    )
    tmp_path = Path(tmp.name)
    return tmp_path, tmp_path


def run_vampire(
    smt2_path,
    timeout: int = 60,
    *,
    collect_stats: bool = True,
    collect_ucore: bool = False,
    show_induction: bool = False,
    proof_file: Optional[Path] = None,
    profile: Optional[str] = None,
) -> VampireResult:
    """
    Prove with a named Vampire profile.

    Default profile is the paper schedule: portfolio + induction.
    When show_induction is set, induction traces come from this same prove run.
    """
    profile = profile or "induction_portfolio"
    vampire_binary = _vampire_binary()
    if not vampire_binary:
        return VampireResult(status="error", error="VAMPIRE_BINARY not configured", strategy=profile)

    smt2_path = Path(smt2_path)
    run_path, tmp_path = prepare_vampire_smt_input(smt2_path)
    command = _vampire_command(
        vampire_binary,
        profile,
        timeout,
        collect_stats=collect_stats,
        collect_ucore=collect_ucore,
        proof_file=proof_file,
        show_induction=show_induction,
    )
    command.append(str(run_path))
    try:
        result = _execute_vampire(command, timeout, collect_ucore=collect_ucore, strategy=profile)
        return result
    finally:
        if tmp_path is not None and tmp_path.exists():
            try:
                tmp_path.unlink()
            except OSError:
                pass


def run_vampire_diagnostic(
    smt2_path,
    timeout: int = 3,
    *,
    show_induction: bool = True,
    profile: Optional[str] = None,
) -> VampireResult:
    """
    Single-strategy diagnostic run for progress comparison and induction traces.
    Not used as the main prover; portfolio remains authoritative for proved=True.

    If `profile` is a portfolio schedule, the mapped diagnostic single-strategy
    is used so baseline/control/candidate stats stay comparable.
    """
    vampire_binary = _vampire_binary()
    if not vampire_binary:
        return VampireResult(status="error", error="VAMPIRE_BINARY not configured")

    spec = VAMPIRE_PROFILES.get(profile or "struct_single", VAMPIRE_PROFILES["struct_single"])
    diag_name = spec.get("diag") or "struct_single"
    smt2_path = Path(smt2_path)
    run_path, tmp_path = prepare_vampire_smt_input(smt2_path)
    command = _vampire_command(
        vampire_binary,
        diag_name,
        timeout,
        collect_stats=True,
        collect_ucore=False,
        proof_file=None,
        show_induction=show_induction,
    )
    command.append(str(run_path))
    try:
        return _execute_vampire(command, timeout, collect_ucore=False, strategy=diag_name)
    finally:
        if tmp_path is not None and tmp_path.exists():
            try:
                tmp_path.unlink()
            except OSError:
                pass


def run_vampire_probe(
    smt2_path,
    profiles: List[str],
    timeout: int = 2,
) -> Dict[str, VampireResult]:
    """Short sequential probe of named profiles for routing (Phase 1 observability)."""
    out: Dict[str, VampireResult] = {}
    for name in profiles:
        if name not in VAMPIRE_PROFILES:
            continue
        out[name] = run_vampire(
            smt2_path,
            timeout=timeout,
            collect_stats=True,
            collect_ucore=False,
            profile=name,
        )
    return out


def run_vampire_routed(
    smt2_path,
    timeout: int = 60,
    *,
    state: Optional[GoalSearchState] = None,
    collect_stats: bool = True,
    collect_ucore: bool = False,
    show_induction: bool = False,
) -> VampireResult:
    """
    Prove with recommended profiles first, then the paper induction portfolio.

    When routing is disabled, this is identical to run_vampire(...).
    """
    if not routing_enabled() or state is None or not state.candidate_profiles:
        return run_vampire(
            smt2_path,
            timeout,
            collect_stats=collect_stats,
            collect_ucore=collect_ucore,
            show_induction=show_induction,
        )

    summaries: Dict[str, dict] = {}
    start = time.time()

    primary = [p for p in state.candidate_profiles if p in VAMPIRE_PROFILES]
    fallback = [
        p for p in (state.fallback_profiles or [VAMPIRE_FALLBACK_PROFILE])
        if p in VAMPIRE_PROFILES and p not in primary
    ]
    reserve = 0
    if fallback_enabled() and fallback:
        reserve = max(fallback_min_timeout(), int(timeout * fallback_fraction()))
        reserve = min(reserve, max(0, timeout - 1))
    primary_timeout = max(1, timeout - reserve)
    result = _run_vampire_parallel(
        smt2_path,
        primary_timeout,
        primary,
        collect_stats=collect_stats,
        collect_ucore=collect_ucore,
        show_induction=show_induction,
    )
    summaries.update(result.portfolio_results)
    if result.proved:
        result.portfolio_results = summaries
        return result

    remaining = timeout - (time.time() - start)
    if fallback_enabled() and fallback and remaining >= 0.5:
        fb = _run_vampire_parallel(
            smt2_path,
            max(1, min(timeout, math.ceil(remaining))),
            fallback,
            collect_stats=collect_stats,
            collect_ucore=collect_ucore,
            show_induction=show_induction,
        )
        summaries.update(fb.portfolio_results)
        if fb.proved:
            fb.portfolio_results = summaries
            return fb
        result = fb
        result.portfolio_results = summaries
        return result

    result.portfolio_results = summaries
    return result


def _vampire_command(
    binary: str,
    profile: str,
    timeout: int,
    *,
    collect_stats: bool,
    collect_ucore: bool,
    proof_file: Optional[Path],
    show_induction: bool = False,
) -> List[str]:
    spec = VAMPIRE_PROFILES.get(profile)
    if spec is None:
        spec = VAMPIRE_PROFILES["induction_portfolio"]
        profile = "induction_portfolio"
    command = [
        binary,
        "-t", f"{timeout}s",
        "--input_syntax", "smtlib2",
    ]
    if spec["kind"] == "portfolio":
        command.extend(["--mode", "portfolio", "--schedule", spec["schedule"]])
    else:
        command.extend(["--mode", "vampire"])
        command.extend(spec.get("extra") or [])

    if collect_ucore:
        command.extend([
            "--output_mode", "ucore",
            "--ignore_missing_inputs_in_unsat_core", "on",
            "--statistics", "none",
            "--proof", "off",
        ])
    else:
        command.extend([
            "--output_mode", "vampire",
            "--statistics", "full" if collect_stats else "none",
            "--proof", "off",
        ])
        if proof_file is not None:
            command = [c for c in command if c not in ("--proof", "off")]
            command.extend([
                "--proof", "on",
                "--print_proofs_to_file", str(proof_file),
            ])
        if show_induction:
            command.extend(["--show_induction", "on"])
    return command


def _compact_vampire(result: VampireResult) -> dict:
    return {
        "proved": result.proved,
        "status": result.status,
        "elapsed": round(result.elapsed, 3),
        "strategy": result.strategy,
        "stats": result.stats,
        "error": result.error,
    }


def _vampire_result_from_output(
    name: str,
    stdout: str,
    stderr: str,
    elapsed: float,
    returncode: int,
    *,
    collect_ucore: bool,
    timed_out: bool = False,
) -> VampireResult:
    result = VampireResult(strategy=name)
    result.elapsed = elapsed
    result.stdout = stdout or ""
    result.stderr = stderr or ""
    result.status = classify_status(
        result.stdout, result.stderr, returncode, timed_out
    )
    result.proved = result.status == "unsat"
    result.stats = parse_vampire_stats(result.stdout + "\n" + result.stderr)
    focus, formulas = parse_induction_trace(result.stdout + "\n" + result.stderr)
    result.induction_focus = focus
    result.induction_formulas = formulas
    if collect_ucore and result.proved:
        result.used_lemma_names = parse_ucore_lemma_names(result.stdout)
    return result


def _richest_vampire(results: List[VampireResult]) -> Optional[VampireResult]:
    if not results:
        return None
    return max(
        results,
        key=lambda r: (
            len(r.stats or {}),
            len(r.induction_focus or []),
            len(r.stdout or ""),
        ),
    )


def _harvest_proc_output(proc) -> Tuple[str, str]:
    if proc.poll() is None:
        _cleanup_process(proc)
    try:
        stdout, stderr = proc.communicate(timeout=1)
    except Exception:
        return "", ""
    return stdout or "", stderr or ""


def _run_vampire_parallel(
    smt2_path,
    timeout: int,
    profiles: List[str],
    *,
    collect_stats: bool,
    collect_ucore: bool,
    show_induction: bool = False,
) -> VampireResult:
    profiles = [p for p in profiles if p in VAMPIRE_PROFILES]
    if not profiles:
        return run_vampire(
            smt2_path,
            timeout,
            collect_stats=collect_stats,
            collect_ucore=collect_ucore,
            show_induction=show_induction,
        )
    if len(profiles) == 1:
        result = run_vampire(
            smt2_path,
            timeout,
            collect_stats=collect_stats,
            collect_ucore=collect_ucore,
            show_induction=show_induction,
            profile=profiles[0],
        )
        result.portfolio_results = {profiles[0]: _compact_vampire(result)}
        return result

    vampire_binary = _vampire_binary()
    smt2_path = Path(smt2_path)
    run_path, tmp_path = prepare_vampire_smt_input(smt2_path)
    processes = {}
    start = time.time()
    summaries: Dict[str, dict] = {}
    try:
        for name in profiles:
            cmd = _vampire_command(
                vampire_binary,
                name,
                timeout,
                collect_stats=collect_stats,
                collect_ucore=collect_ucore,
                proof_file=None,
                show_induction=show_induction,
            ) + [str(run_path)]
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
                summaries[name] = {"status": "error", "error": "binary not found"}
            except Exception as e:
                summaries[name] = {"status": "error", "error": str(e)}

        if not processes:
            return VampireResult(status="error", error="no vampire process started")

        completed = set()
        full_results: Dict[str, VampireResult] = {}
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
                    summaries[name] = {
                        "proved": False,
                        "status": "error",
                        "elapsed": round(time.time() - start, 3),
                        "strategy": name,
                        "error": str(e),
                    }
                    continue
                result = _vampire_result_from_output(
                    name,
                    stdout or "",
                    stderr or "",
                    time.time() - start,
                    proc.returncode or -1,
                    collect_ucore=collect_ucore,
                )
                full_results[name] = result
                summaries[name] = _compact_vampire(result)
                if result.proved:
                    for other, op in processes.items():
                        if other != name:
                            _cleanup_process(op)
                    result.portfolio_results = summaries
                    return result
            if len(completed) == len(processes):
                break
            time.sleep(0.05)

        elapsed = time.time() - start
        timed_out = len(completed) < len(processes)
        for name, proc in processes.items():
            if name in summaries:
                continue
            stdout, stderr = _harvest_proc_output(proc)
            result = _vampire_result_from_output(
                name,
                stdout,
                stderr,
                elapsed,
                proc.returncode if proc.returncode is not None else -1,
                collect_ucore=collect_ucore,
                timed_out=True,
            )
            full_results[name] = result
            summaries[name] = _compact_vampire(result)
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
        richest = _richest_vampire(list(full_results.values()))
        return VampireResult(
            proved=False,
            status=final_status,
            elapsed=elapsed,
            strategy=richest.strategy if richest else profiles[0],
            stats=dict(richest.stats) if richest else {},
            induction_focus=list(richest.induction_focus) if richest else [],
            induction_formulas=list(richest.induction_formulas) if richest else [],
            stdout=richest.stdout if richest else "",
            stderr=richest.stderr if richest else "",
            portfolio_results=summaries,
        )
    finally:
        for proc in processes.values():
            _cleanup_process(proc)
        if tmp_path is not None and tmp_path.exists():
            try:
                tmp_path.unlink()
            except OSError:
                pass


def parse_vampire_stats(text: str) -> Dict[str, int]:
    """Parse the last statistics block from Vampire output."""
    stats: Dict[str, int] = {}
    # Prefer the last occurrence of each key (portfolio prints many blocks).
    patterns = [
        (r"Generated clauses:\s*(\d+)", "Generated clauses"),
        (r"Final active clauses:\s*(\d+)", "Final active clauses"),
        (r"Final passive clauses:\s*(\d+)", "Final passive clauses"),
        (r"Fw demodulations:\s*(\d+)", "Fw demodulations"),
        (r"Bw demodulations:\s*(\d+)", "Bw demodulations"),
        (r"Fw demodulations to eq\. taut\.:\s*(\d+)", "Fw demodulations to eq. taut."),
        (r"Forward superposition:\s*(\d+)", "Forward superposition"),
        (r"Backward superposition:\s*(\d+)", "Backward superposition"),
        (r"StructuralInduction:\s*(\d+)", "StructuralInduction"),
        (r"InductionApplications:\s*(\d+)", "InductionApplications"),
        (r"GeneralizedInductionApplications:\s*(\d+)", "GeneralizedInductionApplications"),
        (r"IntegerInfiniteIntervalInduction:\s*(\d+)", "IntegerInfiniteIntervalInduction"),
        (r"IntegerFiniteIntervalInduction:\s*(\d+)", "IntegerFiniteIntervalInduction"),
        (r"MaxInductionDepth:\s*(\d+)", "MaxInductionDepth"),
    ]
    for pattern, key in patterns:
        matches = re.findall(pattern, text)
        if matches:
            try:
                stats[key] = int(matches[-1])
            except ValueError:
                pass
    return stats


def parse_induction_trace(text: str) -> Tuple[List[str], List[str]]:
    """
    Extract induction focus literals/terms and induction formulas from
    --show_induction output.
    """
    focus: List[str] = []
    formulas: List[str] = []
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("[Induction]"):
            continue
        m_proc = re.search(r"\[Induction\] process (.+?) in \d+\.", line)
        if m_proc:
            focus.append(m_proc.group(1).strip())
            continue
        m_form = re.search(r"\[Induction\] formula \d+\.\s*(.+?)(?:\s*\[|$)", line)
        if m_form:
            formulas.append(m_form.group(1).strip())
    # De-duplicate while preserving order; keep short list for prompts.
    focus = _dedup_preserve(focus)[:8]
    formulas = _dedup_preserve(formulas)[:4]
    return focus, formulas


def parse_ucore_lemma_names(text: str) -> List[str]:
    """Parse SMT-LIB unsat core names from Vampire --output_mode ucore."""
    names: List[str] = []
    in_core = False
    for line in text.splitlines():
        s = line.strip()
        if s == "(":
            in_core = True
            continue
        if s == ")":
            in_core = False
            continue
        if in_core and s and not s.startswith("ERROR") and not s.startswith("WARNING"):
            # Names are bare identifiers like lemma_1
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s):
                names.append(s)
    return names


def classify_status(stdout: str, stderr: str, returncode: int, timed_out: bool) -> str:
    if timed_out:
        return "timeout"
    text = (stdout + "\n" + stderr).lower()
    if "unsatisfiable" in text or re.search(r"\bunsat\b", text) or "refutation found" in text:
        return "unsat"
    if "satisfiable" in text and "unsatisfiable" not in text:
        # careful: 'unsatisfiable' contains 'satisfiable'
        if re.search(r"(?<!un)satisfiable", text) or re.search(r"\bsat\b", text):
            return "sat"
    if "incomplete strategy" in text or "refutation not found" in text:
        return "incomplete"
    if "user:" in text or "user:" in stderr.lower():
        return "error"
    if "timeout" in text or "time limit" in text:
        return "timeout"
    return "unknown"


def _vampire_stat_rate(
    stats: Dict[str, int],
    elapsed: float,
    *keys: str,
) -> float:
    total = sum(int(stats.get(k, 0)) for k in keys)
    return activity_rate(total, elapsed)


def compute_progress_score(
    baseline: VampireResult,
    candidate: VampireResult,
    *,
    control: Optional[VampireResult] = None,
) -> Tuple[float, List[str]]:
    """
    Score whether adding lemmas made Vampire 'less stuck'.
    Returns (score, human-readable signals). Higher is better; >0 means progress.

    Comparisons use log1p relative gain of per-second rates vs the control
    (or baseline) run, so small Nat tasks and large ADT searches share one gate.
    """
    if candidate.proved:
        return 100.0, ["proved_goal"]
    if candidate.status == "error":
        return -10.0, ["solver_error"]

    signals: List[str] = []
    score = 0.0
    b, c = baseline.stats, candidate.stats
    ref_stats = control.stats if control is not None else b
    ref_elapsed = control.elapsed if control is not None else baseline.elapsed
    cand_elapsed = candidate.elapsed

    dem_c = _vampire_stat_rate(c, cand_elapsed, "Fw demodulations", "Bw demodulations")
    dem_r = _vampire_stat_rate(ref_stats, ref_elapsed, "Fw demodulations", "Bw demodulations")
    taut_c = _vampire_stat_rate(c, cand_elapsed, "Fw demodulations to eq. taut.")
    taut_r = _vampire_stat_rate(ref_stats, ref_elapsed, "Fw demodulations to eq. taut.")
    ind_c = _vampire_stat_rate(
        c, cand_elapsed,
        "InductionApplications", "GeneralizedInductionApplications", "StructuralInduction",
    )
    ind_r = _vampire_stat_rate(
        ref_stats, ref_elapsed,
        "InductionApplications", "GeneralizedInductionApplications", "StructuralInduction",
    )

    strong = 0
    if is_relative_gain(dem_c, dem_r):
        score += gain_score(dem_c, dem_r, 2.5)
        signals.append(
            f"more_demodulations(+{pct_label(dem_c, dem_r)}%)"
        )
        strong += 1
    if is_relative_gain(taut_c, taut_r, rare=True):
        score += min(1.25, 0.5 + gain_score(taut_c, taut_r, 0.75))
        signals.append(f"more_eq_taut_demod(+{pct_label(taut_c, taut_r)}%)")
        strong += 1
    if is_relative_gain(ind_c, ind_r, rare=True):
        score += gain_score(ind_c, ind_r, 2.0)
        signals.append(f"more_induction_activity(+{pct_label(ind_c, ind_r)}%)")
        strong += 1

    # Fewer leftover passive clauses under similar generation can mean better focus.
    gen_b = b.get("Generated clauses", 0)
    gen_c = c.get("Generated clauses", 0)
    pas_b = b.get("Final passive clauses", 0)
    pas_c = c.get("Final passive clauses", 0)
    if gen_b >= 1 and gen_c >= 1 and pas_b > 0:
        ratio_b = pas_b / max(gen_b, 1)
        ratio_c = pas_c / max(gen_c, 1)
        better_than_control = True
        if control is not None:
            gen_k = ref_stats.get("Generated clauses", 0)
            pas_k = ref_stats.get("Final passive clauses", 0)
            if gen_k >= 1 and pas_k > 0:
                ratio_k = pas_k / max(gen_k, 1)
                better_than_control = ratio_c + 1e-9 < 0.9 * ratio_k
        if better_than_control and ratio_c + 1e-9 < 0.7 * ratio_b:
            score += 1.0
            signals.append("lower_passive_ratio")
            strong += 1

    # Volume-up without product (eq-taut / induction / focus) ≈ explosion.
    gen_c_rate = activity_rate(gen_c, cand_elapsed)
    gen_r_rate = activity_rate(ref_stats.get("Generated clauses", 0), ref_elapsed)
    productive = any(
        s.startswith("more_eq_taut_demod")
        or s.startswith("more_induction")
        or s == "lower_passive_ratio"
        for s in signals
    )
    if log_gain(gen_c_rate, gen_r_rate) >= EXPLOSION_LOG_GAIN and not productive:
        penalty = min(gain_score(gen_c_rate, gen_r_rate, 1.5), 1.5)
        score -= penalty
        signals.append(f"search_explosion(+{pct_label(gen_c_rate, gen_r_rate)}%)")

    # Require at least two independent signals, or one strong induction/eq-taut signal.
    if strong < 2 and "more_eq_taut_demod" not in "".join(signals) and "more_induction" not in "".join(signals):
        if score > 0:
            score *= 0.35
            signals.append("weak_single_signal")

    if not signals and candidate.status in ("timeout", "incomplete", "unknown"):
        signals.append("no_measurable_progress")

    return score, signals


def derive_repair_hints(result: VampireResult, context: str = "goal") -> List[dict]:
    """
    Turn Vampire failure signals into structured repair hints for the next LLM prompt.
    """
    hints: List[dict] = []
    stats = result.stats

    dem = stats.get("Fw demodulations", 0) + stats.get("Bw demodulations", 0)
    ind = (
        stats.get("InductionApplications", 0)
        + stats.get("StructuralInduction", 0)
        + stats.get("GeneralizedInductionApplications", 0)
    )
    mix = ind + dem
    int_ind = (
        stats.get("IntegerInfiniteIntervalInduction", 0)
        + stats.get("IntegerFiniteIntervalInduction", 0)
    )
    struct_like = ind

    if result.induction_focus:
        hints.append({
            "kind": "induction_stuck",
            "context": context,
            "detail": (
                "Vampire attempted induction on these goal-related literals/terms but "
                "could not finish the proof. Prefer lemmas that discharge the inductive "
                "step (often commutativity/associativity or rewrite bridges)."
            ),
            "induction_focus": result.induction_focus[:6],
            "suggested_actions": [
                "Generate equational lemmas about constructors appearing in the focus terms",
                "If a recursive function appears on both sides, try a generalized form",
                "Avoid repeating lemmas already marked invalid or useless",
            ],
        })

    # Diagnose mix imbalance (shares), not absolute counts.
    if mix > 0:
        ind_share = ind / mix
        dem_share = dem / mix
        rewrite_per_ind = dem / max(ind, 1)
        ind_per_rewrite = ind / max(dem, 1)
        if ind_share >= INDUCTION_SHARE_MIN and rewrite_per_ind < REWRITE_PER_INDUCTION_MAX:
            hints.append({
                "kind": "need_rewrite",
                "context": context,
                "detail": (
                    "Induction is a large share of Vampire activity but rewriting is "
                    "scarce relative to it. Likely missing equational lemmas that "
                    "enable rewriting under the IH."
                ),
                "suggested_actions": [
                    "Propose rewrite-oriented lemmas (distributivity, fold/unfold identities)",
                    "Prefer lemmas whose LHS matches a subterm of the proof goal",
                ],
            })
        elif dem_share >= REWRITE_SHARE_MIN and ind_per_rewrite < INDUCTION_PER_REWRITE_MAX:
            hints.append({
                "kind": "need_induction_lemma",
                "context": context,
                "detail": (
                    "Rewriting dominates search while productive induction stays a "
                    "small share. Try a stronger inductive lemma (generalization / "
                    "strengthen conclusion)."
                ),
                "suggested_actions": [
                    "Strengthen or generalize the goal into an inductive lemma",
                    "Introduce an accumulator / helper-function identity if applicable",
                ],
            })

    ind_all = struct_like + int_ind
    if ind_all > 0 and int_ind / ind_all >= INTEGER_INDUCTION_SHARE_MIN:
        hints.append({
            "kind": "need_arithmetic_lemma",
            "context": context,
            "detail": (
                "Integer-interval induction dominates structural induction. "
                "Prefer arithmetic bridge / monotonicity / recurrence lemmas "
                "rather than ADT constructor facts."
            ),
            "suggested_actions": [
                "Generate arithmetic bridge or monotonicity lemmas",
                "Strengthen recurrences rather than adding constructor equalities",
            ],
        })

    if result.status == "timeout" and not hints:
        hints.append({
            "kind": "timeout",
            "context": context,
            "detail": "Vampire timed out without a clear induction/rewrite signal.",
            "suggested_actions": [
                "Generate simpler lemmas closer to the recursive definitions",
                "Split the goal into smaller equational facts",
            ],
        })

    return hints


def _dedup_preserve(items: List[str]) -> List[str]:
    seen = set()
    out = []
    for x in items:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def _execute_vampire(
    command: List[str],
    timeout: int,
    *,
    collect_ucore: bool,
    strategy: str = "",
) -> VampireResult:
    result = VampireResult(strategy=strategy)
    try:
        logging.debug("启动Vampire: %s", " ".join(command))
        proc = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            preexec_fn=os.setsid,
        )
        start = time.time()
        timed_out = False
        try:
            # Leave only a small collection grace period so routed fallback
            # retains its reserved wall-clock budget.
            stdout, stderr = proc.communicate(timeout=timeout + 1)
        except subprocess.TimeoutExpired:
            timed_out = True
            _cleanup_process(proc)
            stdout, stderr = "", ""
            try:
                stdout, stderr = proc.communicate(timeout=1)
            except Exception:
                pass

        result.elapsed = time.time() - start
        result.stdout = stdout or ""
        result.stderr = stderr or ""
        result.status = classify_status(
            result.stdout, result.stderr, proc.returncode if proc.returncode is not None else -1, timed_out
        )
        result.proved = result.status == "unsat"
        result.stats = parse_vampire_stats(result.stdout + "\n" + result.stderr)
        focus, formulas = parse_induction_trace(result.stdout + "\n" + result.stderr)
        result.induction_focus = focus
        result.induction_formulas = formulas
        if collect_ucore and result.proved:
            result.used_lemma_names = parse_ucore_lemma_names(result.stdout)

        if result.proved:
            logging.info(
                "Vampire验证成功: unsat (耗时: %.2f秒, status=%s)",
                result.elapsed, result.status,
            )
        else:
            logging.debug(
                "Vampire未证出 (status=%s, 耗时: %.2f秒, stats_keys=%s)",
                result.status, result.elapsed, list(result.stats.keys())[:6],
            )
        return result
            
    except FileNotFoundError:
        logging.error("Vampire可执行文件未找到: %s", command[0] if command else "?")
        return VampireResult(status="error", error="binary not found")
    except Exception as e:
        logging.error("启动Vampire进程失败: %s", e)
        return VampireResult(status="error", error=str(e))


def _cleanup_process(proc):
    """清理进程，包括其子进程"""
    if proc.poll() is None:
        try:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            except (OSError, ProcessLookupError):
                proc.terminate()
            try:
                proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                except (OSError, ProcessLookupError):
                    proc.kill()
                proc.wait()
        except Exception as e:
            logging.error("终止Vampire进程时出错: %s", e)
