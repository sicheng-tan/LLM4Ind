import subprocess
import logging
import time
import os
import re
import signal
import tempfile
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from smt_adt_tester_rewrite import needs_tester_rewrite, rewrite_smtlib_testers
from solver_routing import GoalSearchState, VAMPIRE_RACE_PROFILES
from solver_relative_metrics import (
    EXPLOSION_LOG_GAIN,
    INDUCTION_SHARE_MAX,
    INTEGER_INDUCTION_SHARE_MIN,
    MAX_INDUCTION_DEPTH_HINT,
    REWRITE_PER_INDUCTION_MAX,
    SUPERPOSITION_PER_REWRITE_MIN,
    gate_overshoot,
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

# Mix and progress share this definition of "induction activity".
_VAMPIRE_STRUCT_INDUCTION_KEYS = (
    "InductionApplications",
    "StructuralInduction",
    "GeneralizedInductionApplications",
)
_VAMPIRE_INTEGER_INDUCTION_KEYS = (
    "IntegerInfiniteIntervalInduction",
    "IntegerFiniteIntervalInduction",
)
_VAMPIRE_INDUCTION_KEYS = _VAMPIRE_STRUCT_INDUCTION_KEYS + _VAMPIRE_INTEGER_INDUCTION_KEYS
_VAMPIRE_SUPERPOSITION_KEYS = (
    "Forward superposition",
    "Backward superposition",
)
_INDUCTION_FOCUS_MAX = 8
_INDUCTION_FORMULA_STORE_MAX = 32
_INDUCTION_SCHEMA_MAX = 2
_INDUCTION_SCHEMA_CHARS = 180
_INDUCTION_OBLIGATION_MAX = 6
_INDUCTION_KIND_TAG_RE = re.compile(
    r"\[((?:structural|integer|generalized)[^\]]*)\]\s*$",
    re.I,
)
_INDUCTION_BINDER_RE = re.compile(
    r"!\s*\[\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*'?"
    r"([A-Za-z_][A-Za-z0-9_]*)(?:\(\))?'?\s*\]"
)
_INDUCTION_GENERATE_RE = re.compile(
    r"\[Induction\] generate \d+\.\s*(.+?)\s*"
    r"\[((?:generalized )?induction[^\]]*)\]\s*$",
    re.I,
)


@dataclass
class InductionTrace:
    """Parsed --show_induction trace (focus + formulas + structured schemas)."""
    focus: List[str] = field(default_factory=list)
    formulas: List[str] = field(default_factory=list)
    formula_tags: List[str] = field(default_factory=list)
    schemas: List[dict] = field(default_factory=list)
    obligations: List[str] = field(default_factory=list)


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
    induction_schemas: List[dict] = field(default_factory=list)
    induction_obligations: List[str] = field(default_factory=list)
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
# Prove arms: ``VAMPIRE_RACE_PROFILES`` (paper ``induction_portfolio`` only).
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
    "struct_nui": {
        "kind": "vampire",
        "extra": [
            "--induction", "struct",
            "--induction_gen", "on",
            "--induction_on_complex_terms", "on",
            "--non_unit_induction", "on",
            "--avatar", "off",
        ],
        "diag": "struct_single",
        "label": "structural induction with non-unit clauses",
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


def run_vampire_race(
    smt2_path,
    timeout: int,
    profiles: List[str],
    *,
    collect_stats: bool = False,
    collect_ucore: bool = False,
    show_induction: bool = False,
) -> VampireResult:
    """Race several Vampire profiles (first unsat wins).

    Used by scheme short-prove and by usefulness / node-goal prove (via
    ``run_vampire_routed``). Empty / unknown names fall back to
    ``VAMPIRE_RACE_PROFILES``.
    """
    names = [p for p in profiles if p in VAMPIRE_PROFILES]
    if not names:
        names = list(VAMPIRE_RACE_PROFILES)
    return _run_vampire_parallel(
        smt2_path,
        timeout,
        names,
        collect_stats=collect_stats,
        collect_ucore=collect_ucore,
        show_induction=show_induction,
    )


def vampire_diagnostic_profile(profile: Optional[str]) -> str:
    """Single-strategy name used for 3s sidecar (portfolio names map via spec['diag'])."""
    spec = VAMPIRE_PROFILES.get(profile or "struct_single", VAMPIRE_PROFILES["struct_single"])
    return spec.get("diag") or "struct_single"


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

    diag_name = vampire_diagnostic_profile(profile)
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
    """Prove with the paper Vampire schedule (``induction_portfolio`` only).

    ``state`` is kept for API compatibility / Mate telemetry. Usefulness,
    node-goal prove, and scheme short-prove all use ``VAMPIRE_RACE_PROFILES``
    (a single mixed induction portfolio — original LLM4Ind).
    """
    del state  # routing picks prompts/diagnostics; prove arms are fixed
    return run_vampire_race(
        smt2_path,
        timeout,
        list(VAMPIRE_RACE_PROFILES),
        collect_stats=collect_stats,
        collect_ucore=collect_ucore,
        show_induction=show_induction,
    )


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
    if result.status == "error" and not result.error:
        result.error = extract_vampire_error_message(result.stdout, result.stderr)
    result.stats = parse_vampire_stats(result.stdout + "\n" + result.stderr)
    _apply_induction_trace(
        result, parse_induction_trace_rich(result.stdout + "\n" + result.stderr)
    )
    if collect_ucore and result.proved:
        result.used_lemma_names = parse_ucore_lemma_names(result.stdout)
    return result


def _apply_induction_trace(result: VampireResult, trace: InductionTrace) -> None:
    result.induction_focus = list(trace.focus)
    result.induction_formulas = list(trace.formulas)
    result.induction_schemas = list(trace.schemas)
    result.induction_obligations = list(trace.obligations)


def _richest_vampire(results: List[VampireResult]) -> Optional[VampireResult]:
    if not results:
        return None
    return max(
        results,
        key=lambda r: (
            len(r.stats or {}),
            len(r.induction_schemas or []),
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
            induction_schemas=list(richest.induction_schemas) if richest else [],
            induction_obligations=(
                list(richest.induction_obligations) if richest else []
            ),
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


def _balanced_outer_parens(text: str) -> bool:
    s = (text or "").strip()
    if len(s) < 2 or s[0] != "(" or s[-1] != ")":
        return False
    depth = 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i == len(s) - 1
            if depth < 0:
                return False
    return False


def _split_top_level(expr: str, sep: str) -> Optional[Tuple[str, str]]:
    """Split on the first top-level occurrence of ``sep`` (e.g. ``=>`` or ``&``)."""
    depth = 0
    i = 0
    n = len(expr or "")
    sep_len = len(sep)
    while i < n:
        ch = expr[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif depth == 0 and expr.startswith(sep, i):
            left = expr[:i].strip()
            right = expr[i + sep_len :].strip()
            if left or right:
                return left, right
        i += 1
    return None


def _normalize_induction_sort(sort: str) -> str:
    return (sort or "").strip().strip("'").rstrip("()").strip()


def _strip_induction_tag(text: str) -> Tuple[str, str]:
    """Return (body, tag) for a formula that may still carry a kind tag."""
    s = re.sub(r"\s+", " ", text or "").strip()
    tag_m = _INDUCTION_KIND_TAG_RE.search(s)
    if not tag_m:
        return s, ""
    return s[: tag_m.start()].strip(), tag_m.group(1).strip()


def structure_induction_formula(formula: str, tag: str = "") -> dict:
    """Parse a Vampire induction formula into var/sort/base/step/conclusion."""
    body, found_tag = _strip_induction_tag(formula)
    tag = (tag or found_tag or "").strip()
    low = tag.lower()
    kind = "unknown"
    if "structural" in low:
        kind = "structural"
    elif "integer" in low:
        kind = "integer"
    elif "generalized" in low:
        kind = "generalized"
    mode = "one" if "(one)" in low else ""

    binders = _INDUCTION_BINDER_RE.findall(body)
    induct_var = binders[0][0] if binders else ""
    induct_sort = _normalize_induction_sort(binders[0][1]) if binders else ""
    if not induct_var:
        m_var = re.search(r"!\s*\[\s*([A-Za-z_][A-Za-z0-9_]*)\s*\]", body)
        if m_var:
            induct_var = m_var.group(1)

    payload = body
    pref = re.match(r"!\s*\[[^\]]+\]\s*:\s*(.*)$", body)
    if pref:
        payload = pref.group(1).strip()

    def _implication_parts(text: str) -> Optional[Tuple[str, str]]:
        split = _split_top_level(text, "=>")
        if split:
            return split
        if _balanced_outer_parens(text):
            return _split_top_level(text[1:-1].strip(), "=>")
        return None

    base = ""
    step = ""
    conclusion = ""
    split_concl = _implication_parts(payload)
    if split_concl:
        ante, conclusion = split_concl
        if _balanced_outer_parens(ante):
            ante = ante[1:-1].strip()
        split_base = _split_top_level(ante, "&")
        if split_base:
            base, step = split_base
            if _balanced_outer_parens(step):
                step = step[1:-1].strip()
        else:
            # Compact schemas often look like (IH => step-concl) with no separate base.
            inner = _implication_parts(ante)
            if inner:
                base, step_rhs = inner
                step = f"{base} => {step_rhs}"
            else:
                base = ante
    else:
        conclusion = payload

    return {
        "kind": kind,
        "mode": mode,
        "induct_var": induct_var,
        "induct_sort": induct_sort,
        "base": compress_induction_formula(base, 120) if base else "",
        "step": compress_induction_formula(step, 140) if step else "",
        "conclusion": compress_induction_formula(conclusion, 120) if conclusion else "",
        "raw": compress_induction_formula(body, _INDUCTION_SCHEMA_CHARS),
        "tag": tag,
    }


def format_induction_schema_summary(schema: dict) -> str:
    """One-line prompt summary of a structured induction schema."""
    bits: List[str] = []
    var = str(schema.get("induct_var") or "").strip()
    sort = str(schema.get("induct_sort") or "").strip()
    kind = str(schema.get("kind") or "").strip()
    if var and sort:
        bits.append(f"on {var}:{sort}")
    elif var:
        bits.append(f"on {var}")
    if kind and kind != "unknown":
        bits.append(kind)
    head = f"[{', '.join(bits)}] " if bits else ""
    step = str(schema.get("step") or "").strip()
    if step:
        return head + f"step {step}"
    concl = str(schema.get("conclusion") or "").strip()
    if concl:
        return head + f"concl {concl}"
    return head + str(schema.get("raw") or "").strip()



def parse_induction_trace_rich(text: str) -> InductionTrace:
    """Parse --show_induction into focus, formulas, structured schemas, obligations."""
    focus_raw: List[str] = []
    formula_bodies: List[str] = []
    formula_tags: List[str] = []
    obligations_raw: List[str] = []
    pending: Optional[List[str]] = None

    def _flush_pending(tag: str = "") -> None:
        nonlocal pending
        if pending is None:
            return
        body = " ".join(part for part in pending if part).strip()
        pending = None
        if body:
            formula_bodies.append(body)
            formula_tags.append(tag)

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if pending is not None:
            if line.startswith("[Induction]"):
                _flush_pending("")
            else:
                tag_m = _INDUCTION_KIND_TAG_RE.search(line)
                if tag_m:
                    pending.append(line[: tag_m.start()].strip())
                    _flush_pending(tag_m.group(1).strip())
                else:
                    pending.append(line)
                continue

        if not line.startswith("[Induction]"):
            continue

        m_proc = re.search(r"\[Induction\] process (.+?) in \d+\.", line)
        if m_proc:
            focus_raw.append(m_proc.group(1).strip())
            continue

        m_form = re.match(r"\[Induction\] formula \d+\.\s*(.*)$", line)
        if m_form:
            rest = m_form.group(1).strip()
            if not rest:
                pending = []
                continue
            tag_m = _INDUCTION_KIND_TAG_RE.search(rest)
            if tag_m:
                formula_bodies.append(rest[: tag_m.start()].strip())
                formula_tags.append(tag_m.group(1).strip())
            else:
                formula_bodies.append(rest)
                formula_tags.append("")
            continue

        m_gen = _INDUCTION_GENERATE_RE.match(line)
        if m_gen:
            obligations_raw.append(m_gen.group(1).strip())

    _flush_pending("")

    seen_forms = set()
    dedup_bodies: List[str] = []
    dedup_tags: List[str] = []
    for body, tag in zip(formula_bodies, formula_tags):
        key = re.sub(r"\s+", " ", body).strip()
        if not key or key in seen_forms:
            continue
        # Skip the old broken-parser artifact / empty bang-only bodies.
        if key in ("!", "!!"):
            continue
        seen_forms.add(key)
        dedup_bodies.append(key)
        dedup_tags.append(tag)

    focus_all = _dedup_preserve(focus_raw)
    diseq = [lit for lit in focus_all if "!=" in lit or "≠" in lit]
    diseq.sort(key=lambda lit: (-lit.count("("), -len(lit)))
    rest = [lit for lit in focus_all if lit not in diseq]
    focus = (diseq + rest)[:_INDUCTION_FOCUS_MAX]

    structured = []
    for body, tag in zip(dedup_bodies, dedup_tags):
        rec = structure_induction_formula(body, tag)
        rec["_body"] = body
        structured.append(rec)
    ranked_schemas = select_induction_schema_records(
        structured,
        focus,
        limit=_INDUCTION_FORMULA_STORE_MAX,
    )
    formulas: List[str] = []
    tags: List[str] = []
    schemas: List[dict] = []
    for schema in ranked_schemas:
        body = str(schema.pop("_body", "") or "")
        formulas.append(body or str(schema.get("raw") or ""))
        tags.append(str(schema.get("tag") or ""))
        schemas.append(schema)

    return InductionTrace(
        focus=focus,
        formulas=formulas,
        formula_tags=tags,
        schemas=schemas,
        obligations=_select_induction_obligations(obligations_raw, focus),
    )


def parse_induction_trace(text: str) -> Tuple[List[str], List[str]]:
    """Backward-compatible: return (focus, formula bodies) from --show_induction."""
    trace = parse_induction_trace_rich(text)
    return trace.focus, trace.formulas


def _select_induction_obligations(
    obligations: List[str],
    focus: Optional[List[str]] = None,
    *,
    limit: int = _INDUCTION_OBLIGATION_MAX,
) -> List[str]:
    """Keep a few generate-clause obligations; prefer focus overlap / constructors."""
    cleaned = _dedup_preserve(
        [re.sub(r"\s+", " ", item).strip() for item in (obligations or []) if item]
    )
    if not cleaned:
        return []
    focus_blob = " ".join(focus or []).lower()
    tokens = {
        tok for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]*", focus_blob)
        if len(tok) > 1
    }

    def rank(text: str) -> Tuple[int, int, int]:
        low = text.lower()
        overlap = sum(1 for tok in tokens if tok.lower() in low)
        has_ctor = 1 if re.search(r"\bs\s*\(|\bcons\s*\(|\bsucc\s*\(", low) else 0
        has_diseq = 1 if "!=" in text else 0
        return (overlap, has_ctor + has_diseq, -len(text))

    cleaned.sort(key=rank, reverse=True)
    return cleaned[:limit]


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
    # Vampire prints "User error: ...", which lowercases to "user error:"
    # and does *not* contain the substring "user:".
    if "user error" in text:
        return "error"
    if re.search(r"(?m)^error:", text) or "szs status error" in text:
        return "error"
    if "timeout" in text or "time limit" in text:
        return "timeout"
    return "unknown"


def extract_vampire_error_message(stdout: str, stderr: str) -> Optional[str]:
    """Human-readable Vampire failure text for soft-reject / telemetry reasons.

    Prefer ``User error:`` blocks (parse/type); fall back to ``Error:`` / SZS.
    Not used for sat/unsat classification — that is ``classify_status``.
    """
    text = (stdout or "") + "\n" + (stderr or "")
    m = re.search(
        r"(?is)User error:\s*(.*?)(?=\nUser error:|\n% |\Z)",
        text,
    )
    if m:
        body = re.sub(r"\s+", " ", m.group(0)).strip()
        return body[:500] if body else None
    m = re.search(r"(?im)^Error:\s*.+$", text)
    if m:
        return m.group(0).strip()[:500]
    if re.search(r"(?i)szs status error", text):
        return "SZS status Error"
    return None


def _vampire_stat_rate(
    stats: Dict[str, int],
    elapsed: float,
    *keys: str,
) -> float:
    total = sum(int(stats.get(k, 0)) for k in keys)
    return activity_rate(total, elapsed)


def _vampire_induction_counts(stats: Dict[str, int]) -> Tuple[int, int, int]:
    """Return (structural-like, integer-interval, total) induction counts."""
    struct_like = sum(int(stats.get(k, 0) or 0) for k in _VAMPIRE_STRUCT_INDUCTION_KEYS)
    int_ind = sum(int(stats.get(k, 0) or 0) for k in _VAMPIRE_INTEGER_INDUCTION_KEYS)
    return struct_like, int_ind, struct_like + int_ind


def compress_induction_formula(formula: str, limit: int = _INDUCTION_SCHEMA_CHARS) -> str:
    """Shorten Vampire TPTP-like induction formulas for LLM prompts."""
    s = re.sub(r"\s+", " ", formula or "").strip()
    s = re.sub(r"'([A-Za-z][A-Za-z0-9_]*)\(\)'", r"\1", s)
    s = re.sub(r"\s*\[(?:structural|integer|generalized)[^\]]*\]\s*$", "", s, flags=re.I)
    if len(s) > limit:
        s = s[: max(0, limit - 3)].rstrip() + "..."
    return s


def select_induction_schema_records(
    schemas: List[dict],
    focus: Optional[List[str]] = None,
    *,
    limit: int = _INDUCTION_SCHEMA_MAX,
) -> List[dict]:
    """Rank structured induction schemas; prefer focus overlap / step shape / kind."""
    cleaned: List[dict] = []
    seen = set()
    for raw in schemas or []:
        if not isinstance(raw, dict):
            continue
        rec = dict(raw)
        key = (
            str(rec.get("induct_var") or ""),
            str(rec.get("induct_sort") or ""),
            str(rec.get("step") or ""),
            str(rec.get("conclusion") or ""),
            str(rec.get("raw") or ""),
        )
        if not any(key) or key in seen:
            continue
        seen.add(key)
        cleaned.append(rec)
    if not cleaned:
        return []

    diseq_focus = [lit for lit in (focus or []) if "!=" in lit or "≠" in lit]
    diseq_focus.sort(key=lambda lit: (-lit.count("("), -len(lit)))
    preferred_focus = diseq_focus[:2] or list(focus or [])
    focus_blob = " ".join(preferred_focus).lower()
    tokens = {
        tok for tok in re.findall(r"[A-Za-z][A-Za-z0-9_]*", focus_blob)
        if len(tok) > 1 and tok.lower() not in {"sk", "x0", "x1", "x2"}
    }

    def rank(rec: dict) -> Tuple[int, int, int, int, int]:
        blob = " ".join(
            str(rec.get(k) or "")
            for k in ("conclusion", "step", "base", "raw", "induct_sort")
        ).lower()
        overlap = sum(1 for tok in tokens if tok.lower() in blob)
        concl = str(rec.get("conclusion") or "").lower()
        concl_overlap = sum(1 for tok in tokens if tok.lower() in concl)
        # Prefer non-trivial conclusions (binary eq / both sides non-zero constant).
        nontrivial = 1
        if concl.startswith("zero =") or concl.startswith("0 ="):
            nontrivial = 0
        has_step = 1 if str(rec.get("step") or "").strip() else 0
        kind = str(rec.get("kind") or "")
        kind_score = 2 if kind == "structural" else (1 if kind == "integer" else 0)
        has_var = 1 if rec.get("induct_var") and rec.get("induct_sort") else 0
        return (
            nontrivial + concl_overlap,
            overlap,
            has_step + has_var,
            kind_score,
            -len(str(rec.get("raw") or "")),
        )

    cleaned.sort(key=rank, reverse=True)
    return cleaned[:limit]


def select_induction_schemas(
    formulas: List[str],
    focus: Optional[List[str]] = None,
    *,
    limit: int = _INDUCTION_SCHEMA_MAX,
) -> List[str]:
    """Pick a few induction formula summaries for prompts (string view)."""
    records = select_induction_schema_records(
        [structure_induction_formula(raw) for raw in formulas or []],
        focus,
        limit=limit,
    )
    return [format_induction_schema_summary(rec) for rec in records if format_induction_schema_summary(rec)]


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
    rewrite_c = dem_c + taut_c
    rewrite_r = dem_r + taut_r
    ind_c = _vampire_stat_rate(c, cand_elapsed, *_VAMPIRE_INDUCTION_KEYS)
    ind_r = _vampire_stat_rate(ref_stats, ref_elapsed, *_VAMPIRE_INDUCTION_KEYS)

    strong = 0
    if is_relative_gain(rewrite_c, rewrite_r):
        score += gain_score(rewrite_c, rewrite_r, 2.5)
        signals.append(f"more_demodulations(+{pct_label(rewrite_c, rewrite_r)}%)")
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

    # Volume-up without product (rewrite family / induction / focus) ≈ explosion.
    gen_c_rate = activity_rate(gen_c, cand_elapsed)
    gen_r_rate = activity_rate(ref_stats.get("Generated clauses", 0), ref_elapsed)
    sup_c = _vampire_stat_rate(c, cand_elapsed, *_VAMPIRE_SUPERPOSITION_KEYS)
    sup_r = _vampire_stat_rate(ref_stats, ref_elapsed, *_VAMPIRE_SUPERPOSITION_KEYS)
    volume_c = max(gen_c_rate, sup_c)
    volume_r = max(gen_r_rate, sup_r)
    productive = any(
        s.startswith("more_demodulations")
        or s.startswith("more_induction")
        or s == "lower_passive_ratio"
        for s in signals
    )
    if log_gain(volume_c, volume_r) >= EXPLOSION_LOG_GAIN and not productive:
        penalty = min(gain_score(volume_c, volume_r, 1.5), 1.5)
        score -= penalty
        signals.append(f"search_explosion(+{pct_label(volume_c, volume_r)}%)")

    # Require two independent channels, or one induction signal.
    if strong < 2 and "more_induction" not in "".join(signals):
        if score > 0:
            score *= 0.35
            signals.append("weak_single_signal")

    if not signals and candidate.status in ("timeout", "incomplete", "unknown"):
        signals.append("no_measurable_progress")

    return score, signals


def derive_repair_hints(result: VampireResult, context: str = "goal") -> List[dict]:
    """
    Turn Vampire failure signals into structured repair hints for the next LLM prompt.

    Keeps induction_stuck (focus/schemas), need_rewrite, need_arithmetic_lemma,
    and need_directed_rewrite. need_induction_lemma, induction_depth_limit, and
    generic timeout are intentionally disabled (commented) as misleading/noisy.
    """
    hints: List[dict] = []
    stats = result.stats

    dem = stats.get("Fw demodulations", 0) + stats.get("Bw demodulations", 0)
    taut = stats.get("Fw demodulations to eq. taut.", 0)
    sup = sum(int(stats.get(k, 0) or 0) for k in _VAMPIRE_SUPERPOSITION_KEYS)
    _struct_like, int_ind, ind = _vampire_induction_counts(stats)
    mix = ind + dem
    arithmetic_dominant = ind > 0 and int_ind / ind >= INTEGER_INDUCTION_SHARE_MIN
    schema_records = list(result.induction_schemas or [])
    if not schema_records and result.induction_formulas:
        schema_records = [
            structure_induction_formula(raw) for raw in result.induction_formulas
        ]
    schema_records = select_induction_schema_records(
        schema_records,
        list(result.induction_focus or []),
        limit=_INDUCTION_SCHEMA_MAX,
    )
    schemas = [format_induction_schema_summary(rec) for rec in schema_records]
    schemas = [s for s in schemas if s]
    obligations = list(result.induction_obligations or [])[:_INDUCTION_OBLIGATION_MAX]
    induct_vars = _dedup_preserve(
        [
            f"{rec.get('induct_var')}:{rec.get('induct_sort')}"
            if rec.get("induct_sort")
            else str(rec.get("induct_var") or "")
            for rec in schema_records
            if rec.get("induct_var")
        ]
    )
    induct_kinds = _dedup_preserve(
        [str(rec.get("kind") or "") for rec in schema_records if rec.get("kind")]
    )

    if result.induction_focus or schemas or obligations:
        hint = {
            "kind": "induction_stuck",
            "context": context,
            "detail": (
                "Vampire attempted induction on these goal-related literals/terms but "
                "could not finish the proof. Prefer lemmas that discharge the inductive "
                "step (often commutativity/associativity or rewrite bridges)."
            ),
            "induction_focus": result.induction_focus[:6],
            "induction_formulas": schemas,
            "induction_schemas": schema_records,
            "induction_vars": induct_vars,
            "induction_kinds": induct_kinds,
            "induction_obligations": obligations,
            # Binary signal: moderate vote so it does not drown mix overshoot.
            "strength": 0.5,
            "suggested_actions": [
                "Generate equational lemmas about constructors appearing in the focus terms",
                "If a recursive function appears on both sides, try a generalized form",
                "Avoid repeating lemmas already marked invalid or useless",
            ],
        }
        if schemas:
            hint["suggested_actions"] = [
                "Prefer a lemma that discharges the inductive step in the schema (RHS after unfolding)",
                "If the schema IH does not match the conclusion, generalize the inductive lemma",
            ] + hint["suggested_actions"][:1]
        if obligations:
            hint["suggested_actions"] = [
                "Target open induction obligations (base/step clauses) listed below",
            ] + hint["suggested_actions"]
        hints.append(hint)

    # Disabled: need_rewrite — demod/induction mix mainly asks for equational
    # lemmas; keep high-difficulty / induction_stuck as the LLM-facing signal.
    # if mix > 0:
    #     rewrite_per_ind = dem / max(ind, 1)
    #     if ind > 0 and rewrite_per_ind < REWRITE_PER_INDUCTION_MAX:
    #         hints.append({
    #             "kind": "need_rewrite",
    #             "priority": 1,
    #             "context": context,
    #             "detail": (
    #                 "Rewriting is scarce relative to induction (demod/induction < 8). "
    #                 "Likely missing equational lemmas that enable rewriting under the IH."
    #             ),
    #             "strength": round(
    #                 gate_overshoot(rewrite_per_ind, REWRITE_PER_INDUCTION_MAX), 4
    #             ),
    #             "suggested_actions": [
    #                 "Propose rewrite-oriented lemmas (distributivity, fold/unfold identities)",
    #                 "Prefer lemmas whose LHS matches a subterm of the proof goal",
    #             ],
    #         })
        # Disabled: need_induction_lemma — same "strengthen/generalize the goal"
        # narrative as CVC need_stronger_lemma.
        # ind_share = ind / mix
        # if ind_share < INDUCTION_SHARE_MAX and not arithmetic_dominant:
        #     hints.append({
        #         "kind": "need_induction_lemma",
        #         "priority": 2,
        #         "context": context,
        #         "detail": (
        #             "Induction (structural and integer-interval) is a small share of "
        #             f"Vampire activity (<{int(INDUCTION_SHARE_MAX * 100)}%). Try a "
        #             "stronger inductive lemma (generalization / strengthen conclusion)."
        #         ),
        #         "strength": round(gate_overshoot(ind_share, INDUCTION_SHARE_MAX), 4),
        #         "suggested_actions": [
        #             "Strengthen or generalize the goal into an inductive lemma",
        #             "Introduce an accumulator / helper-function identity if applicable",
        #         ],
        #     })

    if arithmetic_dominant:
        int_share = int_ind / ind
        hints.append({
            "kind": "need_arithmetic_lemma",
            "context": context,
            "detail": (
                "Integer-interval induction dominates Vampire induction activity. "
                "Prefer arithmetic bridge / monotonicity / recurrence lemmas "
                "rather than ADT constructor facts."
            ),
            "strength": round(
                gate_overshoot(int_share, INTEGER_INDUCTION_SHARE_MIN, higher=True), 4
            ),
            "suggested_actions": [
                "Generate arithmetic bridge or monotonicity lemmas",
                "Strengthen recurrences rather than adding constructor equalities",
            ],
        })

    rewrite_product = dem + taut
    if sup > 0 and sup / max(rewrite_product, 1) >= SUPERPOSITION_PER_REWRITE_MIN:
        ratio = sup / max(rewrite_product, 1)
        hints.append({
            "kind": "need_directed_rewrite",
            "context": context,
            "detail": (
                "Vampire superposition is high relative to productive rewriting "
                "(demodulation / equality tautologies). Equality is combining "
                "without simplifying; prefer LHS-directed rewrite lemmas."
            ),
            "strength": round(
                min(1.0, max(0.0, (ratio / SUPERPOSITION_PER_REWRITE_MIN) - 1.0)),
                4,
            ),
            "suggested_actions": [
                "Propose rewrite lemmas whose LHS matches a goal subterm",
                "Avoid overly general quantified equalities that explode superposition",
            ],
        })

    # Disabled: induction_depth_limit — depth signal can later drive scheduling
    # (stop deepening / invariant), but prompt text again says strengthen/generalize.
    # depth = int(stats.get("MaxInductionDepth", 0) or 0)
    # if (
    #     depth >= MAX_INDUCTION_DEPTH_HINT
    #     and result.status in ("timeout", "incomplete", "unknown")
    #     and ind > 0
    # ):
    #     hints.append({
    #         "kind": "induction_depth_limit",
    #         "context": context,
    #         "detail": (
    #             f"Vampire repeatedly reached induction depth {depth} without finishing. "
    #             "Strengthen or generalize the inductive lemma rather than searching deeper."
    #         ),
    #         "strength": round(min(1.0, depth / 4.0), 4),
    #         "suggested_actions": [
    #             "Generate a stronger generalized lemma or an auxiliary invariant",
    #             "Introduce an accumulator / helper-function identity if applicable",
    #         ],
    #     })

    # Disabled: generic timeout hint — low information noise.
    # if result.status == "timeout" and not hints:
    #     hints.append({
    #         "kind": "timeout",
    #         "context": context,
    #         "detail": "Vampire timed out without a clear induction/rewrite signal.",
    #         "suggested_actions": [
    #             "Generate simpler lemmas closer to the recursive definitions",
    #             "Split the goal into smaller equational facts",
    #         ],
    #     })

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
        if result.status == "error" and not result.error:
            result.error = extract_vampire_error_message(result.stdout, result.stderr)
        result.stats = parse_vampire_stats(result.stdout + "\n" + result.stderr)
        _apply_induction_trace(
            result, parse_induction_trace_rich(result.stdout + "\n" + result.stderr)
        )
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
