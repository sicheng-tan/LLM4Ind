import subprocess
import logging
import time
import os
import re
import signal
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

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
    stats: Dict[str, int] = field(default_factory=dict)
    induction_focus: List[str] = field(default_factory=list)
    induction_formulas: List[str] = field(default_factory=list)
    used_lemma_names: List[str] = field(default_factory=list)
    stdout: str = ""
    stderr: str = ""
    error: Optional[str] = None

    def to_dict(self) -> dict:
        return asdict(self)


def run_vampire_with_timeout(smt2_path, timeout=60) -> bool:
    """Backward-compatible boolean wrapper (True iff unsat)."""
    return run_vampire(smt2_path, timeout=timeout).proved


def run_vampire(
    smt2_path,
    timeout: int = 60,
    *,
    collect_stats: bool = True,
    collect_ucore: bool = False,
    proof_file: Optional[Path] = None,
) -> VampireResult:
    """
    Portfolio induction run used for proving.
    Optionally collect statistics and/or SMT-LIB unsat cores (named lemmas).
    """
    vampire_binary = _vampire_binary()
    if not vampire_binary:
        return VampireResult(status="error", error="VAMPIRE_BINARY not configured")

    smt2_path = Path(smt2_path)
    command = [
        vampire_binary,
        "-t", f"{timeout}s",
        "--mode", "portfolio",
        "--schedule", "induction",
        "--input_syntax", "smtlib2",
    ]

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
            # Replace proof off with proof on + file sink
            command = [c for c in command if c not in ("--proof", "off")]
            command.extend([
                "--proof", "on",
                "--print_proofs_to_file", str(proof_file),
            ])

    command.append(str(smt2_path))
    return _execute_vampire(command, timeout, collect_ucore=collect_ucore)


def run_vampire_diagnostic(
    smt2_path,
    timeout: int = 3,
    *,
    show_induction: bool = True,
) -> VampireResult:
    """
    Single-strategy diagnostic run for progress comparison and induction traces.
    Not used as the main prover; portfolio remains authoritative for proved=True.
    """
    vampire_binary = _vampire_binary()
    if not vampire_binary:
        return VampireResult(status="error", error="VAMPIRE_BINARY not configured")

    smt2_path = Path(smt2_path)
    command = [
        vampire_binary,
        "-t", f"{timeout}s",
        "--mode", "vampire",
        "--input_syntax", "smtlib2",
        "--output_mode", "vampire",
        "--statistics", "full",
        "--proof", "off",
        "--induction", "struct",
        "--induction_gen", "on",
        "--induction_on_complex_terms", "on",
        "--avatar", "off",
    ]
    if show_induction:
        command.extend(["--show_induction", "on"])
    command.append(str(smt2_path))
    return _execute_vampire(command, timeout, collect_ucore=False)


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


def compute_progress_score(
    baseline: VampireResult,
    candidate: VampireResult,
    *,
    control: Optional[VampireResult] = None,
) -> Tuple[float, List[str]]:
    """
    Score whether adding lemmas made Vampire 'less stuck'.
    Returns (score, human-readable signals). Higher is better; >0 means progress.

    If `control` is provided (e.g. baseline+trivial assert true), only credit
    signals that exceed the control run — filters out spurious clause inflation.
    """
    if candidate.proved:
        return 100.0, ["proved_goal"]
    if candidate.status == "error":
        return -10.0, ["solver_error"]

    signals: List[str] = []
    score = 0.0
    b, c = baseline.stats, candidate.stats
    ctrl = control.stats if control is not None else {}

    def delta(key: str) -> int:
        return int(c.get(key, 0)) - int(b.get(key, 0))

    def delta_over_control(key: str) -> int:
        """Extra gain of candidate vs control, relative to the same baseline."""
        if control is None:
            return delta(key)
        return int(c.get(key, 0)) - int(ctrl.get(key, 0))

    # Rewrite / demodulation growth beyond control ≈ real equational progress.
    dem_delta = delta_over_control("Fw demodulations") + delta_over_control("Bw demodulations")
    taut_delta = delta_over_control("Fw demodulations to eq. taut.")
    ind_delta = (
        delta_over_control("InductionApplications")
        + delta_over_control("GeneralizedInductionApplications")
        + delta_over_control("StructuralInduction")
    )

    strong = 0
    if dem_delta > 100:
        score += min(dem_delta / 250.0, 2.5)
        signals.append(f"more_demodulations(+{dem_delta})")
        strong += 1
    if taut_delta > 8:
        score += 1.25
        signals.append(f"more_eq_taut_demod(+{taut_delta})")
        strong += 1
    if ind_delta > 8:
        score += min(ind_delta / 40.0, 2.0)
        signals.append(f"more_induction_activity(+{ind_delta})")
        strong += 1

    # Fewer leftover passive clauses under similar generation can mean better focus.
    gen_b = b.get("Generated clauses", 0)
    gen_c = c.get("Generated clauses", 0)
    pas_b = b.get("Final passive clauses", 0)
    pas_c = c.get("Final passive clauses", 0)
    if gen_b > 100 and gen_c > 100 and pas_b > 0:
        ratio_b = pas_b / max(gen_b, 1)
        ratio_c = pas_c / max(gen_c, 1)
        # Also require improvement over control passive ratio when available
        better_than_control = True
        if control is not None:
            gen_k = ctrl.get("Generated clauses", 0)
            pas_k = ctrl.get("Final passive clauses", 0)
            if gen_k > 100 and pas_k > 0:
                ratio_k = pas_k / max(gen_k, 1)
                better_than_control = ratio_c + 1e-9 < 0.9 * ratio_k
        if better_than_control and ratio_c + 1e-9 < 0.7 * ratio_b:
            score += 1.0
            signals.append("lower_passive_ratio")
            strong += 1

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
    ind = stats.get("InductionApplications", 0) + stats.get("StructuralInduction", 0)

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

    if ind >= 10 and dem < 100:
        hints.append({
            "kind": "need_rewrite",
            "context": context,
            "detail": (
                "Many induction applications but little demodulation/rewriting progress. "
                "Likely missing equational lemmas that enable rewriting under the IH."
            ),
            "suggested_actions": [
                "Propose rewrite-oriented lemmas (distributivity, fold/unfold identities)",
                "Prefer lemmas whose LHS matches a subterm of the proof goal",
            ],
        })
    elif dem >= 500 and ind < 5:
        hints.append({
            "kind": "need_induction_lemma",
            "context": context,
            "detail": (
                "Plenty of rewriting but little productive induction. "
                "Try a stronger inductive lemma (generalization / strengthen conclusion)."
            ),
            "suggested_actions": [
                "Strengthen or generalize the goal into an inductive lemma",
                "Introduce an accumulator / helper-function identity if applicable",
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
) -> VampireResult:
    result = VampireResult()
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
            stdout, stderr = proc.communicate(timeout=timeout + 5)
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
