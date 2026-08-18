"""
CVC5/CVC4 runner with rich feedback for solver-guided lemma repair.

Design notes vs Vampire:
- Main prove path: multi-strategy portfolio (unchanged behaviour).
- Diagnostic path: single cvc5 inductive strategy + --stats (comparable runs).
- Difficulty path: SMT-LIB produce-difficulty / get-difficulty (cvc5-specific).
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
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

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


# Keys we extract from --stats for progress scoring.
STAT_KEY_PATTERNS = [
    (r"QUANTIFIERS_INST_E_MATCHING(?:_SIMPLE)?\s*:\s*(\d+)", "INST_E_MATCHING"),
    (r"QUANTIFIERS_INST_E_MATCHING_SIMPLE\s*:\s*(\d+)", "INST_E_MATCHING_SIMPLE"),
    (r"QUANTIFIERS_INST_CBQI_PROP\s*:\s*(\d+)", "INST_CBQI_PROP"),
    (r"QUANTIFIERS_INST_CBQI_CONFLICT\s*:\s*(\d+)", "INST_CBQI_CONFLICT"),
    (r"QUANTIFIERS_SKOLEMIZE\s*:\s*(\d+)", "SKOLEMIZE"),
    (r"QUANTIFIERS_CONJ_GEN_GT_ENUM\s*:\s*(\d+)", "CONJ_GEN_GT_ENUM"),
    (r"QUANTIFIERS_CONJ_GEN_SPLIT\s*:\s*(\d+)", "CONJ_GEN_SPLIT"),
    (r"DATATYPES_INST\s*:\s*(\d+)", "DATATYPES_INST"),
    (r"DATATYPES_SPLIT\s*:\s*(\d+)", "DATATYPES_SPLIT"),
    (r"DATATYPES_UNIF\s*:\s*(\d+)", "DATATYPES_UNIF"),
    (r"global::totalTime\s*=\s*(\d+)ms", "TOTAL_TIME_MS"),
]


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

    def to_dict(self) -> dict:
        return asdict(self)


def run_cvc_solver_with_timeout(smt2_path, timeout=60) -> bool:
    """Backward-compatible boolean wrapper (True iff unsat)."""
    return run_cvc(smt2_path, timeout=timeout).proved


def run_cvc(smt2_path, timeout: int = 60, *, collect_stats: bool = False) -> CvcResult:
    """
    Portfolio prove: several CVC5/CVC4 strategies in parallel.
    First unsat wins. Stats are only collected on the winning strategy if requested
    (re-run diagnostic separately for comparable progress scores).
    """
    smt2_path = Path(smt2_path)
    cvc5 = _cvc5_binary()
    cvc4 = _cvc4_binary()

    strategies = {
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
    }

    processes = {}
    start = time.time()
    try:
        for name, cfg in strategies.items():
            cmd = [cfg["binary"]] + cfg["options"] + [str(smt2_path)]
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
            except Exception as e:
                logging.error("Failed to start %s: %s", name, e)

        if not processes:
            return CvcResult(status="error", error="no solver process started")

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
                    continue

                text = (stdout or "") + "\n" + (stderr or "")
                if _stdout_is_unsat(stdout or ""):
                        _cleanup_processes(processes, exclude=name)
                        elapsed = time.time() - start
                        logging.info(
                            "%s验证成功: unsat (策略: %s, %.2fs)",
                            strategies[name]["type"], name, elapsed,
                        )
                        result = CvcResult(
                            proved=True,
                            status="unsat",
                            elapsed=elapsed,
                            strategy=name,
                            stdout=stdout or "",
                            stderr=stderr or "",
                        )
                        if collect_stats:
                            result.stats = parse_cvc_stats(text)
                        return result

            if len(completed) == len(processes):
                break
            time.sleep(0.05)

        elapsed = time.time() - start
        logging.warning("CVC5/CVC4验证超时或失败 (耗时: %.2f秒)", elapsed)
        return CvcResult(proved=False, status="timeout", elapsed=elapsed)

    finally:
        _cleanup_processes(processes)


def run_cvc_diagnostic(
    smt2_path,
    timeout: int = 3,
    *,
    collect_difficulty: bool = True,
) -> CvcResult:
    """
    Single-strategy inductive cvc5 run with --stats (+ optional difficulty).
    Used for progress comparison / repair hints, not as portfolio prover.
    """
    smt2_path = Path(smt2_path)
    binary = _cvc5_binary()
    ms = max(1, int(timeout * 1000))
    cmd = [
        binary,
        "--lang=smt2",
        "--full-saturate-quant",
        "--quant-ind",
        "--conjecture-gen",
        f"--tlimit-per={ms}",
        "--stats",
        str(smt2_path),
    ]
    result = _execute_single(cmd, timeout + 2, strategy="cvc5_inductive_diag")
    if collect_difficulty and not result.proved:
        # Difficulty is most useful on failures; also fine on success.
        diff = run_cvc_difficulty(smt2_path, timeout=min(timeout, 3))
        result.difficulty = diff.difficulty
        if diff.status == "unsat":
            # Difficulty run may prove with same budget; keep diagnostic status authoritative
            pass
    elif collect_difficulty and result.proved:
        diff = run_cvc_difficulty(smt2_path, timeout=min(timeout, 3))
        result.difficulty = diff.difficulty
    return result


def run_cvc_difficulty(smt2_path, timeout: int = 3) -> CvcResult:
    """
    Run cvc5 on a rewritten SMT script that enables produce-difficulty and
    calls (get-difficulty) after check-sat.
    """
    smt2_path = Path(smt2_path)
    binary = _cvc5_binary()
    content = smt2_path.read_text(encoding="utf-8")
    script = _inject_difficulty_script(content)
    ms = max(1, int(timeout * 1000))

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(script)
        tmp_path = tf.name

    try:
        cmd = [
            binary,
            "--lang=smt2",
            "--full-saturate-quant",
            "--quant-ind",
            "--conjecture-gen",
            f"--tlimit-per={ms}",
            tmp_path,
        ]
        result = _execute_single(cmd, timeout + 2, strategy="cvc5_difficulty")
        result.difficulty = parse_cvc_difficulty(result.stdout)
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


def parse_cvc_difficulty(text: str) -> List[Tuple[str, int]]:
    """
    Parse (get-difficulty) output:
      (
      ((forall ...) 10)
      ((not (forall ...)) 1)
      )
    """
    items: List[Tuple[str, int]] = []
    # Find the first s-expression block after unsat/sat that looks like difficulty
    # Each entry: ( <term> <int> )
    for m in re.finditer(
        r"\(\s*(\((?:[^()]|\([^()]*\))*\))\s+(\d+)\s*\)",
        text,
        flags=re.DOTALL,
    ):
        term = re.sub(r"\s+", " ", m.group(1).strip())
        score = int(m.group(2))
        # Skip empty / nonsense
        if term.startswith("(") and score >= 0:
            items.append((term, score))

    # Prefer assertions (forall / not / named) with positive difficulty
    items = [(t, s) for t, s in items if s > 0]
    items.sort(key=lambda x: -x[1])
    # Dedup by term
    seen = set()
    out = []
    for t, s in items:
        if t not in seen:
            seen.add(t)
            out.append((t, s))
    return out[:12]


def compute_progress_score(
    baseline: CvcResult,
    candidate: CvcResult,
    *,
    control: Optional[CvcResult] = None,
) -> Tuple[float, List[str]]:
    """
    Score whether lemmas made cvc5 less stuck, using stats deltas.
    If control is provided, only credit gains beyond the control run.
    """
    if candidate.proved:
        return 100.0, ["proved_goal"]
    if candidate.status == "error":
        return -10.0, ["solver_error"]

    b, c = baseline.stats, candidate.stats
    ctrl = control.stats if control is not None else {}
    signals: List[str] = []
    score = 0.0

    def over_control(key: str) -> int:
        if control is None:
            return int(c.get(key, 0)) - int(b.get(key, 0))
        return int(c.get(key, 0)) - int(ctrl.get(key, 0))

    conj = over_control("CONJ_TOTAL")
    inst = over_control("INST_TOTAL")
    skol = over_control("QUANTIFIERS_SKOLEMIZE")
    dt = over_control("DT_TOTAL")
    strong = 0

    # More productive conjecture-gen beyond control ≈ theory exploration progress
    if conj > 20:
        score += min(conj / 80.0, 2.5)
        signals.append(f"more_conjecture_gen(+{conj})")
        strong += 1
    if skol > 0:
        score += min(skol, 2.0)
        signals.append(f"more_skolemize(+{skol})")
        strong += 1
    if inst > 50:
        score += min(inst / 200.0, 2.0)
        signals.append(f"more_instantiations(+{inst})")
        strong += 1
    if dt > 10:
        score += min(dt / 40.0, 1.5)
        signals.append(f"more_datatype_inference(+{dt})")
        strong += 1

    # Difficulty: if goal assertion difficulty drops, that is progress
    def goal_diff(res: CvcResult) -> Optional[int]:
        for term, s in res.difficulty:
            if "(not" in term and "forall" in term:
                return s
        return None

    gb, gc = goal_diff(baseline), goal_diff(candidate)
    if gb is not None and gc is not None and gc < gb:
        score += 1.5
        signals.append(f"goal_difficulty_drop({gb}->{gc})")
        strong += 1

    # High-difficulty recursive axioms that drop after adding lemmas
    if baseline.difficulty and candidate.difficulty:
        b_map = {t: s for t, s in baseline.difficulty}
        dropped = 0
        for t, s in candidate.difficulty:
            if t in b_map and s + 2 < b_map[t]:
                dropped += 1
        if dropped >= 1:
            score += min(dropped * 0.75, 2.0)
            signals.append(f"axiom_difficulty_drop(x{dropped})")
            strong += 1

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

    hard_axioms = [
        t for t, s in result.difficulty
        if s >= 3 and "forall" in t and "(not" not in t
    ][:4]
    goal_bits = [t for t, s in result.difficulty if "(not" in t][:2]

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

    if conj >= 50 and skol <= 2:
        hints.append({
            "kind": "need_stronger_lemma",
            "context": context,
            "detail": (
                "cvc5 conjecture-gen was active but skolem/induction strengthening "
                "stayed low. Likely missing a stronger inductive lemma (generalization)."
            ),
            "suggested_actions": [
                "Strengthen or generalize the goal into an inductive lemma",
                "Try associativity/commutativity/distributivity style facts",
            ],
        })
    elif skol >= 3 and inst < 30:
        hints.append({
            "kind": "need_rewrite",
            "context": context,
            "detail": (
                "cvc5 skolemized (induction-like) but instantiations stayed sparse. "
                "Missing rewrite-oriented lemmas may be blocking matching."
            ),
            "suggested_actions": [
                "Propose rewrite lemmas whose LHS matches a subterm of the goal",
                "Unfold recursive definitions one step in a lemma",
            ],
        })
    elif result.status in ("timeout", "unknown") and not hints:
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
            stdout, stderr = proc.communicate(timeout=timeout)
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
