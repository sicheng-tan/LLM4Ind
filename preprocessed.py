"""SMT2 preprocessing: split axioms vs proof goal and emit a single trailing check-sat.

Tip/Isa exports sometimes use a non-SMT-LIB datatype form
``(declare-datatypes ((T 0)) ((T (C ...) ...)))``. That is rewritten to
``(declare-datatypes ((T 0)) (((C ...) ...)))`` so cvc5 can parse the file.
"""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import List, Optional, Tuple


_TIP_DATATYPE = re.compile(
    r"(\(declare-datatypes\s*\(\s*\(\s*(\w+)\s+\d+\s*\)\s*\)\s*)"
    r"\(\s*\(\s*\2\b\s+",
    re.DOTALL,
)


def normalize_tip_datatype(cmd: str) -> str:
    """Rewrite Tip-style ``((Name ctors...))`` to SMT-LIB ``(((ctors...)))``."""
    match = _TIP_DATATYPE.match(cmd)
    if not match:
        return cmd
    # Consumed Tip ``((Name ``; emit SMT-LIB constructor-list opens ``((``.
    return f"{match.group(1)}(({cmd[match.end():]}"


def _paren_delta(text: str) -> int:
    return text.count("(") - text.count(")")


def _strip_line_comment(line: str) -> Tuple[str, str]:
    """Return (code_without_comment, code_to_store). Comments are dropped."""
    if ";" not in line:
        return line, line
    code = line.split(";", 1)[0].rstrip()
    return code, code


def process_smt_file(input_path: Path, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)

    # Keep a copy of the (possibly syntax-fixed) source next to the template.
    raw = input_path.read_text(encoding="utf-8")
    fixed_source = normalize_tip_datatypes_in_text(raw)
    (output_dir / input_path.name).write_text(fixed_source, encoding="utf-8")

    lines = [line.rstrip("\n") for line in fixed_source.splitlines()]

    sections = {
        "set_logic": [],
        "sorts": [],
        "datatypes": [],
        "functions": [],
        "proof_goal": [],
        "check_exit": [],
    }

    current_block: Optional[str] = None
    paren_stack = 0
    proof_goal_lines: List[str] = []
    potential_proof_goal = False
    assert_paren_count = 0

    def _close_if_balanced() -> None:
        nonlocal current_block, paren_stack
        if current_block is not None and paren_stack <= 0:
            current_block = None
            paren_stack = 0

    def _start_block(name: str, stripped: str, original_line: str) -> None:
        nonlocal current_block, paren_stack
        current_block = name
        paren_stack = _paren_delta(stripped)
        sections[name].append(original_line)
        _close_if_balanced()

    for line in lines:
        stripped_raw, original_line = _strip_line_comment(line)
        stripped = stripped_raw.strip()
        if not stripped:
            continue

        # Trailing solver commands always win over an open block whose parens
        # already balanced (the historical bug left current_block='functions'
        # after a one-line assert, so check-sat was swallowed into axioms).
        if stripped.startswith(("(check-sat", "(exit")):
            sections["check_exit"].append(original_line)
            current_block = None
            paren_stack = 0
            potential_proof_goal = False
            proof_goal_lines = []
            continue

        if stripped.startswith("(set-logic"):
            sections["set_logic"].append(original_line)
            continue

        if stripped.startswith("(declare-sort"):
            _start_block("sorts", stripped, original_line)
            continue

        if stripped.startswith("(declare-datatypes"):
            _start_block("datatypes", stripped, original_line)
            continue

        if stripped.startswith(
            ("(declare-fun", "(declare-const", "(define-fun", "(assert (")
        ) and not stripped.startswith("(assert (not") and not potential_proof_goal:
            _start_block("functions", stripped, original_line)
            continue

        if stripped.startswith("(assert (not"):
            current_block = "proof_goal"
            proof_goal_lines = [original_line]
            paren_stack = _paren_delta(stripped)
            potential_proof_goal = False
            if paren_stack == 0:
                sections["proof_goal"].append(
                    " ".join(line.strip() for line in proof_goal_lines)
                )
                proof_goal_lines = []
                current_block = None
            continue

        if stripped.startswith("(assert") and not stripped.startswith("(assert ("):
            potential_proof_goal = True
            proof_goal_lines = [original_line]
            assert_paren_count = _paren_delta(stripped)
            continue

        if potential_proof_goal and stripped.startswith("(not"):
            current_block = "proof_goal"
            proof_goal_lines.append(original_line)
            paren_stack = assert_paren_count + _paren_delta(stripped)
            potential_proof_goal = False
            if paren_stack == 0:
                sections["proof_goal"].append(
                    " ".join(line.strip() for line in proof_goal_lines)
                )
                proof_goal_lines = []
                current_block = None
            continue

        if potential_proof_goal and not stripped.startswith("(not"):
            current_block = "functions"
            paren_stack = assert_paren_count
            sections["functions"].extend(proof_goal_lines)
            sections["functions"].append(original_line)
            paren_stack += _paren_delta(stripped)
            potential_proof_goal = False
            proof_goal_lines = []
            _close_if_balanced()
            continue

        if current_block == "proof_goal":
            proof_goal_lines.append(original_line)
            paren_stack += _paren_delta(stripped)
            if paren_stack <= 0:
                sections["proof_goal"].append(
                    " ".join(line.strip() for line in proof_goal_lines)
                )
                proof_goal_lines = []
                current_block = None
            continue

        if current_block in ("datatypes", "functions", "sorts"):
            sections[current_block].append(original_line)
            paren_stack += _paren_delta(stripped)
            _close_if_balanced()
            continue

        # Unclassified top-level command: keep with function/axiom block.
        sections["functions"].append(original_line)

    if potential_proof_goal and proof_goal_lines:
        sections["functions"].extend(proof_goal_lines)

    # Never leave solver queries inside axiom text.
    cleaned_functions: List[str] = []
    for item in sections["functions"]:
        item_stripped = item.strip()
        if item_stripped.startswith("(check-sat") or item_stripped.startswith("(exit"):
            sections["check_exit"].append(item)
        else:
            cleaned_functions.append(item)
    sections["functions"] = cleaned_functions

    template_path = output_dir / "template.smt2"
    with open(template_path, "w", encoding="utf-8") as f:
        if sections["set_logic"]:
            f.write(sections["set_logic"][0] + "\n\n")

        if sections["sorts"]:
            f.write("\n".join(sections["sorts"]) + "\n\n")

        if sections["datatypes"]:
            f.write("; datatypes\n")
            f.write("\n".join(sections["datatypes"]) + "\n")
            f.write("; datatypes end\n\n")

        if sections["functions"]:
            f.write("; functions declarations\n")
            f.write("\n".join(sections["functions"]) + "\n")
            f.write("; functions declarations end\n\n")

        if sections["proof_goal"]:
            f.write("; proof goal\n")
            for goal in sections["proof_goal"]:
                f.write(goal + "\n")
            f.write("; proof goal end\n\n")

        # Exactly one check-sat, always after the negated goal.
        f.write("(check-sat)\n")
        if any(item.strip().startswith("(exit") for item in sections["check_exit"]):
            f.write("(exit)\n")

    return template_path


def normalize_tip_datatypes_in_text(text: str) -> str:
    """Normalize every top-level Tip-style declare-datatypes command in *text*."""
    out: List[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("(declare-datatypes", i):
            start = i
            depth = 0
            j = i
            while j < n:
                ch = text[j]
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
            cmd = text[start:j]
            out.append(normalize_tip_datatype(cmd))
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def process_directory(source_dir: Path, target_root: Path) -> None:
    for root, _, files in os.walk(source_dir):
        for file in files:
            if not file.endswith(".smt2"):
                continue
            input_path = Path(root) / file
            relative_path = input_path.relative_to(source_dir).parent
            output_dir = target_root / relative_path / file[:-5]
            process_smt_file(input_path, output_dir)


if __name__ == "__main__":
    process_directory(
        Path("benchmarks/smtlib2/autoproof"),
        Path("benchmarks/preprocessed/autoproof"),
    )
