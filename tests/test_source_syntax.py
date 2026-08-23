#!/usr/bin/env python3
"""Regression test that compiles every Python source file in the repository."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def python_sources() -> list[Path]:
    return sorted(
        path
        for path in ROOT.rglob("*.py")
        if ".git" not in path.parts and "__pycache__" not in path.parts
    )


def test_all_python_sources_compile() -> None:
    errors = []
    for path in python_sources():
        try:
            compile(path.read_text(encoding="utf-8"), str(path), "exec")
        except SyntaxError as exc:
            errors.append(f"{path}: {exc.__class__.__name__}: {exc}")
    assert not errors, "Python syntax errors found:\n" + "\n".join(errors)


def main() -> int:
    test_all_python_sources_compile()
    print(f"syntax compile passed: {len(python_sources())} Python files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
