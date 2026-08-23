#!/usr/bin/env python3
"""Smoke-test imports of both Mate entry modules without calling an LLM."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_mate_modules_import() -> None:
    env = os.environ.copy()
    env.update({
        "OPENAI_API_KEY": "unit-test-placeholder",
        "MODEL_TYPE": "gpt-4o",
    })
    proc = subprocess.run(
        [
            sys.executable,
            "-c",
            "import Mate_new; import Mate_new_vampire; print('mate imports ok')",
        ],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0, (
        "Mate module import failed:\n"
        f"stdout={proc.stdout}\n"
        f"stderr={proc.stderr}"
    )
    assert "mate imports ok" in proc.stdout


def main() -> int:
    test_mate_modules_import()
    print("Mate module imports passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
