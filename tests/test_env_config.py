#!/usr/bin/env python3
"""Experiment env loading: custom API base / model, DOTENV_PATH."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from env_config import setup_environment


def test_dotenv_path_sets_openai_endpoint(tmp_path, monkeypatch) -> None:
    env_file = tmp_path / "case.env"
    env_file.write_text(
        "\n".join(
            [
                "OPENAI_API_KEY=test-key",
                "OPENAI_API_BASE=https://example.test/v1",
                "OPENAI_MODEL=gpt-5.5",
                "MODEL_TYPE=gpt-5.5",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    for name in (
        "OPENAI_API_KEY",
        "OPENAI_API_BASE",
        "OPENAI_MODEL",
        "MODEL_TYPE",
        "DOTENV_PATH",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("DOTENV_PATH", str(env_file))

    config = setup_environment()
    assert config["OPENAI_API_KEY"] == "test-key"
    assert config["OPENAI_API_BASE"] == "https://example.test/v1"
    assert config["OPENAI_MODEL"] == "gpt-5.5"
    assert config["MODEL_TYPE"] == "gpt-5.5"
