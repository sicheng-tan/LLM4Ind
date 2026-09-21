#!/usr/bin/env python3
"""Experiment env loading: custom API base / model, DOTENV_PATH."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from env_config import setup_environment, thinking_api_style, _llm_call_kwargs


def test_dotenv_path_sets_openai_endpoint(tmp_path, monkeypatch) -> None:
    env_file = tmp_path / "case.env"
    env_file.write_text(
        "\n".join(
            [
                "OPENAI_API_KEY=test-key",
                "OPENAI_API_BASE=https://example.test/v1",
                "OPENAI_MODEL=gpt-5.5",
                "MODEL_TYPE=gpt-5.5",
                "LLM_TIMEOUT=30",
                "LLM_MAX_RETRIES=0",
                "ENABLE_THINKING=true",
                "REASONING_EFFORT=low",
                "MAX_TOKENS=8192",
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
        "LLM_TIMEOUT",
        "LLM_MAX_RETRIES",
        "ENABLE_THINKING",
        "REASONING_EFFORT",
        "MAX_TOKENS",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("DOTENV_PATH", str(env_file))

    config = setup_environment()
    assert config["OPENAI_API_KEY"] == "test-key"
    assert config["OPENAI_API_BASE"] == "https://example.test/v1"
    assert config["OPENAI_MODEL"] == "gpt-5.5"
    assert config["MODEL_TYPE"] == "gpt-5.5"
    assert config["LLM_TIMEOUT"] == 30.0
    assert config["LLM_MAX_RETRIES"] == 0
    assert config["ENABLE_THINKING"] is True
    assert config["REASONING_EFFORT"] == "low"
    assert config["MAX_TOKENS"] == 8192


def test_thinking_api_style_detects_vendor() -> None:
    assert thinking_api_style({"MODEL_TYPE": "qwen3", "OPENAI_MODEL": "Qwen/..."}) == "qwen"
    assert thinking_api_style({"MODEL_TYPE": "qwen", "OPENAI_MODEL": ""}) == "qwen"
    assert (
        thinking_api_style(
            {"MODEL_TYPE": "deepseek-v4-flash", "OPENAI_MODEL": "deepseek-v4-flash"}
        )
        == "deepseek_v4"
    )
    assert (
        thinking_api_style(
            {
                "MODEL_TYPE": "deepseek-v4-flash",
                "OPENAI_MODEL": "deepseek-ai/DeepSeek-V4-Flash",
            }
        )
        == "deepseek_v4"
    )
    assert thinking_api_style({"MODEL_TYPE": "deepseek", "OPENAI_MODEL": ""}) == "deepseek_v4"
    assert thinking_api_style({"MODEL_TYPE": "gpt-5.5", "OPENAI_MODEL": "gpt-5.5"}) == "none"


def test_llm_call_kwargs_qwen_vs_deepseek() -> None:
    assert _llm_call_kwargs({}) == {}
    assert _llm_call_kwargs({"ENABLE_THINKING": None, "MAX_TOKENS": None}) == {}

    # Non-thinking providers: ignore ENABLE_THINKING / REASONING_EFFORT wire fields.
    plain = _llm_call_kwargs(
        {
            "MODEL_TYPE": "gpt-5.5",
            "OPENAI_MODEL": "gpt-5.5",
            "ENABLE_THINKING": True,
            "REASONING_EFFORT": "low",
            "MAX_TOKENS": 8192,
        }
    )
    assert plain == {"max_tokens": 8192}

    # Qwen: only enable_thinking; effort is not sent.
    qwen_off = _llm_call_kwargs(
        {
            "MODEL_TYPE": "qwen3",
            "OPENAI_MODEL": "Qwen/Qwen3-235B-A22B-Instruct-2507",
            "ENABLE_THINKING": False,
            "REASONING_EFFORT": "low",
            "MAX_TOKENS": 8192,
        }
    )
    assert qwen_off["max_tokens"] == 8192
    assert qwen_off["extra_body"] == {"enable_thinking": False}

    qwen_on = _llm_call_kwargs(
        {
            "MODEL_TYPE": "qwen",
            "OPENAI_MODEL": "",
            "ENABLE_THINKING": True,
            "REASONING_EFFORT": "high",
        }
    )
    assert qwen_on["extra_body"] == {"enable_thinking": True}

    # DeepSeek V4: thinking.type + reasoning_effort; no enable_thinking.
    # Default (unset) is explicitly disabled — provider default would be high on.
    ds_default = _llm_call_kwargs(
        {
            "MODEL_TYPE": "deepseek-v4-flash",
            "OPENAI_MODEL": "deepseek-v4-flash",
        }
    )
    assert ds_default["extra_body"] == {"thinking": {"type": "disabled"}}

    ds_off = _llm_call_kwargs(
        {
            "MODEL_TYPE": "deepseek-v4-flash",
            "OPENAI_MODEL": "deepseek-v4-flash",
            "ENABLE_THINKING": False,
            "MAX_TOKENS": 16384,
        }
    )
    assert ds_off["extra_body"] == {"thinking": {"type": "disabled"}}
    assert ds_off["max_tokens"] == 16384

    ds_low = _llm_call_kwargs(
        {
            "MODEL_TYPE": "deepseek-v4-flash",
            "OPENAI_MODEL": "deepseek-ai/DeepSeek-V4-Flash",
            "ENABLE_THINKING": True,
            "REASONING_EFFORT": "low",
            "MAX_TOKENS": 16384,
        }
    )
    assert ds_low["extra_body"] == {
        "thinking": {"type": "enabled"},
        "reasoning_effort": "low",
    }

    # Opt-in via effort alone; enabled with that effort.
    ds_effort_only = _llm_call_kwargs(
        {
            "MODEL_TYPE": "deepseek-v4-flash",
            "OPENAI_MODEL": "deepseek-v4-flash",
            "REASONING_EFFORT": "high",
        }
    )
    assert ds_effort_only["extra_body"] == {
        "thinking": {"type": "enabled"},
        "reasoning_effort": "high",
    }

    # Enabled without explicit effort defaults to low (not provider high).
    ds_on = _llm_call_kwargs(
        {
            "MODEL_TYPE": "deepseek-v4-flash",
            "OPENAI_MODEL": "deepseek-v4-flash",
            "ENABLE_THINKING": True,
        }
    )
    assert ds_on["extra_body"] == {
        "thinking": {"type": "enabled"},
        "reasoning_effort": "low",
    }
