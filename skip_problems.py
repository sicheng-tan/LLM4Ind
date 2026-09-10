"""Skip known non-theorem tasks before an experiment run.

A skip file is one path per line. Blank lines and ``#`` comments are ignored.
Paths are matched as trailing path components against copied task folders, so
``benchmarks/preprocessed/ind-ben/list/crafted_assorted/2`` still matches
``.../20260910_120000_ind-ben/list/crafted_assorted/2``.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

SKIP_FILE_ENV = "SKIP_PROBLEMS_FILE"
_PREPROCESSED_MARK = ("benchmarks", "preprocessed")


def add_skip_file_argument(parser) -> None:
    parser.add_argument(
        "--skip-file",
        type=str,
        default=None,
        help="每行一个错误定理路径的排除列表（# 开头为注释）。"
             f"也可用环境变量 {SKIP_FILE_ENV}。未指定则不排除。",
    )


def resolve_skip_file(cli_value: Optional[str] = None) -> Optional[str]:
    raw = (cli_value or os.getenv(SKIP_FILE_ENV) or "").strip()
    if not raw:
        return None
    path = Path(raw)
    if path.is_file():
        return str(path.resolve())
    repo_relative = Path(__file__).resolve().parent / raw
    if repo_relative.is_file():
        return str(repo_relative)
    return raw


def normalize_skip_parts(raw: str) -> Tuple[str, ...]:
    """Turn one skip-file line into path parts used for suffix matching."""
    text = (raw or "").strip().strip("\"'")
    if not text or text.startswith("#"):
        return ()
    text = text.replace("\\", "/")
    path = Path(text)
    if path.suffix.lower() == ".smt2":
        path = path.parent
    parts = [part for part in path.parts if part not in ("/", ".", "")]
    if parts and len(parts[0]) == 2 and parts[0][1] == ":":
        parts = parts[1:]
    for index in range(len(parts) - 1):
        if tuple(parts[index:index + 2]) == _PREPROCESSED_MARK:
            parts = parts[index + 2:]
            break
    return tuple(parts)


def load_skip_patterns(skip_file: str) -> List[Tuple[str, ...]]:
    path = Path(skip_file)
    if not path.is_file():
        raise FileNotFoundError(f"skip-file 不存在: {path}")
    patterns: List[Tuple[str, ...]] = []
    seen = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = normalize_skip_parts(line)
        if not parts:
            continue
        if parts in seen:
            continue
        seen.add(parts)
        patterns.append(parts)
    if not patterns:
        return []
    return patterns


def _component_matches(folder_part: str, skip_part: str) -> bool:
    if folder_part == skip_part:
        return True
    # Copied dataset roots are named ``<timestamp>_<original>``.
    return folder_part.endswith("_" + skip_part)


def _suffix_matches(folder_parts: Sequence[str], skip_parts: Sequence[str]) -> bool:
    if not skip_parts or len(folder_parts) < len(skip_parts):
        return False
    tail = folder_parts[-len(skip_parts):]
    return all(
        _component_matches(folder_part, skip_part)
        for folder_part, skip_part in zip(tail, skip_parts)
    )


def folder_is_skipped(folder: str, patterns: Sequence[Tuple[str, ...]]) -> bool:
    folder_parts = Path(folder).parts
    return any(_suffix_matches(folder_parts, pattern) for pattern in patterns)


def filter_skipped_folders(
    folders: Iterable[str],
    skip_file: Optional[str],
) -> Tuple[List[str], List[str], List[Tuple[str, ...]]]:
    """Return ``(kept, skipped, patterns)``. No file means keep everything."""
    folder_list = list(folders)
    if not skip_file:
        return folder_list, [], []
    patterns = load_skip_patterns(skip_file)
    kept: List[str] = []
    skipped: List[str] = []
    for folder in folder_list:
        if folder_is_skipped(folder, patterns):
            skipped.append(folder)
        else:
            kept.append(folder)
    return kept, skipped, patterns


def report_skipped_folders(skipped: Sequence[str], skip_file: str) -> None:
    print(f"skip-file: {skip_file}")
    print(f"排除已知错误定理 {len(skipped)} 题，不进入求解")
    for folder in skipped:
        print(f"  skip {folder}")
