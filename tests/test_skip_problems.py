#!/usr/bin/env python3
"""Skip-file path matching for known non-theorem tasks."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from skip_problems import (
    filter_skipped_folders,
    folder_is_skipped,
    load_skip_patterns,
    normalize_skip_parts,
)


def test_normalize_strips_preprocessed_and_smt2() -> None:
    assert normalize_skip_parts(
        "benchmarks/preprocessed/ind-ben/list/crafted_assorted/2"
    ) == ("ind-ben", "list", "crafted_assorted", "2")
    assert normalize_skip_parts(
        "benchmarks/preprocessed/dtt/dtt-leon/bsearch-tree-goal4/template.smt2"
    ) == ("dtt", "dtt-leon", "bsearch-tree-goal4")
    assert normalize_skip_parts("# comment") == ()
    assert normalize_skip_parts("  ") == ()


def test_copied_dataset_prefix_still_matches() -> None:
    patterns = [
        normalize_skip_parts("benchmarks/preprocessed/ind-ben/list/crafted_assorted/2")
    ]
    copied = (
        "/tmp/results/20260910_120000_ind-ben/list/crafted_assorted/2"
    )
    assert folder_is_skipped(copied, patterns)
    assert not folder_is_skipped(
        "/tmp/results/20260910_120000_ind-ben/list/crafted_assorted/22",
        patterns,
    )
    assert not folder_is_skipped(
        "/tmp/results/20260910_120000_ind-ben/list/crafted_assorted/12",
        patterns,
    )


def test_dtt_bsearch_does_not_skip_vmcai_homonym() -> None:
    patterns = [
        normalize_skip_parts(
            "benchmarks/preprocessed/dtt/dtt-leon/bsearch-tree-goal4"
        )
    ]
    assert folder_is_skipped(
        "/tmp/20260910_dtt/dtt-leon/bsearch-tree-goal4", patterns
    )
    assert not folder_is_skipped(
        "/tmp/20260910_vmcai15-dt/leon/bsearch-tree-goal4", patterns
    )
    assert not folder_is_skipped(
        "/tmp/20260910_dtt/dtt-leon/bsearch-tree-goal14", patterns
    )


def test_filter_reads_file(tmp_path: Path) -> None:
    skip = tmp_path / "skip.txt"
    skip.write_text(
        "# header\n"
        "ind-ben/list/crafted_assorted/2\n"
        "\n"
        "dtt/dtt-leon/bsearch-tree-goal4\n",
        encoding="utf-8",
    )
    folders = [
        str(tmp_path / "20260101_ind-ben/list/crafted_assorted/2"),
        str(tmp_path / "20260101_ind-ben/list/crafted_assorted/3"),
        str(tmp_path / "20260101_dtt/dtt-leon/bsearch-tree-goal4"),
    ]
    kept, skipped, patterns = filter_skipped_folders(folders, str(skip))
    assert len(patterns) == 2
    assert kept == [folders[1]]
    assert skipped == [folders[0], folders[2]]


def test_bundled_skip_file_parses() -> None:
    bundled = ROOT / "experiments" / "configs" / "skip_nontheorems.txt"
    patterns = load_skip_patterns(str(bundled))
    assert len(patterns) == 16
    assert ("ind-ben", "list", "crafted_assorted", "2") in patterns
    assert ("ind-ben", "tree", "crafted_rotate", "10") in patterns
    assert ("dtt", "dtt-leon", "bsearch-tree-goal11") in patterns
    assert ("vmcai15-dt", "leon", "heap-goal11") in patterns
    assert ("vmcai15-dt", "isa", "goal75") in patterns


def main() -> int:
    test_normalize_strips_preprocessed_and_smt2()
    test_copied_dataset_prefix_still_matches()
    test_dtt_bsearch_does_not_skip_vmcai_homonym()
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        test_filter_reads_file(Path(tmp))
    test_bundled_skip_file_parses()
    print("skip problem tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
