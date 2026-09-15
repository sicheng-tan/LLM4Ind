"""Ancestor stack + same_as_ancestor screening + PROOF PATH GOALS prompt."""

from __future__ import annotations

import os
import unittest
from unittest.mock import patch

from ancestor_stack import (
    empty_ancestor_stack,
    extend_ancestors,
    format_proof_path_goals_for_prompt,
    lemma_matches_ancestor,
)
from exp_flags import ancestor_cycle_filter_enabled, ancestor_prompt_enabled
from lemma_gates import (
    BENIGN_SCREEN_GATES,
    apply_static_lemma_screen,
    lemma_same_as_goal,
)


ROOT = (
    "(forall ((x Bin) (y Bin) (z Bin)) "
    "(= (times x (plus y z)) (plus (times x y) (times x z))))"
)
LEFT = (
    "(forall ((a Bin) (b Bin) (c Bin)) "
    "(= (times (plus a b) c) (plus (times a c) (times b c))))"
)
ROOT_ALPHA = (
    "(forall ((u Bin) (v Bin) (w Bin)) "
    "(= (times u (plus v w)) (plus (times u v) (times u w))))"
)
BRIDGE = (
    "(forall ((x Bin) (y Bin)) "
    "(= (times (OneAnd x) y) (plus (ZeroAnd (times x y)) y)))"
)


class AncestorStackTests(unittest.TestCase):
    def test_extend_builds_strict_path(self) -> None:
        root = empty_ancestor_stack()
        child = extend_ancestors(root, "template", 0, ROOT)
        self.assertEqual(len(child), 1)
        self.assertEqual(child[0]["goal_id"], "template")
        grand = extend_ancestors(child, "template_1", 1, LEFT)
        self.assertEqual(len(grand), 2)
        self.assertEqual(grand[1]["formula"], LEFT)

    def test_match_alpha(self) -> None:
        stack = extend_ancestors((), "template", 0, ROOT)
        hit = lemma_matches_ancestor(
            ROOT_ALPHA, stack, equivalent=lemma_same_as_goal
        )
        self.assertIsNotNone(hit)
        self.assertEqual(hit["goal_id"], "template")
        self.assertIsNone(
            lemma_matches_ancestor(BRIDGE, stack, equivalent=lemma_same_as_goal)
        )

    def test_format_prompt_requires_ancestors(self) -> None:
        self.assertEqual(
            format_proof_path_goals_for_prompt(
                current_id="template",
                current_depth=0,
                current_formula=ROOT,
                stack=(),
            ),
            "",
        )
        stack = extend_ancestors((), "template", 0, ROOT)
        txt = format_proof_path_goals_for_prompt(
            current_id="template_1",
            current_depth=1,
            current_formula=LEFT,
            stack=stack,
        )
        self.assertIn("PROOF PATH GOALS", txt)
        self.assertIn("CURRENT", txt)
        self.assertIn("ANCESTOR A0", txt)
        self.assertIn(ROOT, txt)
        self.assertIn(LEFT, txt)


class AncestorScreenTests(unittest.TestCase):
    def test_drops_ancestor_benign(self) -> None:
        stack = extend_ancestors((), "template", 0, ROOT)
        with patch.dict(os.environ, {
            "ANCESTOR_CYCLE_FILTER": "on",
            "LEMMA_FILTER_DROP": "on",
            "LEMMA_DEFINED_SYMBOLS": "off",
        }):
            kept, dropped = apply_static_lemma_screen(
                [ROOT_ALPHA, BRIDGE],
                original_forall=LEFT,
                smt="; empty",
                invalid_records=[],
                same_as_goal=lemma_same_as_goal,
                ancestor_stack=stack,
            )
        self.assertEqual(kept, [BRIDGE])
        self.assertEqual(len(dropped), 1)
        self.assertEqual(dropped[0][2], "same_as_ancestor")
        self.assertIn("cycle_detected", dropped[0][1])
        self.assertIn("same_as_ancestor", BENIGN_SCREEN_GATES)

    def test_same_as_goal_still_separate(self) -> None:
        stack = extend_ancestors((), "template", 0, ROOT)
        with patch.dict(os.environ, {
            "ANCESTOR_CYCLE_FILTER": "on",
            "LEMMA_FILTER_DROP": "on",
            "LEMMA_DEFINED_SYMBOLS": "off",
        }):
            kept, dropped = apply_static_lemma_screen(
                [LEFT, BRIDGE],
                original_forall=LEFT,
                smt="; empty",
                invalid_records=[],
                same_as_goal=lemma_same_as_goal,
                ancestor_stack=stack,
            )
        self.assertEqual(kept, [BRIDGE])
        self.assertEqual(dropped[0][2], "same_as_goal")

    def test_filter_off_skips_ancestor_gate(self) -> None:
        stack = extend_ancestors((), "template", 0, ROOT)
        with patch.dict(os.environ, {
            "ANCESTOR_CYCLE_FILTER": "off",
            "LEMMA_FILTER_DROP": "on",
            "LEMMA_DEFINED_SYMBOLS": "off",
        }):
            self.assertFalse(ancestor_cycle_filter_enabled())
            kept, dropped = apply_static_lemma_screen(
                [ROOT_ALPHA, BRIDGE],
                original_forall=LEFT,
                smt="; empty",
                invalid_records=[],
                same_as_goal=lemma_same_as_goal,
                ancestor_stack=stack,
            )
        self.assertEqual(kept, [ROOT_ALPHA, BRIDGE])
        self.assertEqual(dropped, [])


class AncestorFlagTests(unittest.TestCase):
    def test_flags_default_on(self) -> None:
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("ANCESTOR_CYCLE_FILTER", None)
            os.environ.pop("ANCESTOR_PROMPT", None)
            self.assertTrue(ancestor_cycle_filter_enabled())
            self.assertTrue(ancestor_prompt_enabled())


if __name__ == "__main__":
    unittest.main()
