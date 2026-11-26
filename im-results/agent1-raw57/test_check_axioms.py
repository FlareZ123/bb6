#!/usr/bin/env python3
"""Regression tests for wrapped Lean axiom-report parsing."""
from __future__ import annotations

import unittest

from check_axioms import parse_axiom_profiles


class ParseAxiomProfilesTests(unittest.TestCase):
    def test_single_line_profiles(self) -> None:
        text = (
            "'A.theorem' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'B.theorem' depends on axioms: []\n"
        )
        self.assertEqual(
            parse_axiom_profiles(text),
            [
                ("'A.theorem'", {"propext", "Classical.choice", "Quot.sound"}),
                ("'B.theorem'", set()),
            ],
        )

    def test_wrapped_profile_and_following_profile(self) -> None:
        text = (
            "'A.theorem' depends on axioms: [propext,\n"
            "  Classical.choice,\n"
            "  Quot.sound]\n"
            "'B.theorem' depends on axioms: [propext]\n"
        )
        self.assertEqual(
            parse_axiom_profiles(text),
            [
                ("'A.theorem'", {"propext", "Classical.choice", "Quot.sound"}),
                ("'B.theorem'", {"propext"}),
            ],
        )

    def test_unterminated_profile_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "unterminated"):
            parse_axiom_profiles("'A.theorem' depends on axioms: [propext,\n")

    def test_next_profile_cannot_hide_unterminated_profile(self) -> None:
        text = (
            "'A.theorem' depends on axioms: [propext,\n"
            "'B.theorem' depends on axioms: [Quot.sound]\n"
        )
        with self.assertRaisesRegex(ValueError, "new axiom profile"):
            parse_axiom_profiles(text)


if __name__ == "__main__":
    unittest.main()
