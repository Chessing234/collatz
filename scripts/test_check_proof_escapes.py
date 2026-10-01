#!/usr/bin/env python3
"""Regression tests for source masking and forbidden-code detection."""
import unittest
from check_proof_escapes import code_only, violations


class EscapeScreenTests(unittest.TestCase):
    def test_citation_and_escaped_quotes(self):
        text = r'def citation := "title \"2 axioms, 0 sorry\""'
        self.assertEqual(violations(text), [])

    def test_nested_comments(self):
        text = '/- sorry /- axiom -/ native_decide -/\n-- sorryAx\nexample : True := by trivial'
        self.assertEqual(violations(text), [])

    def test_actual_proof_escapes(self):
        for term in ('sorry', 'sorryAx', 'native_decide', 'ofReduceBool', 'byAsSorry'):
            with self.subTest(term=term):
                self.assertTrue(violations(f'example : True := by {term}'))

    def test_comment_delimiters_in_strings_do_not_hide_code(self):
        for value in ('/-', '--', '-/'):
            self.assertEqual(violations(f'def s := "{value}"\nexample : False := by sorry'),
                             [(2, 'sorry')])

    def test_raw_strings(self):
        for value in ('r"sorry"', 'r#"sorry " axiom"#', 'r###"native_decide"###'):
            self.assertEqual(violations('def s := '+value+'\nexample : False := by sorry'),
                             [(2, 'sorry')])

    def test_characters_and_identifier_primes(self):
        self.assertEqual(violations('def quote := \'"\'\nexample\' : False := by sorry'),
                         [(2, 'sorry')])

    def test_interpolated_code_is_never_masked(self):
        for value in ('s!"{(by sorry : Nat)}"', 'm!"{(by sorry : Nat)}"',
                      's!"{(by let x := "text"; sorry : Nat)}"'):
            self.assertTrue(violations('def s := '+value))

    def test_positions_preserved(self):
        text = 'def s := "first\nsecond"\n/-nested\ncomment-/\nexample : False := by sorry'
        self.assertEqual(len(code_only(text)), len(text))
        self.assertEqual(violations(text), [(5, 'sorry')])

    def test_declaration_location_after_blank_lines(self):
        self.assertEqual(violations('/- ignored -/\n\nprivate\nopaque bad : Nat'),
                         [(4, 'opaque')])

    def test_declarations_and_attributes(self):
        for value in ('axiom bad : False', 'private unsafe def bad := 1',
                      '@[extern "native"] def bad := 1', 'opaque bad : Nat'):
            self.assertTrue(violations(value))


if __name__ == '__main__':
    unittest.main()
