"""Controls for the limited comments-only recorded-candidate transformation."""

import unittest

from lark_kernels.certificate import DEFAULT_PROOFS, validate_proofs
from reproduction.local_models.replay_comments import remove_comments


class CommentReplayTests(unittest.TestCase):
    def test_nested_and_line_comments_preserve_code_and_line_structure(self):
        text = "by\r\n  /- outer /- inner -- not line -/ end -/\r\n  rfl -- explanation\r\n"
        cleaned, count = remove_comments(text)
        self.assertEqual(count, 3)
        self.assertEqual(len(text), len(cleaned))
        self.assertEqual(
            [i for i, c in enumerate(text) if c in "\r\n"],
            [i for i, c in enumerate(cleaned) if c in "\r\n"],
        )
        self.assertEqual(cleaned.split(), ["by", "rfl"])

    def test_comments_cannot_hide_outside_declarations_or_admission(self):
        for forbidden in (
            "sorry",
            "native_decide",
            "axiom fabricated : False",
            "end LarkCertificate",
        ):
            with self.subTest(forbidden=forbidden):
                good, _ = remove_comments("by /- " + forbidden + " -/ rfl")
                validate_proofs({**DEFAULT_PROOFS, "segmentation_data": good})
                bad, _ = remove_comments("by /- harmless -/ " + forbidden)
                with self.assertRaises(ValueError):
                    validate_proofs({**DEFAULT_PROOFS, "segmentation_data": bad})

    def test_quoted_forms_are_refused_instead_of_reinterpreted_as_comments(self):
        for text in (
            'by exact "-- text"',
            "by exact «/- name -/»",
            "by exact '-'",
            'by exact r#"/- text -/"#',
        ):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "Quoted forms"):
                remove_comments(text)

    def test_unterminated_block_comment_is_refused(self):
        for text in ("by /- unclosed", "by /- outer /- inner -/ rfl"):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "Unterminated"):
                remove_comments(text)

    def test_identifier_apostrophes_are_preserved(self):
        source = "by\n  have value' := value\n  exact value' -- comment\n"
        cleaned, count = remove_comments(source)
        self.assertEqual(count, 1)
        self.assertIn("have value' := value", cleaned)
        self.assertIn("exact value'", cleaned)

    def test_documentation_tokens_are_not_removed_as_whitespace(self):
        for text in ("by /-- documentation -/ rfl", "by /-! module text -/ rfl"):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "Documentation"):
                remove_comments(text)

    def test_ambiguous_line_or_column_forms_are_refused(self):
        for text in ("by -- comment\r rfl", "by /- α -/ rfl", "by /-\tcomment -/ rfl"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                remove_comments(text)


if __name__ == "__main__":
    unittest.main()
