"""Focused algebra/interface regressions, not a formal geometry verifier."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent


class SeparatorTests(unittest.TestCase):
    def checker(self):
        path = ROOT / "verify.py"
        self.assertTrue(path.is_file(), "missing independent algebra checker")
        spec = importlib.util.spec_from_file_location("separator_verify", path)
        if spec is None or spec.loader is None:
            self.fail("checker module cannot be loaded")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module

    def test_literal_integral_derivations(self):
        result = self.checker().geometry_algebra()
        self.assertEqual(set(result), {"F", "A", "B", "delta", "E", "outsider"})

    def test_long_floor_rejects_wrong_coefficient(self):
        v = self.checker()
        self.assertTrue(callable(getattr(v, "long_floor", None)), "missing long-floor derivation")
        table = v.long_floor()
        self.assertEqual(len(table), 3)
        self.assertTrue(all(len(row) == 4 for row in table))
        bad = [list(row) for row in table]
        bad[2][2] += 1  # Still positive: positivity alone must not pass this.
        with self.assertRaisesRegex(v.VerificationError, "Bernstein"):
            v.long_floor(bad)

    def test_separator_budget_requires_two(self):
        v = self.checker()
        self.assertTrue(callable(getattr(v, "scalar_conclusion", None)), "missing separator budget")
        out = v.scalar_conclusion(v.R(1, 10), 2)
        self.assertTrue(out["strict"])
        self.assertEqual(out["linear_margin"], v.R(1012129, 155820000))
        with self.assertRaisesRegex(v.VerificationError, "two separators"):
            v.scalar_conclusion(v.R(1, 10), 1)

    def test_zero_height_is_null_not_strict(self):
        v = self.checker()
        try:
            result = v.scalar_conclusion(v.R(0), 0)
        except v.VerificationError as error:
            self.fail(f"zero-height literal branch missing: {error}")
        self.assertEqual(result, dict(S=0, H=0, linear_margin=0, strict=False))

    def test_mixed_event_recipe_error(self):
        v = self.checker()
        self.assertTrue(callable(getattr(v, "recipe_regression", None)), "missing typed-angle check")
        result = v.recipe_regression()
        self.assertEqual(result, dict(t=v.R(20,99), correct=v.R(99,101),
                                     erroneous=v.R(9401,10201), difference=-v.R(598,10201)))
        with self.assertRaisesRegex(v.VerificationError, "half-angle"):
            v.recipe_regression(result["erroneous"])

    def test_cyclic_incidence_ledger(self):
        v = self.checker()
        self.assertTrue(callable(getattr(v, "incidence_algebra", None)), "missing cyclic ledger")
        rows = v.incidence_algebra()
        self.assertEqual(set(rows), {"C", "D1", "D2"})
        self.assertEqual(rows["C"]["block_sizes"], [1, 1, 1, 1, 3])
        for row in rows.values():
            self.assertEqual(row["base_weights"], [1]*5)

    def test_compact_receipt(self):
        v = self.checker()
        self.assertTrue(callable(getattr(v, "verify_all", None)), "missing aggregate replay")
        result = v.verify_all()
        self.assertEqual(result["status"], "PASS_EXACT_SEPARATOR_ALGEBRA")
        self.assertEqual(result["margin"], "1012129/15582000")
        self.assertEqual(result["bernstein_coefficients"], 12)
        self.assertEqual(result["incidence_topologies"], ["C", "D1", "D2"])
        self.assertFalse(result["geometry_formalized"])


if __name__ == "__main__":
    unittest.main()
