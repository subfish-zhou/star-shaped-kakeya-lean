"""Focused guards; unittest checks remain active under python -O."""
import unittest
from fractions import Fraction as F
import verifier as v


class Guards(unittest.TestCase):
    def test_source_load_exact_and_overload(self):
        self.assertIsNotNone(v, 'source-load checker is not implemented')
        rows = [(F(0), F(1), (F(1, 3), F(2, 3), F(0), F(0), F(0)))]
        self.assertEqual(v.source_load(rows), F(1))
        rows[0] = (F(0), F(1), (F(1, 3), F(2, 3), F(1, 10**30), F(0), F(0)))
        with self.assertRaisesRegex(ValueError, 'source overload'):
            v.source_load(rows)

    def test_wrong_price_rejected(self):
        self.assertTrue(hasattr(v, 'load'), 'fixed witness loader is missing')
        data = v.load()
        data['x'] = '1/3'
        with self.assertRaisesRegex(ValueError, 'fixed witness'):
            v.validate(data)

    def test_wrong_arithmetic_rejected(self):
        self.assertTrue(hasattr(v, 'receipts'), 'branch arithmetic is missing')
        values = v.receipts(v.load())
        v.certify(values)
        values['low'] = 0
        with self.assertRaisesRegex(ValueError, 'arithmetic: low'):
            v.certify(values)

    def test_fixed_rows_and_loads(self):
        table = v.rows(v.load())
        self.assertEqual(len(table), 7)
        e = F(v.FIXED['epsilon'])
        self.assertEqual([sum(p) for _, _, p in table], [1, 1-e, 1-e, 1, 1, 1-e, 1])
        self.assertEqual(v.source_load(table), 1)

    def test_float_boolean_and_target_changes_rejected(self):
        for key, bad in [('x', 0.3), ('x', True), ('target', '0.08')]:
            with self.subTest(key=key, bad=bad):
                data = v.load()
                data[key] = bad
                with self.assertRaises(ValueError):
                    v.validate(data)

    def test_tail_exact_crossings_and_zero(self):
        # Independent three-piece integration: [.8,1], [1,1.1], [1.1,1.6].
        expected = F(1, 2)*(1-F(4, 5)**2)/2 + F(1, 20) + F(1, 8)
        self.assertEqual(expected, F(53, 200))
        self.assertEqual(v.terminal_integral(F(8, 5), F(4, 5), F(8, 5)), expected)
        self.assertEqual(v.terminal_integral(F(8, 5), F(8, 5), F(2)), 0)
        self.assertEqual(v.terminal_integral(F(16, 5), F(8, 5), F(16, 5)), F(27, 40))
        self.assertEqual(v.terminal_integral(F(8, 5), F(1), F(1)), 0)

    def test_all_branch_values_in_independent_decimal_windows(self):
        values = v.receipts(v.load())
        lows = ('0.082812499999998901998654', '0.082812499999991696642604',
                '0.082812499999972190411137')
        for key, lower in zip(v.BRANCHES, lows):
            self.assertTrue(values[key] > v.A(lower), key)
            self.assertTrue(values[key] < v.A(F(lower)+F(1, 10**24)), key)
        self.assertTrue(values['first-tail'].contains(v.A(F(53, 640))))
        self.assertTrue(values['later-tail'].contains(v.A(F(27, 256))))
        del values['later-tail']
        with self.assertRaisesRegex(ValueError, 'branch coverage'):
            v.certify(values)


if __name__ == '__main__':
    unittest.main()
