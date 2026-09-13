import unittest
import verify_one_tenth as v


class CoefficientTests(unittest.TestCase):
    def setUp(self):
        self.values, self.lam, self.failed_precursor = v.build()

    def test_actual_four_branches(self):
        v.certify(self.values, self.lam)

    def test_rejected_pure_price_precursor(self):
        self.values['low'] = self.failed_precursor
        with self.assertRaises(ValueError):
            v.certify(self.values, self.lam)

    def test_out_of_capacity_price(self):
        with self.assertRaises(ValueError):
            v.certify(self.values, v.A(2))

    def test_missing_finite_high(self):
        del self.values['finite_high']
        with self.assertRaises(ValueError):
            v.certify(self.values, self.lam)

    def test_underpaid_tail(self):
        self.values['first_tail'] = v.A('53/640')
        with self.assertRaises(ValueError):
            v.certify(self.values, self.lam)


if __name__ == '__main__':
    unittest.main()
