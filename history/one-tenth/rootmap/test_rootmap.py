#!/usr/bin/env python3
"""Focused exact regressions, discoverable by unittest in normal and -O modes."""
import copy
from fractions import Fraction as F
from itertools import product
import unittest
import check_rootmap as m


class RootmapTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = m.build_candidate()
        cls.mapping = m.load_fixture()

    def test_nonempty_complete_census_and_ordered_partitions(self):
        self.assertEqual(len(m.universe()), 441)
        self.assertEqual(len(self.expected['candidate_roots']), 27)
        combined = self.expected['conditional_old_plus_candidate_ids']
        complement = self.expected['ordered_conditional_complement']
        self.assertEqual(len(complement), 407)
        self.assertEqual(sorted(combined+complement), list(self.mapping))
        self.assertFalse(set(combined) & set(complement))
        self.assertEqual(self.expected['preserved_old_certified_roots_not_reaudited'], list(m.OLD))

    def test_omitted_or_swapped_root_fixture_rejected(self):
        lines = (m.HERE/'production_ids.tsv').read_text().splitlines()
        with self.assertRaisesRegex(ValueError, 'omitted/reordered'):
            m.parse_fixture('\n'.join(lines[:5]+lines[6:]))
        # Keeping the count is not sufficient: duplicate a signature under another ID.
        fields = lines[8].split('\t')
        lines[8] = fields[0]+'\t'+'\t'.join(lines[7].split('\t')[1:])
        with self.assertRaisesRegex(ValueError, 'signature universe'):
            m.parse_fixture('\n'.join(lines))

    def test_omitted_candidate_and_complement_rejected(self):
        for key in ('candidate_root_ids', 'candidate_roots', 'ordered_conditional_complement'):
            bad = copy.deepcopy(self.expected)
            bad[key].pop()
            with self.assertRaises(ValueError):
                m.validate_candidate(bad, self.expected)

    def test_altered_guard_rejected(self):
        changes = [('A', '2*I*R+2*h*(R*R-I*I)'), ('B', 'I-h*R'),
                   ('closing_gap', 'qR=I_free/R_free'),
                   ('closure_nonnegative', ['I_free', '7*R_free-3*I_free'])]
        for key, value in changes:
            bad = copy.deepcopy(self.expected)
            bad['guard_contract'][key] = value
            with self.assertRaises(ValueError):
                m.validate_candidate(bad, self.expected)
        bad = copy.deepcopy(self.expected)
        bad['guard_contract']['weak_states']['0'] = 'A>=0'
        with self.assertRaises(ValueError):
            m.validate_candidate(bad, self.expected)

    def test_no_promotion_or_four_face_count_mutation(self):
        for key, value in [('promotion_authorized', True), ('new_fully_certified_production_roots', ['R004'])]:
            bad = copy.deepcopy(self.expected)
            bad[key] = value
            with self.assertRaises(ValueError):
                m.validate_candidate(bad, self.expected)
        bad = copy.deepcopy(self.expected)
        bad['four_lower_faces']['new_root_coverage'] = 23
        with self.assertRaises(ValueError):
            m.validate_candidate(bad, self.expected)

    def test_product_norm_and_all_path_reconstruction(self):
        free = (F(1, 100), F(1, 100), F(1, 5), F(1, 5), F(1, 5), F(1, 2))
        for name, path in m.PATHS:
            qs = [free[i] for i in path]
            r, i, a, b = m.support_values(qs, F(1, 10))
            norm = F(1)
            for q in qs:
                norm *= 1+q*q
            self.assertEqual(r*r+i*i, norm, name)
            # Independently form cos/sin of the actual full path angle.
            c, s = F(1), F(0)
            for q in qs:
                cq, sq = (1-q*q)/(1+q*q), 2*q/(1+q*q)
                c, s = c*cq-s*sq, s*cq+c*sq
            self.assertEqual(a/norm, s-F(1, 5)*c)
            self.assertEqual(b/r, i/r-F(1, 5))

    def test_adjacent_state0_to_short_identity(self):
        checked = 0
        for h, q in product((F(0), F(1, 20), F(1, 5)), (F(0), F(1, 10), F(1, 5), F(3, 7))):
            r, i, a, b = m.support_values([q], h)
            self.assertEqual((r, i), (1, q))
            self.assertEqual(a/2-b, h*(1+q*q))
            for state in (0, 1, 2):
                if m.weak_state(state, a, b):
                    self.assertTrue(q <= 2*h if state != 2 else q >= 2*h)
                    checked += 1
        self.assertGreater(checked, 0)

    def test_A_and_B_equality_both_incident_states(self):
        q = F(1, 10)
        h = q/(1-q*q)
        _, _, a, b = m.support_values([q], h)
        self.assertEqual(a, 0)
        self.assertLess(b, 0)
        self.assertTrue(m.weak_state(0, a, b))
        self.assertTrue(m.weak_state(1, a, b))
        _, _, a, b = m.support_values([2*h], h)
        self.assertEqual(b, 0)
        self.assertTrue(m.weak_state(1, a, b))
        self.assertTrue(m.weak_state(2, a, b))
        self.assertFalse(m.weak_state(0, a, b))
        # Zero-width short at positive h is not discarded.
        _, _, a, b = m.support_values([F(0)], h)
        self.assertTrue(m.weak_state(0, a, b))

    def test_zero_height_all_selected_closures_and_seam(self):
        for qL, qR in ((m.D, m.U), (m.U, m.D)):
            free = (F(0),)*5 + (qL,)
            self.assertEqual(m.closing_gap(free), qR)
            for row in self.expected['candidate_roots']:
                sig = self.mapping[row['root_id']]
                self.assertTrue(m.carrier_point(sig, free, F(0)))
                self.assertTrue(m.theorem_point(sig, free, F(0)))
        # Positive margin at h=0 is deliberately nowhere claimed by the checker.

    def test_positive_height_simultaneous_long_equalities(self):
        h = F(1, 10)
        free = (F(1, 100), F(1, 100), 2*h, 2*h, 2*h, F(1, 2))
        found = []
        for row in self.expected['candidate_roots']:
            sig = self.mapping[row['root_id']]
            if m.carrier_point(sig, free, h):
                found.append(row['root_id'])
                self.assertTrue(m.theorem_point(sig, free, h))
        self.assertGreater(len(found), 0, 'must exercise a real whole-support weak carrier')
        self.assertGreaterEqual(m.closing_gap(free), m.D)

    def test_missing_separator_and_wrong_closure_branch_rejected(self):
        with self.assertRaisesRegex(ValueError, 'gap box'):
            m.closing_gap((F(1, 5),)*6)
        with self.assertRaisesRegex(ValueError, 'closure cone'):
            m.closing_gap((m.D,)*5+(m.U,))
        with self.assertRaisesRegex(ValueError, 'outside cube'):
            m.cube((F(0),)*6+(F(2),))

    def test_reflection_and_cube_inverse(self):
        for a, b in m.universe():
            self.assertEqual(m.reflect(m.reflect(b)), b)
        z = tuple(F(i, 7) for i in range(7))
        free, h = m.cube(z)
        inverse = tuple(q/m.D for q in free[:5])+(F(21, 40)*(free[5]-m.D), 5*h)
        self.assertEqual(inverse, z)
        self.assertGreater(m.D, 2*m.HMAX)
        self.assertLess(3*m.D*m.D, 1)  # atan(D)<pi/6, branch proof


if __name__ == '__main__':
    unittest.main()
