import copy
import json
import unittest
import verify_closeout as v


class CloseoutTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((v.ROOT / 'closeout.json').read_text())

    def test_reviewed_partition(self):
        v.validate(self.data)

    def test_missing_root_rejected(self):
        self.data['new_roots'].pop()
        with self.assertRaises(ValueError):
            v.validate(self.data)

    def test_global_claim_rejected(self):
        self.data['universal_0p1_proved'] = True
        with self.assertRaises(ValueError):
            v.validate(self.data)

    def test_omitted_binding_rejected(self):
        self.data['audited_files'].pop('separator/THEOREM.md')
        with self.assertRaises(ValueError):
            v.validate(self.data)

    def test_wrong_review_commit_rejected(self):
        self.data['reviewed_commits']['rootmap'] = '0' * 40
        with self.assertRaises(ValueError):
            v.validate(self.data)


if __name__ == '__main__':
    unittest.main()
