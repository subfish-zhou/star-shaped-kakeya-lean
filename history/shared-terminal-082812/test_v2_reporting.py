#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

D = Path(__file__).resolve().parent
V = D / "class_independent_terminal_strict_arb_v2.py"
W = D / "class_independent_terminal_strict_witness.json"
_spec = importlib.util.spec_from_file_location("strict_v2", V)
if _spec is None or _spec.loader is None:
    raise RuntimeError(f"cannot import verifier from {V}")
C = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(C)


def run_mutated(**updates):
    witness = json.loads(W.read_text())
    witness.update(updates)
    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "mutated-witness.json"
        path.write_text(json.dumps(witness))
        return C.run(path)


class ReportingRegressionTests(unittest.TestCase):
    def test_receipt_parameters_come_from_witness(self):
        result = run_mutated(H="1/4", M0="9/10", R="3/2")
        self.assertEqual(
            result["parameters"],
            {"H": "1/4", "M0": "9/10", "R": "3/2"},
        )

    def test_receipt_target_label_comes_from_witness(self):
        result = run_mutated(target_pi_times_coefficient="2/25")
        self.assertEqual(result["target"]["pi_times_coefficient"], "2/25")


class NormalizedWitnessRegressionTests(unittest.TestCase):
    def test_frozen_witness_uses_unit_price_scale(self):
        witness = json.loads(W.read_text())
        self.assertEqual(
            witness["generator_diagnostics_not_proof"]["inward_scale"], "1"
        )
        self.assertEqual(witness["prices"]["low"][0], "1")

    def test_normalized_witness_certifies_promoted_floor(self):
        result = C.run(W)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(
            result["target"]["pi_times_coefficient"], "0.082812499999972190"
        )
        self.assertTrue(all(result["checks"].values()))


if __name__ == "__main__":
    unittest.main()
