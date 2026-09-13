#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

D = Path(__file__).resolve().parent
V = D / "class_independent_terminal_strict_arb_v2.py"
W = D / "class_independent_terminal_strict_witness.json"
_spec = importlib.util.spec_from_file_location("strict_v2_security", V)
if _spec is None or _spec.loader is None:
    raise RuntimeError(f"cannot import verifier from {V}")
C = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(C)


def witness_copy() -> dict:
    return json.loads(W.read_text())


def write_witness(witness: dict, directory: str) -> Path:
    path = Path(directory) / W.name
    path.write_text(json.dumps(witness))
    return path


class CanonicalGridSecurityTests(unittest.TestCase):
    def test_single_price_row_deletion_is_rejected(self):
        witness = witness_copy()
        del witness["prices"]["low"][17]
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaisesRegex(C.SchemaError, "length mismatch"):
                C.run(write_witness(witness, td))

    def test_coordinated_grid_and_all_price_row_deletion_is_rejected(self):
        witness = witness_copy()
        del witness["radial_grid"][17]
        for row in witness["prices"].values():
            del row[17]
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaisesRegex(C.SchemaError, "canonical radial_grid"):
                C.run(write_witness(witness, td))


class ContractsSecurityTests(unittest.TestCase):
    def assert_contracts_rejected(self, mutate) -> None:
        witness = witness_copy()
        mutate(witness["contracts"])
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaisesRegex(C.SchemaError, "contracts mismatch"):
                C.run(write_witness(witness, td))

    def test_forged_contract_value_is_rejected(self):
        self.assert_contracts_rejected(
            lambda contracts: contracts.__setitem__("source_load", "attacker claim")
        )

    def test_extra_contract_field_is_rejected(self):
        self.assert_contracts_rejected(
            lambda contracts: contracts.__setitem__("unreviewed", "accepted")
        )

    def test_missing_contract_field_is_rejected(self):
        self.assert_contracts_rejected(lambda contracts: contracts.pop("numbers"))


class SourceLoadSecurityTests(unittest.TestCase):
    def test_source_overload_is_non_pass_and_nonzero_cli(self):
        witness = witness_copy()
        witness["prices"]["terminal_global"][0] = "1"
        with tempfile.TemporaryDirectory() as td:
            witness_path = write_witness(witness, td)
            output_path = Path(td) / "receipt.json"
            completed = subprocess.run(
                [sys.executable, "-B", str(V), str(witness_path), "--output", str(output_path)],
                check=False,
                capture_output=True,
                text=True,
            )
            receipt = json.loads(output_path.read_text())
        self.assertNotEqual(completed.returncode, 0)
        self.assertEqual(receipt["status"], "FAIL")
        self.assertFalse(receipt["source_load"]["pass"])


class OptimizedReplaySecurityTests(unittest.TestCase):
    BUNDLE = (
        "reproduce_v2.py",
        "class_independent_terminal_strict_arb_v2.py",
        "class_independent_terminal_strict_witness.json",
        "class_independent_terminal_strict_receipt_v2.json",
        "hash_ledger_v2.json",
    )

    def run_mutated_replay(self, mutate) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as td:
            bundle = Path(td)
            for name in self.BUNDLE:
                shutil.copyfile(D / name, bundle / name)
            mutate(bundle)
            return subprocess.run(
                [sys.executable, "-O", "-B", str(bundle / "reproduce_v2.py")],
                cwd=bundle,
                check=False,
                capture_output=True,
                text=True,
            )

    def assert_replay_rejects(self, mutate, reason: str) -> None:
        completed = self.run_mutated_replay(mutate)
        self.assertNotEqual(
            completed.returncode,
            0,
            msg=f"optimized replay accepted mutation:\n{completed.stdout}\n{completed.stderr}",
        )
        self.assertIn(reason, completed.stderr)
        self.assertNotIn("SHARED_TERMINAL_V2_EXACT_TREE_REPLAY_OK", completed.stdout)

    def test_python_optimized_replay_accepts_unmodified_bundle(self):
        completed = self.run_mutated_replay(lambda bundle: None)
        self.assertEqual(completed.returncode, 0, msg=completed.stderr)
        self.assertIn("SHARED_TERMINAL_V2_EXACT_TREE_REPLAY_OK", completed.stdout)

    def test_python_optimized_replay_rejects_metadata_mutation(self):
        def mutate(bundle: Path) -> None:
            ledger_path = bundle / "hash_ledger_v2.json"
            ledger = json.loads(ledger_path.read_text())
            ledger["release_floor"] = "forged"
            ledger_path.write_text(json.dumps(ledger))

        self.assert_replay_rejects(mutate, "hash ledger metadata mismatch: release_floor")

    def test_python_optimized_replay_rejects_contract_metadata_mutation(self):
        def mutate(bundle: Path) -> None:
            witness_path = bundle / "class_independent_terminal_strict_witness.json"
            witness = json.loads(witness_path.read_text())
            witness["contracts"]["source_load"] = "forged contract"
            witness_path.write_text(json.dumps(witness))
            ledger_path = bundle / "hash_ledger_v2.json"
            ledger = json.loads(ledger_path.read_text())
            ledger["witness_sha256"] = hashlib.sha256(witness_path.read_bytes()).hexdigest()
            ledger_path.write_text(json.dumps(ledger))

        self.assert_replay_rejects(mutate, "verifier exited 2")

    def test_python_optimized_replay_rejects_hash_mutation(self):
        def mutate(bundle: Path) -> None:
            ledger_path = bundle / "hash_ledger_v2.json"
            ledger = json.loads(ledger_path.read_text())
            ledger["witness_sha256"] = "0" * 64
            ledger_path.write_text(json.dumps(ledger))

        self.assert_replay_rejects(mutate, "witness_sha256 mismatch")

    def test_python_optimized_replay_rejects_receipt_mutation(self):
        def mutate(bundle: Path) -> None:
            receipt_path = bundle / "class_independent_terminal_strict_receipt_v2.json"
            receipt = json.loads(receipt_path.read_text())
            receipt["coefficient_lower"] = "forged"
            receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
            ledger_path = bundle / "hash_ledger_v2.json"
            ledger = json.loads(ledger_path.read_text())
            ledger["receipt_sha256"] = hashlib.sha256(receipt_path.read_bytes()).hexdigest()
            ledger_path.write_text(json.dumps(ledger))

        self.assert_replay_rejects(mutate, "receipt byte mismatch")

    def test_python_optimized_replay_rejects_non_pass_verifier(self):
        def mutate(bundle: Path) -> None:
            verifier_path = bundle / "class_independent_terminal_strict_arb_v2.py"
            source = verifier_path.read_text()
            old = "out['status']='PASS' if src['pass'] and all(checks.values()) and out['strict_gt_0p082'] else 'FAIL'"
            new = "out['status']='FAIL' if src['pass'] and all(checks.values()) and out['strict_gt_0p082'] else 'PASS'"
            self.assertEqual(source.count(old), 1)
            verifier_path.write_text(source.replace(old, new))
            ledger_path = bundle / "hash_ledger_v2.json"
            ledger = json.loads(ledger_path.read_text())
            ledger["verifier_sha256"] = hashlib.sha256(verifier_path.read_bytes()).hexdigest()
            ledger_path.write_text(json.dumps(ledger))

        self.assert_replay_rejects(mutate, "verifier exited 2")


if __name__ == "__main__":
    unittest.main()
