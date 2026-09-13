#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

D = Path(__file__).resolve().parent
V = D / "class_independent_terminal_strict_arb_v2.py"
W = D / "class_independent_terminal_strict_witness.json"
R = D / "class_independent_terminal_strict_receipt_v2.json"
LEDGER_PATH = D / "hash_ledger_v2.json"
EXPECTED_LEDGER_METADATA = {
    "git_parent": "ccfd7f7dae432c27b7a3b35991c4c133f8027137",
    "receipt_path": "archive/shared-terminal-082812/class_independent_terminal_strict_receipt_v2.json",
    "release_floor": "0.082812499999972190",
    "strict_internal_lower": "0.0828124999999721904111374192974978881",
    "verifier_path": "archive/shared-terminal-082812/class_independent_terminal_strict_arb_v2.py",
    "witness_path": "archive/shared-terminal-082812/class_independent_terminal_strict_witness.json",
}
HASH_KEYS = {"verifier_sha256", "witness_sha256", "receipt_sha256"}


class ReplayError(RuntimeError):
    pass


def fail_unless(condition: bool, message: str) -> None:
    if not condition:
        raise ReplayError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_ledger() -> dict:
    ledger = json.loads(LEDGER_PATH.read_text())
    fail_unless(isinstance(ledger, dict), "hash ledger must be an object")
    expected_keys = set(EXPECTED_LEDGER_METADATA) | HASH_KEYS
    fail_unless(set(ledger) == expected_keys, "hash ledger schema mismatch")
    for key, expected in EXPECTED_LEDGER_METADATA.items():
        fail_unless(ledger[key] == expected, f"hash ledger metadata mismatch: {key}")
    for key in HASH_KEYS:
        value = ledger[key]
        fail_unless(
            isinstance(value, str)
            and len(value) == 64
            and all(char in "0123456789abcdef" for char in value),
            f"invalid SHA-256 field: {key}",
        )
    return ledger


def main() -> None:
    ledger = load_ledger()
    for key, path in (
        ("verifier_sha256", V),
        ("witness_sha256", W),
        ("receipt_sha256", R),
    ):
        actual = sha(path)
        fail_unless(actual == ledger[key], f"{key} mismatch: {actual} != {ledger[key]}")

    with tempfile.TemporaryDirectory() as td:
        output = Path(td) / "receipt.json"
        completed = subprocess.run(
            [sys.executable, "-B", str(V), str(W), "--output", str(output)],
            check=False,
        )
        fail_unless(completed.returncode == 0, f"verifier exited {completed.returncode}")
        fail_unless(output.is_file(), "verifier did not produce a receipt")
        fail_unless(output.read_bytes() == R.read_bytes(), "receipt byte mismatch")
        receipt = json.loads(output.read_text())
        fail_unless(receipt.get("status") == "PASS", "reproduced receipt is not PASS")
        fail_unless(
            receipt.get("strict_gt_0p082") is True,
            "reproduced receipt does not prove strict_gt_0p082",
        )
    print("SHARED_TERMINAL_V2_EXACT_TREE_REPLAY_OK")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"SHARED_TERMINAL_V2_EXACT_TREE_REPLAY_ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
