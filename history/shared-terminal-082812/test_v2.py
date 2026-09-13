#!/usr/bin/env python3
from pathlib import Path
import json
import subprocess
import sys
import tempfile

D = Path(__file__).resolve().parent
V = D / "class_independent_terminal_strict_arb_v2.py"
W = D / "class_independent_terminal_strict_witness.json"
R = D / "class_independent_terminal_strict_receipt_v2.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


source = V.read_text()
require("pole_candidates=[m,O,R]" in source, "base pole candidates absent")
require("pole_candidates.append(O+ax)" in source, "pole interior grid events absent")
receipt = json.loads(R.read_text())
values = receipt["receipts"]["pole_endpoint_values"]
points = [entry["M"] for entry in values]
require(len(values) > 3, "too few pole endpoint values")
require(any("1.300000" in point for point in points), "pole interior grid events absent")
with tempfile.TemporaryDirectory() as td:
    output = Path(td) / "receipt.json"
    completed = subprocess.run(
        [sys.executable, "-B", str(V), str(W), "--output", str(output)],
        check=False,
    )
    require(completed.returncode == 0, f"verifier exited {completed.returncode}")
    require(output.read_bytes() == R.read_bytes(), "receipt byte mismatch")
print("SHARED_TERMINAL_V2_TESTS_OK")
