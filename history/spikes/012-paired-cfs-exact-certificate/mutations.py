#!/usr/bin/env python3
"""Adversarial controls for arithmetic teeth, geometry, and artifact binding."""
from __future__ import annotations

import copy
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
PRODUCTION_FAULTS = (
    "remove_paired_term",
    "asin_wrong_direction",
    "high_tail_start",
)


def geometric_mutation_cases(data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """The three retained primary-geometry fault families."""
    def cloned() -> dict[str, Any]:
        return copy.deepcopy(data)

    overlap = cloned()
    overlap["paired"]["J_left"] = overlap["paired"]["H"]
    bad_q = cloned()
    bad_q["paired"]["q"] = "1/2"
    bad_q["paired"]["paired_reach"] = "1/2"
    cross = cloned()
    cross["paired"]["J_right"] = "1/20"
    return {
        "paired_J_overlap": overlap,
        "q_not_above_half": bad_q,
        "J_crosses_alpha2": cross,
    }


def detect_production_fault(data: dict[str, Any], fault: str) -> str:
    """Inject a real checker arithmetic/ownership fault and require detection."""
    from checker import check_certificate, public_certificate
    from validator import validate_certificate

    if fault not in PRODUCTION_FAULTS:
        raise ValueError(f"unknown production fault: {fault}")
    try:
        report = check_certificate(data, test_fault=fault)
    except Exception as exc:
        print(f"MUTATION_REJECTED {fault} checker: {exc}")
        return "checker"
    artifact = public_certificate(report)
    try:
        validate_certificate(data, artifact)
    except Exception as exc:
        print(f"MUTATION_REJECTED {fault} validator: {exc}")
        return "validator"
    raise AssertionError(f"production mutation survived checker and validator: {fault}")


def _require_rejected(name: str, label: str, fn: Any, *args: Any) -> None:
    try:
        fn(*args)
    except Exception as exc:
        print(f"MUTATION_REJECTED {name} {label}: {exc}")
        return
    raise AssertionError(f"mutation survived: {name} {label}")


def main() -> None:
    from checker import check_certificate, public_certificate
    from validator import validate_certificate

    data = json.loads((ROOT / "primary_data.json").read_text())
    baseline = public_certificate(check_certificate(data))
    validate_certificate(data, baseline)  # healthy negative control

    rejection_assertions = 0
    for name, case in geometric_mutation_cases(data).items():
        _require_rejected(name, "checker", check_certificate, case)
        _require_rejected(name, "validator", validate_certificate, case, baseline)
        rejection_assertions += 2

    for fault in PRODUCTION_FAULTS:
        detect_production_fault(data, fault)
        rejection_assertions += 1

    coherent_w_tamper = copy.deepcopy(baseline)
    coherent_w_tamper["exact_rational_witness"] = baseline["implicit_upper"]
    coherent_w_tamper["exact_rational_witness_sha256"] = hashlib.sha256(
        coherent_w_tamper["exact_rational_witness"].encode("ascii")
    ).hexdigest()
    _require_rejected("witness_tamper", "validator", validate_certificate, data, coherent_w_tamper)
    rejection_assertions += 1

    sha_tamper = copy.deepcopy(baseline)
    sha_tamper["exact_rational_witness_sha256"] = "0" * 64
    _require_rejected("sha_tamper", "validator", validate_certificate, data, sha_tamper)
    rejection_assertions += 1

    old_q_tamper = copy.deepcopy(data)
    old_q_tamper["old_q"] = str(Q(0))
    _require_rejected("old_q_tamper", "checker", check_certificate, old_q_tamper)
    _require_rejected("old_q_tamper", "validator", validate_certificate, old_q_tamper, baseline)
    rejection_assertions += 2

    if rejection_assertions != 13:
        raise AssertionError(f"expected 13 rejection assertions, got {rejection_assertions}")
    print(json.dumps({
        "status": "ALL_MUTATIONS_REJECTED",
        "fault_families": 6,
        "binding_and_provenance_attacks": 3,
        "rejection_assertions": rejection_assertions,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
