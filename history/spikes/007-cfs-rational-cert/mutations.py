#!/usr/bin/env python3
"""Required fail-closed mutations for the independent validator."""
from __future__ import annotations

import copy
import json
from fractions import Fraction as Q
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent


def fs(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"


def mutation_cases(data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    radius = copy.deepcopy(data)
    # Reverse one radius step while retaining syntactically valid rationals.
    radius["R"][10] = fs(Q(radius["R"][11]) + Q(1, 10**9))

    tail = copy.deepcopy(data)
    tail["high_tail"]["tail_start"] = 1

    overlap = copy.deepcopy(data)
    overlap["t"][2] = overlap["t"][1]

    bad_log_terms = copy.deepcopy(data)
    bad_log_terms["log_terms"] = -1

    bad_pi = copy.deepcopy(data)
    bad_pi["pi_lower"] = "22/7"

    return {
        "radius_direction": radius,
        "missing_tail_band": tail,
        "radial_overlap": overlap,
        "negative_log_terms": bad_log_terms,
        "unsafe_pi_lower": bad_pi,
    }


def main() -> None:
    from independent_validator import ValidationError, validate
    data = json.loads((ROOT / "frozen_schedule.json").read_text())
    for name, mutation in mutation_cases(data).items():
        try:
            validate(mutation)
        except ValidationError as exc:
            print(f"MUTATION_REJECTED {name}: {exc}")
        else:
            raise AssertionError(f"mutation survived: {name}")


if __name__ == "__main__":
    main()
