#!/usr/bin/env python3
"""Exact Fraction certificate for one frozen finite C_FS schedule.

This checker derives every low payment from the index-closed schedule and uses
an explicit positive atanh-series tail to upper-bound each logarithm.
"""
from __future__ import annotations

from fractions import Fraction as Q
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
LOG_TERMS = 4
PI_LOWER = Q(333, 106)


def require(name: str, condition: bool) -> None:
    if not condition:
        raise ValueError(name)


def q(value: str) -> Q:
    return Q(value)


def log_upper_ratio(y: Q, terms: int) -> Q:
    require("fixed positive log truncation", terms == LOG_TERMS)
    require("log direction", y >= 1)
    z = (y - 1) / (y + 1)
    require("atanh domain", 0 <= z < 1)
    partial = sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), Q(0))
    tail = z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return 2 * (partial + tail)


def ledger_lower(a: Q, b: Q, radius: Q, terms: int) -> Q:
    require("ledger interval", 0 <= a <= b <= radius)
    ratio = (radius + b) / (radius + a)
    return (-(b * b - a * a) / 2 + 2 * radius * (b - a)
            - 2 * radius * radius * log_upper_ratio(ratio, terms))


def high_tail_contract(data: dict[str, Any], common: Q) -> Q:
    """Uniform lower bound for every high band k>=0, not a finite sample.

    Put A=eta+k/2, B=A+1/2 and d=sqrt(1+eta^2)-eta.  The frozen
    rational r0 is a strict lower bound for sqrt(1+eta^2).  For all A>=eta,
    sqrt(A^2-eta^2) >= d(A-eta), since d<1 and
    A+eta >= d^2(A-eta).  Hence R_eta(A)>=A+d.  Also R_eta(A)<A+1.
    Thus width R-B >= d-1/2 and B/(R+B) is bounded below by its k=0
    rational value.  Integrating the triangular (R-u) lower bound proves the
    returned coefficient for the complete infinite tail.
    """
    eta = q(data["eta"])
    contract = data["high_tail"]
    require("tail starts at zero", contract["tail_start"] == 0)
    r0 = q(contract["sqrt_one_plus_eta_sq_lower"])
    require("eta range", 0 < eta < Q(1, 2))
    require("radical lower", r0 * r0 < 1 + eta * eta)
    d0 = r0 - eta
    require("tail width", Q(1, 2) < d0 < 1)
    # Exact symbolic side conditions used for every real A>=eta.
    require("tail slope", d0 * d0 <= 1)
    require("tail eta sign", eta >= 0)
    require("tail reach", 1 - d0 * d0 - 2 * eta * d0 > 0)
    width = d0 - Q(1, 2)
    factor = (eta + Q(1, 2)) / (2 * eta + Q(3, 2))
    high = factor * width * width / 2
    require("high payment", high > common)
    return high


def certify(data: dict[str, Any]) -> dict[str, Any]:
    alpha = [q(x) for x in data["alpha"]]
    radii = [q(x) for x in data["R"]]
    switches = [q(x) for x in data["t"]]
    eta, target, common = q(data["eta"]), q(data["target"]), q(data["common"])
    pi_lower = q(data["pi_lower"])
    terms = int(data["log_terms"])
    n = int(data["N"])

    require("64 classes", n == 64)
    require("log_terms contract", terms == LOG_TERMS)
    require("pi_lower contract", pi_lower == PI_LOWER)
    require("index closure", len(alpha) == n + 1 and len(radii) == n and len(switches) == n + 1)
    require("partition endpoints", alpha[0] == 0 and alpha[-1] == eta)
    require("partition order", all(alpha[j] < alpha[j + 1] for j in range(n)))
    require("R0", radii[0] == Q(1, 2))
    require("radius order", all(radii[j] <= radii[j + 1] for j in range(n - 1)))
    require("geometry", all(radii[j] * radii[j] <= Q(1, 4) + alpha[j] * alpha[j] for j in range(n)))
    require("t0", switches[0] == alpha[1])
    require("switch order", all(switches[j] < switches[j + 1] for j in range(n)))
    require("first long window", switches[1] >= eta)
    require("window caps", all(switches[j + 1] <= radii[j] for j in range(n)))
    require("low high separation", switches[-1] < eta + Q(1, 2))

    payments: list[Q] = []
    for j in range(n):
        payment = ledger_lower(alpha[j + 1], switches[1], radii[0], terms)
        for i in range(1, j + 1):
            payment += ledger_lower(switches[i], switches[i + 1], radii[i], terms)
        require(f"payment {j}", payment > common)
        payments.append(payment)

    high = high_tail_contract(data, common)
    require("height branch", eta / 2 > target)
    require("pi branch", common * pi_lower > target)
    require("strict improvement", target > Q(141, 2000))
    return {
        "witness": target,
        "common": common,
        "minimum_low_payment": min(payments),
        "minimum_low_class": payments.index(min(payments)),
        "high_payment_lower": high,
        "height_margin": eta / 2 - target,
        "pi_margin": common * pi_lower - target,
        "low_margin": min(payments) - common,
    }


def compact(result: dict[str, Any]) -> dict[str, Any]:
    return {key: (f"{value.numerator}/{value.denominator}" if isinstance(value, Q) else value)
            for key, value in result.items()}


def main() -> None:
    data = json.loads((ROOT / "frozen_schedule.json").read_text())
    result = certify(data)
    output = compact(result) | {"status": "C_FS_RATIONAL_CERTIFICATE_OK"}
    (ROOT / "exact_result.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
