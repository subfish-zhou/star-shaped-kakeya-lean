#!/usr/bin/env python3
"""Exact arithmetic certificate for UNIVERSAL-ONE-FIFTEENTH.md.

This checks the frozen rational comparisons.  Decimal integral evaluations are
high-precision diagnostics, not interval proofs.
"""

from fractions import Fraction as Q
import json
import math
from pathlib import Path


def require(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)


def integrate_weighted_chord(x0: Q, x1: Q) -> Q:
    """Integrate (1/2-u)L(u), where L chords f(u)=u/(1/2+u)."""
    y0 = x0 / (Q(1, 2) + x0)
    y1 = x1 / (Q(1, 2) + x1)
    slope = (y1 - y0) / (x1 - x0)
    intercept = y0 - slope * x0

    def primitive(u: Q) -> Q:
        # (1/2-u)(slope*u+intercept)
        return (-slope * u**3 / 3
                + (slope / 2 - intercept) * u**2 / 2
                + intercept * u / 2)

    return primitive(x1) - primitive(x0)


def main() -> None:
    # Derive the low-ledger piecewise chord integrals from the frozen breakpoints.
    x0, x1, x2 = Q(2, 15), Q(19, 60), Q(1, 2)
    low_piece_1 = integrate_weighted_chord(x0, x1)
    low_piece_2 = integrate_weighted_chord(x1, x2)
    require("low piece 1", low_piece_1 == Q(12221, 837900))
    require("low piece 2", low_piece_2 == Q(605, 84672))
    low_total = low_piece_1 + low_piece_2
    require("low total identity", low_total == Q(873983, 40219200))
    require("low exceeds common rational threshold", low_total > Q(10, 471))

    # sqrt(229)/15 brackets and their exact consequences for k=0.
    eta, b0 = Q(2, 15), Q(19, 30)
    r0_sq = Q(229, 225)
    r0_upper, r0_lower = Q(101, 100), Q(121, 120)
    require("R0 upper square", r0_sq < r0_upper**2)
    require("R0 lower square", r0_sq > r0_lower**2)
    require("R0 width consequence", r0_lower - b0 == Q(3, 8))
    ratio0_lower = b0 / r0_upper
    require("R0 ratio consequence", ratio0_lower == Q(190, 303))

    c0_lower = ratio0_lower * Q(3, 8) ** 2 / 4
    require("C0 lower identity", c0_lower == Q(285, 12928))
    require("C0 exceeds threshold", c0_lower > Q(10, 471))

    # For k>=1, (a+1/2)/(a+1) is increasing; its first value is 34/49.
    a1 = eta + Q(1, 2)
    ratio_k_lower = (a1 + Q(1, 2)) / (a1 + 1)
    require("Ck ratio lower identity", ratio_k_lower == Q(34, 49))
    ck_lower = ratio_k_lower * Q(3, 8) ** 2 / 4
    require("Ck lower identity", ck_lower == Q(153, 6272))
    require("Ck exceeds threshold", ck_lower > Q(10, 471))

    # pi > 333/106 implies 1/(15*pi) < 106/4995 < 10/471.
    pi_recip_upper = Q(106, 4995)
    require("strong rational pi-chain", Q(10, 471) > pi_recip_upper)

    # Final comparison with the previous lower bound, using pi < 22/7.
    old_upper_using_22_7 = Q(131, 6250) * Q(22, 7)
    final_margin = Q(1, 15) - old_upper_using_22_7
    require("final margin identity", final_margin == Q(52, 65625))
    require("final margin positive", final_margin > 0)

    # High-precision floating diagnostics with the runtime libm.
    eta = 2.0 / 15.0

    def primitive(u: float, R: float) -> float:
        return -u * u / 2.0 + 2.0 * R * u - 2.0 * R * R * math.log(R + u)

    def coeff(b: float, R: float) -> float:
        return primitive(R, R) - primitive(b, R)

    cminus = coeff(eta, 0.5)
    rows = []
    for k in range(8):
        a = eta + k / 2.0
        b = a + 0.5
        R = math.sqrt(a * a + 1.0 + 2.0 * math.sqrt(max(0.0, a * a - eta * eta)))
        rows.append({"k": k, "a": a, "b": b, "R": R, "width": R - b, "coefficient": coeff(b, R)})

    result = {
        "exact": {
            "low_total": f"{low_total.numerator}/{low_total.denominator}",
            "common_threshold": "10/471",
            "c0_lower": f"{c0_lower.numerator}/{c0_lower.denominator}",
            "ck_lower": f"{ck_lower.numerator}/{ck_lower.denominator}",
            "final_margin_using_pi_lt_22_over_7": f"{final_margin.numerator}/{final_margin.denominator}",
        },
        "diagnostic": {
            "one_over_15": 1.0 / 15.0,
            "old_lower": 131.0 * math.pi / 6250.0,
            "relative_gain": (1.0 / 15.0) / (131.0 * math.pi / 6250.0) - 1.0,
            "Cminus": cminus,
            "one_over_15pi": 1.0 / (15.0 * math.pi),
            "high_ledgers": rows,
        },
        "status": "ONE_FIFTEENTH_CERTIFICATE_OK",
    }

    out = Path(__file__).with_name("one_fifteenth_certificate.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    print("ONE_FIFTEENTH_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
