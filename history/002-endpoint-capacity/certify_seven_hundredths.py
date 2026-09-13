#!/usr/bin/env python3
"""Exact rational certificate for the universal 7/100 radial-schedule bound.

All decisions use fractions. Logarithms are bounded above by the positive
atanh series, giving rigorous lower bounds for the radial ledger integrals.
"""

from fractions import Fraction as Q
import json
import math
from pathlib import Path


def require(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)


def log_upper_ratio(y: Q, terms: int = 3) -> Q:
    """Upper bound log(y), y>=1, using z=(y-1)/(y+1)."""
    require("log argument", y >= 1)
    z = (y - 1) / (y + 1)
    require("atanh range", 0 <= z < 1)
    partial = sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), Q(0))
    tail = z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return 2 * (partial + tail)


def ledger_lower(a: Q, b: Q, R: Q) -> Q:
    """Lower bound integral_a^b u(R-u)/(R+u) du for 0<=a<=b<=R."""
    require("ledger interval", 0 <= a <= b <= R)
    log_upper = log_upper_ratio((R + b) / (R + a))
    return -(b * b - a * a) / 2 + 2 * R * (b - a) - 2 * R * R * log_upper


def qstr(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"


def main() -> None:
    eta = Q(7, 50)
    area_target = Q(7, 100)

    # pi > 333/106 gives 7/(100*pi) < 371/16650.
    common = Q(371, 16650)
    require("common coefficient identity", common == eta * Q(53, 333))

    # Low-m schedule. Classes L_j have 7j/400 < m <= 7(j+1)/400.
    radii = [
        Q(1, 2), Q(5003, 10000), Q(1253, 2500), Q(5027, 10000),
        Q(631, 1250), Q(203, 400), Q(5109, 10000), Q(5147, 10000),
    ]
    endpoints = [
        Q(7, 400), Q(671, 2000), Q(3419, 10000), Q(44, 125),
        Q(3661, 10000), Q(3841, 10000), Q(163, 400),
        Q(1098, 2500), Q(5147, 10000),
    ]
    require("low schedule starts at first class cap", endpoints[0] == Q(7, 400))
    require("window radii increasing", all(radii[i] < radii[i + 1] for i in range(7)))
    require("low schedule ordered", all(endpoints[i] < endpoints[i + 1] for i in range(8)))
    require("each radial interval below its window radius",
            all(endpoints[k + 1] <= radii[k] for k in range(8)))

    low_rows = []
    for j in range(8):
        a_j = Q(7 * j, 400)
        b_j = Q(7 * (j + 1), 400)
        # Geometry: M^2 >= 1/4+m^2 > 1/4+a_j^2 >= R_j^2.
        geometry_margin = Q(1, 4) + a_j * a_j - radii[j] * radii[j]
        require(f"geometry radius {j}", geometry_margin >= 0)

        payment = ledger_lower(max(b_j, endpoints[0]), endpoints[1], radii[0])
        for k in range(1, j + 1):
            payment += ledger_lower(max(b_j, endpoints[k]), endpoints[k + 1], radii[k])
        margin = payment - common
        require(f"low payment {j}", margin > 0)
        low_rows.append({
            "j": j,
            "m_upper": qstr(b_j),
            "radius": qstr(radii[j]),
            "geometry_margin": qstr(geometry_margin),
            "payment_lower": qstr(payment),
            "margin_over_common": qstr(margin),
            "payment_decimal": float(payment),
        })

    # High-m half-unit bands. R(a)<a+1, D(a)=R(a)-a is increasing.
    # At a0=eta, R0=sqrt(1+eta^2)>1009/1000, b0=eta+1/2=16/25,
    # hence every ledger width exceeds 369/1000. Also
    # b/(R+b) > (a+1/2)/(2a+3/2), increasing in a, with minimum 32/89.
    r0_sq = 1 + eta * eta
    r0_lower = Q(1009, 1000)
    b0 = eta + Q(1, 2)
    require("R0 rational lower square", r0_sq > r0_lower ** 2)
    width = r0_lower - b0
    require("high width identity", width == Q(369, 1000))
    factor = (eta + Q(1, 2)) / (2 * eta + Q(3, 2))
    require("high factor identity", factor == Q(32, 89))
    high_lower = factor * width * width / 2
    high_margin = high_lower - common
    require("high uniform lower", high_margin > 0)
    require("low-high radial separation", endpoints[-1] < b0)

    # Final comparisons.
    pi_lower = Q(333, 106)
    require("final pi product identity", common * pi_lower == area_target)
    gain_over_previous = area_target - Q(1717, 25000)
    require("gain identity", gain_over_previous == Q(33, 25000))
    require("gain positive", gain_over_previous > 0)

    result = {
        "parameters": {
            "eta": qstr(eta),
            "area_target": qstr(area_target),
            "common_direction_coefficient": qstr(common),
            "pi_lower_used": qstr(pi_lower),
            "log_terms": 3,
        },
        "low_schedule": {
            "radii": [qstr(x) for x in radii],
            "endpoints": [qstr(x) for x in endpoints],
            "rows": low_rows,
            "minimum_margin_decimal": min(row["payment_decimal"] - float(common) for row in low_rows),
        },
        "high_schedule": {
            "width_lower": qstr(width),
            "factor_lower": qstr(factor),
            "coefficient_lower": qstr(high_lower),
            "margin_over_common": qstr(high_margin),
        },
        "final": {
            "gain_over_1717_25000": qstr(gain_over_previous),
            "area_target_decimal": float(area_target),
            "relative_gain_over_1717_25000": float(area_target / Q(1717, 25000) - 1),
        },
        "status": "SEVEN_HUNDREDTHS_CERTIFICATE_OK",
    }

    out = Path(__file__).with_name("seven_hundredths_certificate.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    print("SEVEN_HUNDREDTHS_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
