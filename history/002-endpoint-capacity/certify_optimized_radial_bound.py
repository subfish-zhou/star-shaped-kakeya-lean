#!/usr/bin/env python3
"""Exact certificate for the optimized universal radial-sliver bound.

Proves the frozen rational comparisons for eta = 1717/12500 and the final
bound area >= eta/2 = 1717/25000.  No floating-point arithmetic is used for
certificate decisions.
"""

from fractions import Fraction as Q
import json
import math
from pathlib import Path


def require(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)


def main() -> None:
    eta = Q(1717, 12500)
    target = eta / 2

    # Low ledger.  log(y)=2*sum z^(2j+1)/(2j+1), with the tail bounded by
    # 2*z^7/(7*(1-z^2)).
    y = Q(2) / (1 + 2 * eta)
    z = (y - 1) / (y + 1)
    require("y identity", y == Q(12500, 7967))
    require("z identity", z == Q(4533, 20467))
    require("z range", 0 < z < 1)
    log_upper = 2 * (z + z**3 / 3 + z**5 / 5
                     + z**7 / (7 * (1 - z**2)))
    require(
        "log upper identity",
        log_upper
        == Q(
            2255392730789667442828102686477,
            5007302326850532853032257075000,
        ),
    )
    low_lower = Q(3, 8) - eta + eta**2 / 2 - log_upper / 2
    require(
        "low lower identity",
        low_lower
        == Q(
            1368465910852584744183198399925437,
            62591279085631660662903213437500000,
        ),
    )

    # pi > 333/106 implies eta/(2*pi) < 53*eta/333.
    common_coeff = 53 * eta / 333
    require("common coeff identity", common_coeff == Q(91001, 4162500))
    low_margin = low_lower - common_coeff
    require(
        "low margin identity",
        low_margin
        == Q(
            29629268185379654216641093095521,
            20842895935515343000746770074687500000,
        ),
    )
    require("low margin positive", low_margin > 0)

    # First high ledger: rational enclosure of R0=sqrt(1+eta^2).
    r0_sq = 1 + eta**2
    r0_lower = Q(50469, 50000)
    r0_upper = Q(100939, 100000)
    require("R0 lower square", r0_sq - r0_lower**2 == Q(49463, 2500000000))
    require("R0 upper square", r0_upper**2 - r0_sq == Q(161, 400000000))
    b0 = eta + Q(1, 2)
    width = r0_lower - b0
    require("width identity", width == Q(18601, 50000))
    require("width positive", width > 0)

    c0_lower = b0 / (r0_upper + b0) * width**2 / 2
    require("C0 lower identity", c0_lower == Q(2756559700367, 102921875000000))
    c0_margin = c0_lower - common_coeff
    require(
        "C0 margin identity",
        c0_margin == Q(168654896472211, 34272984375000000),
    )
    require("C0 margin positive", c0_margin > 0)

    # Every k>=1: the rational factor is minimized at a1=eta+1/2.
    factor = (eta + 1) / (2 * eta + Q(5, 2))
    require("high factor identity", factor == Q(14217, 34684))
    high_lower = factor * width**2 / 2
    require(
        "high lower identity",
        high_lower == Q(4919042206617, 173420000000000),
    )
    high_margin = high_lower - common_coeff
    require(
        "high margin identity",
        high_margin == Q(375529581203461, 57748860000000000),
    )
    require("high margin positive", high_margin > 0)

    # Compare against the previous 131*pi/6250 using pi < 355/113.
    previous_upper = Q(131, 6250) * Q(355, 113)
    final_margin = target - previous_upper
    require("final margin identity", final_margin == Q(8001, 2825000))
    require("final margin positive", final_margin > 0)
    relative_gain_lower = final_margin / previous_upper
    require("relative gain identity", relative_gain_lower == Q(8001, 186020))

    result = {
        "eta": f"{eta.numerator}/{eta.denominator}",
        "area_bound": f"{target.numerator}/{target.denominator}",
        "exact": {
            "log_upper": f"{log_upper.numerator}/{log_upper.denominator}",
            "low_lower": f"{low_lower.numerator}/{low_lower.denominator}",
            "common_coefficient_upper": f"{common_coeff.numerator}/{common_coeff.denominator}",
            "low_margin": f"{low_margin.numerator}/{low_margin.denominator}",
            "ledger_width_lower": f"{width.numerator}/{width.denominator}",
            "C0_lower": f"{c0_lower.numerator}/{c0_lower.denominator}",
            "C0_margin": f"{c0_margin.numerator}/{c0_margin.denominator}",
            "high_lower": f"{high_lower.numerator}/{high_lower.denominator}",
            "high_margin": f"{high_margin.numerator}/{high_margin.denominator}",
            "margin_over_131pi6250_using_pi_lt_355_113": f"{final_margin.numerator}/{final_margin.denominator}",
            "relative_gain_lower": f"{relative_gain_lower.numerator}/{relative_gain_lower.denominator}",
        },
        "diagnostic": {
            "area_bound": float(target),
            "previous_lower": 131 * math.pi / 6250,
            "relative_gain_actual": float(target) / (131 * math.pi / 6250) - 1,
            "mechanism_numeric_ceiling": 0.06868430842034249,
            "gap_to_numeric_ceiling": 0.06868430842034249 - float(target),
        },
        "status": "OPTIMIZED_RADIAL_BOUND_CERTIFICATE_OK",
    }

    out = Path(__file__).with_name("optimized_radial_bound_certificate.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    print("OPTIMIZED_RADIAL_BOUND_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
