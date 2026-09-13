"""Twelve preregistered exact controls; no optimization, no file writes.

Only standard-library Fraction arithmetic. Geometry/continuum claims remain
human proofs; the sharper ratio kernel here is explicitly CONDITIONAL.
"""
from fractions import Fraction as F
import json
import time


def require(ok, message):
    if not ok:
        raise ValueError(message)


def affine_weighted(c, d, a, b):
    """Integral min(r,1)*(c+d*r) on 0<=a<=b, split exactly at 1."""
    require(F(0) <= a <= b, "integration order")
    cuts = sorted({a, b} | ({F(1)} if a < 1 < b else set()))
    result = F(0)
    for u, v in zip(cuts, cuts[1:]):
        if v <= 1:
            result += c*(v*v-u*u)/2 + d*(v**3-u**3)/3
        else:
            result += c*(v-u) + d*(v*v-u*u)/2
    return result


def collar(s, a, b):
    """Integral w(r)*min(1/2,(s-r)_+), with support clipping."""
    a, b = max(F(0), a), min(s, b)
    if a >= b:
        return F(0)
    cut = s-F(1, 2)
    result = F(0)
    if a < min(b, cut):
        result += affine_weighted(F(1, 2), F(0), a, min(b, cut))
    if max(a, cut) < b:
        result += affine_weighted(s, F(-1), max(a, cut), b)
    return result


def tail_formula(R):
    require(R > F(1, 2), "terminal theorem requires R>1/2")
    if R <= 1:
        return R*R/24
    if R <= F(3, 2):
        return (-8*R**3+33*R**2-30*R+9)/(96*R)
    if R <= 2:
        return (-R*R+8*R-6)/(32*R)
    return F(1, 8)-1/(16*R)


def ratio(m, upper, a, b):
    """Conditional inf endpoint ratio for these fixed domains (upper>=m+1/2).

    On r<m: min(q,(m-r)/m), q=1/(2*upper). No theorem asserted.
    """
    require(upper >= m+F(1, 2), "ratio fixed-domain guard")
    a, b = max(F(0), a), min(m, b)
    if a >= b:
        return F(0)
    q = 1/(2*upper)
    split = m*(1-q)
    result = F(0)
    if a < min(b, split):
        result += affine_weighted(q, F(0), a, min(b, split))
    if max(a, split) < b:
        result += affine_weighted(F(1), -1/m, max(a, split), b)
    return result


def main():
    start = time.monotonic()
    out = []
    fixed = (F(3, 4), F(1), F(5, 4), F(3, 2), F(8, 5), F(2), F(5, 2), F(3))
    for number, R in enumerate(fixed, 1):
        exact = collar(R, R/2, R)/(2*R)
        require(exact == tail_formula(R), "tail piecewise identity")
        require((exact >= F(1, 10)) == (R >= F(5, 2)), "tail cutoff")
        row = {"control": number, "R": str(R), "fresh_tail": str(exact)}
        if R == F(8, 5):
            require(exact == F(53, 640), "baseline first tail changed")
        if R == 3:
            rho = F(1, 10)/exact
            require(rho == F(24, 25), "constant tail reserve")
            row["tail_price_for_one_tenth"] = str(rho)
        out.append(row)
    R = F(5, 2)
    require(collar(R, F(3), F(4)) == 0, "empty clipped band")
    require(collar(R, F(0), F(3)) == collar(R, F(0), R), "upper truncation")
    out.append({"control": 9, "truncation": "PASS", "whole_tail_kernel": str(collar(R, F(0), R)/(2*R))})
    m = F(99, 100)
    old = collar(m, F(0), m)/R
    q = 1/(2*R)
    joint = ratio(m, R, F(0), m)
    require(joint == m*m*q*(q*q-3*q+3)/6, "conditional ratio primitive")
    reserved = ratio(m, R, F(1, 2), m)
    require(old < F(1, 10) and joint < F(1, 10), "full high ceilings")
    require(R-1 > m, "old endpoint window obstruction")
    low_mass = F(1, 8)
    high_mass = (m*m-F(1, 4))/2
    out.append({"control": 10, "old_full_high": str(old), "conditional_ratio_full_high": str(joint),
                "conditional_ratio_high_after_half": str(reserved),
                "low_required_weighted_mean_K": str(F(1, 10)/low_mass),
                "high_required_weighted_mean_K": str(F(1, 10)/high_mass),
                "conditional_ratio_residual_multiplier_needed": str(F(1, 10)/reserved)})
    # Fixed two-tier all-ones dual. K1 >= K2 precisely below r=4m/5;
    # then K2 is the upper envelope until the reserved tail begins at 5/4.
    cut = 4*m/5
    envelope = ratio(m, F(3, 2), F(0), cut) + ratio(F(3, 2), R, cut, F(5, 4))
    require(envelope < F(1, 5), "two-tier all-ones source obstruction")
    out.append({"control": 11, "conditional_two_tier_envelope": str(envelope),
                "required_two_tier_sum": "1/5", "deficit": str(F(1, 5)-envelope)})
    R, a = F(8, 5), F(5, 8)
    early = collar(R, a, R)/(2*R)
    require(early == (85-50*a*a)/640, "early tail primitive")
    require(early > F(1, 10), "early tail alternative")
    threshold_squared = (F(85)-640*F(1, 10))/50
    require(threshold_squared == F(21, 50), "early tail threshold")
    out.append({"control": 12, "early_tail_at_5_over_8": str(early),
                "maximum_prefix_cut_squared": str(threshold_squared)})
    require(len(out) == 12, "fixed control count")
    print(json.dumps({"status": "PASS", "controls": out,
                      "arithmetic_wall_seconds": time.monotonic()-start,
                      "scope": "exact arithmetic only; conditional ratios are not proved union kernels"}, indent=2))


if __name__ == "__main__":
    main()
