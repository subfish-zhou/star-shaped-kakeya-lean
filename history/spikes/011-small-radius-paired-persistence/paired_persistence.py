#!/usr/bin/env python3
"""Formula and resource scouts for small-radius paired persistence.

The continuum proof is in THEOREM.md.  Floating quadrature here is SCOUT evidence;
exact Fraction arithmetic is used for the frozen CFS surrogate ordering.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction as Q
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
FROZEN = REPO / "spikes/007-cfs-rational-cert/frozen_schedule.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def kernel(u: float, radius: float) -> float:
    require(0 <= u <= radius, "require 0<=u<=radius")
    return u * (radius - u) / (radius + u) if u < radius else 0.0


def level_coefficient(H: float, u: float, radius: float) -> float:
    """Coefficient c(H,u,R) in |Q_u|* >= c |A|*."""
    require(0 <= H <= u <= radius, "require 0<=H<=u<=R")
    if u == 0 or u == radius:
        return 0.0 if u == radius else 2.0
    beta = math.asin(H / u)
    return 2.0 * (radius - u) / (radius + u) * (1.0 - 2.0 * beta / math.pi)


def old_fixed_cut_level(class_mass: float, H: float, u: float, radius: float) -> float:
    require(0 <= class_mass <= math.pi, "mass outside [0,pi]")
    require(0 <= H <= u <= radius, "require 0<=H<=u<=R")
    if u == radius:
        return 0.0
    return max(0.0, 2.0 * (radius - u) / (radius + u) * class_mass
               - 4.0 * math.asin(H / u))


def simpson(f: Callable[[float], float], a: float, b: float, n: int = 4096) -> float:
    require(a <= b and n >= 2, "invalid Simpson interval")
    if a == b:
        return 0.0
    if n % 2:
        n += 1
    step = (b - a) / n
    total = f(a) + f(b)
    total += 4.0 * sum(f(a + step * i) for i in range(1, n, 2))
    total += 2.0 * sum(f(a + step * i) for i in range(2, n, 2))
    return total * step / 3.0


def paired_payment(H: float, a: float, b: float, radius: float, n: int = 4096) -> float:
    """P(H;a,b,R)=integral_a^b u*c(H,u,R) du."""
    require(0 <= H <= a <= b <= radius, "require 0<=H<=a<=b<=R")
    if a == b:
        return 0.0
    return simpson(lambda u: u * level_coefficient(H, u, radius), a, b, n)


def primitive(u: float, radius: float) -> float:
    return -u * u / 2.0 + 2.0 * radius * u - 2.0 * radius * radius * math.log(radius + u)


def ledger(a: float, b: float, radius: float) -> float:
    require(0 <= a <= b <= radius, "invalid ledger interval")
    return primitive(b, radius) - primitive(a, radius)


def log_upper_ratio(y: Q, terms: int = 4) -> Q:
    require(y >= 1 and terms == 4, "frozen exact log contract")
    z = (y - 1) / (y + 1)
    partial = sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), Q(0))
    tail = z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return 2 * (partial + tail)


def ledger_lower(a: Q, b: Q, radius: Q) -> Q:
    require(0 <= a <= b <= radius, "invalid exact ledger interval")
    ratio = (radius + b) / (radius + a)
    return (-(b * b - a * a) / 2 + 2 * radius * (b - a)
            - 2 * radius * radius * log_upper_ratio(ratio))


def frozen_low_payments() -> tuple[dict, list[Q]]:
    data = json.loads(FROZEN.read_text(encoding="utf-8"))
    alpha = [Q(x) for x in data["alpha"]]
    radii = [Q(x) for x in data["R"]]
    switches = [Q(x) for x in data["t"]]
    payments: list[Q] = []
    for j in range(data["N"]):
        value = ledger_lower(alpha[j + 1], switches[1], radii[0])
        for i in range(1, j + 1):
            value += ledger_lower(switches[i], switches[i + 1], radii[i])
        payments.append(value)
    return data, payments


def resource_witness(H: float, q: float, epsilon: float) -> dict:
    """Sound first-cell CFS replacement plus disjoint inner paired payment.

    J=[alpha_1,alpha_1+epsilon] is replaced, not double charged.  On J the old
    R=1/2 action for D0 is replaced by the R_c action for D0\\N.
    """
    data, exact = frozen_low_payments()
    alpha = [float(Q(x)) for x in data["alpha"]]
    switches = [float(Q(x)) for x in data["t"]]
    a, a2, t = alpha[1], alpha[2], switches[1]
    require(0 < H < a < 1 - q, "need 0<H<alpha1<1-q")
    require(0 < epsilon <= a2 - a, "replacement must stay in first-cell-only slice")
    require(0.5 < q and t < q, "need complement reach beyond first window")
    complement_reach = min(math.hypot(0.5, H), q)
    require(t < complement_reach, "complement reach must cover first window")

    pair = paired_payment(H, H, a, 1 - q)
    loss = ledger(a, a + epsilon, 0.5)
    replacement = ledger(a, a + epsilon, complement_reach)
    gain = replacement - loss
    p0 = float(exact[0])
    untouched = min(float(x) for x in exact[1:])
    near = p0 - loss + pair
    complement = p0 + gain
    objective = min(near, complement, untouched)
    return {
        "H": H,
        "q": q,
        "epsilon": epsilon,
        "alpha1": a,
        "alpha2": a2,
        "first_switch": t,
        "common_paired_reach": 1 - q,
        "complement_reach": complement_reach,
        "paired_inner_coefficient": pair,
        "replacement_old_debit": loss,
        "replacement_complement_payment": replacement,
        "replacement_complement_gain": gain,
        "exact_surrogate_p0_float": p0,
        "exact_surrogate_untouched_floor_float": untouched,
        "near_column": near,
        "complement_column": complement,
        "resource_lp_objective": objective,
        "strictly_lifts_old_exact_surrogate_p0": objective > p0,
        "hits_untouched_floor": abs(objective - untouched) <= 5e-15,
        "supports": {
            "paired": [H, a],
            "replacement": [a, a + epsilon],
            "legacy_rest_starts": a + epsilon,
            "pair_replacement_overlap_length": 0.0,
        },
        "evidence": "PAPER theorem + FLOATING SCOUT; not an outward-rounded constant certificate",
    }


def swapped_arc_attack(h: float, u: float, radius: float) -> dict:
    require(0 < h <= u < radius, "need 0<h<=u<R")
    aR, au = math.asin(h / radius), math.asin(h / u)
    k = aR + au
    theta_plus, theta_minus = math.pi - k / 2, k / 2
    plus = (theta_plus + aR, theta_plus + au)
    minus = (theta_minus + math.pi - au, theta_minus + math.pi - aR)
    beta = au
    return {
        "endpoint_error": max(abs(plus[0] - minus[0]), abs(plus[1] - minus[1])),
        "both_projective_anchors_in_bad_beta_ball": max(k / 2, k / 2) <= beta,
        "beta": beta,
    }


def legal_alternating(N: int, m: int) -> dict:
    require(N >= 3 and N % 2 == 1 and m > 0 and m % 2 == 1 and m < N - 2,
            "N,m odd with 0<m<N-2")
    ell = math.pi / N
    angle = m * ell / 2
    require(angle + ell < math.pi / 2, "alternating geometry out of range")
    h = 0.5 * math.tan(angle)
    return {"N": N, "m": m, "h": h, "M": math.hypot(0.5, h),
            "anti_periodic": N % 2 == 1, "anti_shift": m % 2 == 1}


def report() -> dict:
    data, exact = frozen_low_payments()
    a = float(Q(data["alpha"][1]))
    # Frozen rational-looking scout parameters; no certification is claimed.
    witness = resource_witness(a / 2.0, 0.51, 0.0034)
    H, u, R, tiny = 0.01, 0.02, 0.49, 1e-6
    return {
        "status": "PAPER_LEVEL_PROPORTIONAL_THEOREM_SURVIVES",
        "formula": "2*(R-u)/(R+u)*(1-2*asin(H/u)/pi)",
        "old_absolute_TT_at_tiny_mass": old_fixed_cut_level(tiny, H, u, R),
        "new_proportional_TT_at_tiny_mass": level_coefficient(H, u, R) * tiny,
        "frozen_exact_first_class_is_unique_minimum": exact[0] < min(exact[1:]),
        "exact_first_to_second_surrogate_gap_float": float(min(exact[1:]) - exact[0]),
        "resource_witness": witness,
        "swapped_track_attack": swapped_arc_attack(0.02, 0.30, 0.49),
        "alternating_control": legal_alternating(10001, 101),
        "warnings": [
            "quadrature and displayed LP objective are scouting only",
            "strict structural lift is analytic; no new advertised universal decimal is certified",
            "the first-cell action is replacement, never simultaneous R+paired charging",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/scout.json")
    args = parser.parse_args()
    out = report()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
