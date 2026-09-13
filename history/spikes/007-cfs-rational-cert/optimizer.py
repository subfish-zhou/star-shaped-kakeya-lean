#!/usr/bin/env python3
"""Numerical N=64 scout and conservative rationaliser.

The floating solve is only a schedule finder.  `frozen_schedule.json` is the
proof object and must pass both exact_certificate.py and the independently
implemented atom validator.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import brentq, minimize

ROOT = Path(__file__).resolve().parent
DEN = 10**9
OLD32 = np.array([
    0, 27226, 38590, 47324, 54682, 61151, 66981, 72321, 77266,
    81884, 86225, 90323, 94208, 97900, 101419, 104778, 107987,
    111058, 113996, 116807, 119496, 122066, 124519, 126854,
    129071, 131166, 133135, 134969, 136656, 138174, 139487,
    140523, 141046,
], dtype=float) / 10**6


def primitive(u: float, radius: float) -> float:
    return -u * u / 2 + 2 * radius * u - 2 * radius * radius * math.log(radius + u)


def integral(a: float, b: float, radius: float) -> float:
    return primitive(b, radius) - primitive(a, radius)


def backward_schedule(alpha: np.ndarray):
    n = len(alpha) - 1
    radii = np.sqrt(0.25 + alpha[:-1] ** 2)
    radii[0] = 0.5
    switches = np.empty(n + 1)
    switches[n] = radii[n - 1]
    for j in range(n - 1, 0, -1):
        mass = integral(alpha[j], alpha[j + 1], 0.5)
        hi = switches[j + 1]
        fn = lambda x: integral(x, hi, radii[j]) - mass
        if fn(0.0) < 0:
            return None
        switches[j] = brentq(fn, 0.0, hi, xtol=1e-14, rtol=1e-14)
    switches[0] = alpha[1]
    if switches[1] < alpha[-1] or np.any(np.diff(switches) <= 0):
        return None
    return integral(alpha[1], switches[1], 0.5), radii, switches


def unpack(log_ratios: np.ndarray, eta: float) -> np.ndarray:
    z = np.r_[log_ratios, 0.0]
    z -= z.max()
    widths = np.exp(z)
    widths /= widths.sum()
    return np.r_[0.0, eta * np.cumsum(widths)]


def scout(n: int = 64, eta: float = 0.141089985239328):
    alpha0 = np.interp(np.linspace(0, 1, n + 1), np.linspace(0, 1, 33), OLD32)
    alpha0 *= eta / alpha0[-1]
    widths = np.diff(alpha0) / eta
    z0 = np.log(widths[:-1] / widths[-1])

    def objective(z):
        result = backward_schedule(unpack(z, eta))
        return 1.0 if result is None else -result[0]

    fit = minimize(objective, z0, method="L-BFGS-B",
                   options={"maxiter": 500, "ftol": 1e-15, "gtol": 1e-10, "maxls": 50})
    alpha = unpack(fit.x, eta)
    payment, radii, switches = backward_schedule(alpha)
    return {
        "status": "NUMERIC_LOCAL_CANDIDATE",
        "success": bool(fit.success),
        "message": fit.message,
        "iterations": int(fit.nit),
        "eta": eta,
        "objective": min(eta / 2, math.pi * payment),
        "low_payment": payment,
        "alpha": alpha.tolist(),
        "R": radii.tolist(),
        "t": switches.tolist(),
    }


def nearest(x: float) -> int:
    return int(math.floor(x * DEN + 0.5))


def rationalise(candidate: dict) -> dict:
    eta_num = nearest(candidate["eta"])
    alpha_num = [nearest(x) for x in candidate["alpha"]]
    alpha_num[0], alpha_num[-1] = 0, eta_num
    # Exact downward cap: floor(D*sqrt(1/4+(a/D)^2)).
    radius_num = [math.isqrt((DEN // 2) ** 2 + a * a) for a in alpha_num[:-1]]
    radius_num[0] = DEN // 2
    switch_num = [nearest(x) for x in candidate["t"]]
    switch_num[0] = alpha_num[1]
    switch_num[-1] = radius_num[-1]
    # Safety against a one-ulp scout rounding at a cap.
    for j in range(len(radius_num)):
        switch_num[j + 1] = min(switch_num[j + 1], radius_num[j])
    radical_lower_num = math.isqrt(DEN * DEN + eta_num * eta_num)

    def s(num: int) -> str:
        from fractions import Fraction
        value = Fraction(num, DEN)
        return f"{value.numerator}/{value.denominator}"

    return {
        "schema": "cfs-index-closed-rational-schedule-v1",
        "evidence": "EXACT_RATIONAL_WITNESS; optimizer row is NUMERIC only",
        "N": 64,
        "eta": s(eta_num),
        "target": "3527/50000",
        "common": "44909/2000000",
        "pi_lower": "333/106",
        "log_terms": 4,
        "alpha": [s(x) for x in alpha_num],
        "R": [s(x) for x in radius_num],
        "t": [s(x) for x in switch_num],
        "high_tail": {
            "tail_start": 0,
            "band_step": "1/2",
            "sqrt_one_plus_eta_sq_lower": s(radical_lower_num),
            "contract": "symbolic_all_real_A_ge_eta_hence_all_integer_k_ge_0",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, help="rationalise an existing numeric candidate")
    parser.add_argument("--write-frozen", action="store_true")
    args = parser.parse_args()
    if args.candidate:
        candidate = json.loads(args.candidate.read_text())
    else:
        candidate = scout()
        (ROOT / "numeric_scout.json").write_text(json.dumps(candidate, indent=2) + "\n")
    frozen = rationalise(candidate)
    if args.write_frozen:
        (ROOT / "frozen_schedule.json").write_text(json.dumps(frozen, indent=2) + "\n")
    summary = {k: candidate[k] for k in ("status", "objective", "low_payment") if k in candidate}
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
