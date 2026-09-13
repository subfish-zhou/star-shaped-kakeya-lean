#!/usr/bin/env python3
"""Numerical scout for a joint inside/outside lower-bound route.

Evidence level: numerical spike only.  The objective assumes the proposed
annular payment lemma and must not be quoted as a theorem.
"""
from __future__ import annotations

import json
import math
import time
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq, differential_evolution, minimize

OUT = Path(__file__).with_name("result.json")
EPS = 1e-10
M = 1.0 - EPS


def geometry(a: float, rl: float) -> dict:
    rad = 4.0 * rl * rl * (1.0 + a * a) - a * a
    if rad < 0.0:
        return {"valid": False, "radicand": rad}
    d = a * (1.0 - math.sqrt(rad)) / (2.0 * (1.0 + a * a))
    inner = rl * rl - d * d
    if inner <= 0.0:
        return {"valid": False, "radicand": rad, "d": d, "inner": inner}
    den = 1.0 - 2.0 * math.sqrt(inner)
    if den <= 0.0:
        return {"valid": False, "radicand": rad, "d": d, "inner": inner, "den": den}
    R1 = math.sqrt(1.0 + 4.0 * d * d) / den
    rho = R1 - 1.0
    return {
        "valid": True,
        "radicand": rad,
        "d": d,
        "inner": inner,
        "den": den,
        "R1": R1,
        "rho": rho,
    }


def branches(r: float, rl: float) -> tuple[float, float, float]:
    return (
        (1.0 + 2.0 * r) / (1.0 - 2.0 * r),
        (1.0 + 2.0 * rl) / (1.0 - 2.0 * rl),
        math.pi / (math.pi / 2.0 - math.atan(2.0 * r)),
    )


def integral_and_switches(a: float, rl: float, r0: float) -> tuple[float, list[float]]:
    def integrand(r: float) -> float:
        return r / max(branches(r, rl))

    grid = np.linspace(a, r0, 1201)
    active = np.argmax(np.asarray([branches(float(r), rl) for r in grid]), axis=1)
    changes = np.where(active[1:] != active[:-1])[0]
    roots: list[float] = []
    for j in changes:
        lo, hi = float(grid[j]), float(grid[j + 1])
        old, new = int(active[j]), int(active[j + 1])
        roots.append(brentq(lambda z: branches(z, rl)[old] - branches(z, rl)[new], lo, hi))
    val, _ = quad(integrand, a, r0, points=roots, epsabs=2e-12, epsrel=2e-12, limit=200)
    return float(val), roots


def exterior_payment(a: float, r0: float, rho: float) -> float:
    """Sharp one-sided-shadow payment coefficient C_ext.

    For 0 < delta <= a, the unit needle lies on one side of the support
    perpendicular, so convexity of asin gives
      area(Delta outside B_r0) >= C_ext * asin(delta/(M*rho)).
    This function evaluates the candidate coefficient numerically; the geometric
    lemma and its outer-measure aggregation are separate proof obligations.
    """
    H0 = math.asin(a / (M * rho))
    return a / (2.0 * H0) - M * r0 * r0 / 2.0


def evaluate(x: np.ndarray, details: bool = False):
    a, rl, r0 = map(float, x)
    if not (0.0 < a <= rl <= r0 < 0.5 and r0 >= 0.15):
        bad = 10.0 + sum(abs(v) for v in x)
        return (bad, None) if details else bad
    geo = geometry(a, rl)
    if not geo.get("valid", False):
        bad = 10.0 + a + rl + r0
        return (bad, None) if details else bad
    rho = geo["rho"]
    if not (rho > r0 and a < M * rho and rho > 0.5):
        bad = 10.0 + a + rl + r0
        return (bad, None) if details else bad
    I, switches = integral_and_switches(a, rl, r0)
    cext = exterior_payment(a, r0, rho)
    if cext <= 0.0:
        bad = 10.0 - cext
        return (bad, None) if details else bad
    high = a / (2.0 * math.pi)
    selected_ext = cext / 4.0
    residual_annulus = (rho * rho - r0 * r0) / 2.0
    outer = min(selected_ext, residual_annulus)
    joint = min(high, I, outer)
    d = {
        "a": a,
        "r_lambda": rl,
        "r0": r0,
        "geometry": geo,
        "I": I,
        "switches": switches,
        "high": high,
        "C_ext": cext,
        "selected_exterior_coefficient": selected_ext,
        "residual_annulus_coefficient": residual_annulus,
        "outer": outer,
        "joint": joint,
        "active_bottleneck": min(
            [(high, "high"), (I, "inner"), (outer, "outer")], key=lambda y: y[0]
        )[1],
    }
    return (1.0 - joint, d) if details else 1.0 - joint


def main() -> None:
    started = time.time()
    bounds = [(0.002, 0.49), (0.004, 0.4995), (0.15, 0.4995)]
    runs = []
    for seed in range(12):
        de = differential_evolution(
            evaluate,
            bounds,
            seed=seed,
            maxiter=220,
            popsize=12,
            tol=2e-9,
            polish=False,
            workers=1,
            updating="immediate",
        )
        local = minimize(
            evaluate,
            de.x,
            method="Nelder-Mead",
            options={"maxiter": 1800, "xatol": 3e-11, "fatol": 2e-13},
        )
        _, detail = evaluate(local.x, details=True)
        runs.append({"seed": seed, "de": de.x.tolist(), "local": local.x.tolist(), "detail": detail})
    valid = [r for r in runs if r["detail"] is not None]
    best = max(valid, key=lambda r: r["detail"]["joint"])
    result = {
        "status": "numerical-spike-only",
        "proposed_lemma_unproved": True,
        "objective": "min(a/(2*pi), I, C_ext/4, (rho^2-r0^2)/2)",
        "epsilon": EPS,
        "best": best,
        "runs": runs,
        "elapsed_seconds": time.time() - started,
        "global_optimality_claim": False,
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"best": best["detail"], "elapsed_seconds": result["elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    main()
