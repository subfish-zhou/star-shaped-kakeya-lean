#!/usr/bin/env python3
"""Direct-geometry falsification test for the annular triangle lemmas.

    /usr/bin/python3 spikes/001-joint-inner-outer/test_annular_geometry.py

**This is a falsification test, not a proof.**  It samples and adversarially
optimises legal unit-needle positions and checks the statements of
``PROOF.md`` Lemmas 4.1, 4.2, 4.3, Propositions 4.5 and 5.3 against
independent coordinate geometry (an exact disk/triangle intersection formula,
cross-checked by Monte-Carlo).  Passing it establishes only that no
counterexample was found in the sampled region; the proofs in ``PROOF.md``
are what carry the mathematics.

Conventions match ``PROOF.md``: the needle avoids the **open** ball
``B(0,rho)`` (sphere contact is legal), the working ball ``B(0,r0)`` is
closed, and the origin triangle is ``conv({0} u N)``.

Configuration.  After the normalising rigid motion, a needle of height
``delta`` is ``[s, s+1] x {delta}``; legality is ``s >= L`` (right side) or
``s + 1 <= -L`` (left side), with ``L = sqrt(rho^2 - delta^2)``.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import differential_evolution

# Fixed candidate parameters (same tuple as certify.py).
H0 = float(Fraction(13177, 100000))
R_LAMBDA = float(Fraction(10227, 50000))
R0 = float(Fraction(999, 2000))
EPS_DEL = 1e-10
M = 1.0 - EPS_DEL

TOL = 1e-11
RNG = np.random.default_rng(20260802)


# --------------------------------------------------------------------------
# geometry of the fixed candidate
# --------------------------------------------------------------------------

def candidate_rho() -> float:
    a, rl = H0, R_LAMBDA
    q = 4.0 * rl * rl * (1.0 + a * a) - a * a
    d = a * (1.0 - math.sqrt(q)) / (2.0 * (1.0 + a * a))
    inner = rl * rl - d * d
    den = 1.0 - 2.0 * math.sqrt(inner)
    return math.sqrt(1.0 + 4.0 * d * d) / den - 1.0


RHO = candidate_rho()
C_EXT = H0 / (2.0 * math.asin(H0 / (M * RHO))) - M * R0 * R0 / 2.0


def half_width(delta: float) -> float:
    """H(delta) = arcsin(delta / (m rho))."""
    return math.asin(delta / (M * RHO))


def width_formula(rho: float, delta: float) -> float:
    """The claimed exact maximal one-sided angular width W_rho(delta)."""
    if delta <= 0.0:
        return 0.0
    root = math.sqrt(rho * rho - delta * delta)
    return math.asin(delta / rho) - math.atan(delta / (1.0 + root))


# --------------------------------------------------------------------------
# independent coordinate geometry
# --------------------------------------------------------------------------

def endpoints(delta: float, s: float) -> tuple[np.ndarray, np.ndarray]:
    return np.array([s, delta]), np.array([s + 1.0, delta])


def min_norm_on_segment(a: np.ndarray, b: np.ndarray) -> float:
    """Distance from the origin to the closed segment [a, b]."""
    d = b - a
    dd = float(d @ d)
    if dd == 0.0:
        return float(np.hypot(*a))
    t = float(-(a @ d) / dd)
    t = min(1.0, max(0.0, t))
    return float(np.hypot(*(a + t * d)))


def is_legal(rho: float, delta: float, s: float, slack: float = 0.0) -> bool:
    a, b = endpoints(delta, s)
    return min_norm_on_segment(a, b) >= rho - slack


def angular_width_coordinates(delta: float, s: float) -> float:
    """Angular width of the triangle, from the polar angles of the endpoints."""
    a, b = endpoints(delta, s)
    ta = math.atan2(a[1], a[0])
    tb = math.atan2(b[1], b[0])
    return abs(ta - tb)


def _tri_area(a: np.ndarray, b: np.ndarray) -> float:
    return 0.5 * (a[0] * b[1] - a[1] * b[0])


def _sector_area(r: float, a: np.ndarray, b: np.ndarray) -> float:
    ang = math.atan2(a[0] * b[1] - a[1] * b[0], a[0] * b[0] + a[1] * b[1])
    return 0.5 * r * r * ang


def disk_triangle_area(r: float, a: np.ndarray, b: np.ndarray) -> float:
    """Signed area of disk(0, r) intersected with the triangle (0, a, b).

    Standard chord decomposition: the part of [a, b] inside the disk is a
    sub-segment [t1, t2]; the pieces outside contribute circular sectors.
    """
    d = b - a
    aa = float(d @ d)
    if aa == 0.0:
        return 0.0
    bb = 2.0 * float(a @ d)
    cc = float(a @ a) - r * r
    disc = bb * bb - 4.0 * aa * cc
    if disc <= 0.0:
        return _sector_area(r, a, b)
    root = math.sqrt(disc)
    t1 = (-bb - root) / (2.0 * aa)
    t2 = (-bb + root) / (2.0 * aa)
    if t2 <= 0.0 or t1 >= 1.0:
        return _sector_area(r, a, b)
    t1 = max(t1, 0.0)
    t2 = min(t2, 1.0)
    p1 = a + t1 * d
    p2 = a + t2 * d
    return (_sector_area(r, a, p1) + _tri_area(p1, p2)
            + _sector_area(r, p2, b))


def exterior_area_coordinates(delta: float, s: float, r0: float) -> float:
    """area(Delta \\ closedBall(0, r0)) from exact coordinate geometry."""
    a, b = endpoints(delta, s)
    return abs(_tri_area(a, b)) - abs(disk_triangle_area(r0, a, b))


def interior_area_coordinates(delta: float, s: float, r0: float) -> float:
    a, b = endpoints(delta, s)
    return abs(disk_triangle_area(r0, a, b))


def exterior_area_monte_carlo(delta: float, s: float, r0: float,
                              samples: int = 400000) -> float:
    """Independent Monte-Carlo estimate of the same exterior area."""
    a, b = endpoints(delta, s)
    u = RNG.random(samples)
    v = RNG.random(samples)
    flip = u + v > 1.0
    u = np.where(flip, 1.0 - u, u)
    v = np.where(flip, 1.0 - v, v)
    pts = np.outer(u, a) + np.outer(v, b)
    outside = np.hypot(pts[:, 0], pts[:, 1]) > r0
    return float(abs(_tri_area(a, b)) * outside.mean())


# --------------------------------------------------------------------------
# sampling of legal configurations
# --------------------------------------------------------------------------

def legal_offsets(rho: float, delta: float) -> list[float]:
    """A spread of legal right-hand offsets, including sphere contact."""
    root = math.sqrt(rho * rho - delta * delta)
    return [root, root * (1.0 + 1e-12), root + 1e-6, root + 1e-3,
            root + 0.05, root + 0.5, root + 3.0, root + 40.0, root + 5000.0]


def sampled_configurations() -> list[tuple[float, float]]:
    """(delta, s) pairs covering the boundary and interior of the range."""
    deltas = [0.0, 1e-12, 1e-8, 1e-4, 1e-3, 0.01, 0.05, H0 / 2.0,
              H0 * (1.0 - 1e-9), H0]
    deltas += list(RNG.uniform(0.0, H0, 40))
    configurations = []
    for delta in deltas:
        for s in legal_offsets(RHO, delta):
            configurations.append((float(delta), float(s)))
    return configurations


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------

def check_one_sidedness() -> dict:
    """No legal unit needle straddles the forbidden disk (Lemma 4.1)."""
    violations = []
    scanned = 0
    for rho in [RHO, 0.2, 0.45, 0.51, 0.9, 1.0, 3.0]:
        for frac in np.linspace(0.0, 0.999, 25):
            delta = float(frac) * rho
            root = math.sqrt(max(rho * rho - delta * delta, 0.0))
            for s in np.linspace(-2.0 * root - 2.0, 2.0 * root + 2.0, 601):
                s = float(s)
                scanned += 1
                if not is_legal(rho, delta, s, slack=1e-15):
                    continue
                if not (s >= root - 1e-12 or s + 1.0 <= -root + 1e-12):
                    violations.append({"rho": rho, "delta": delta, "s": s})
    return {"name": "one_sidedness_lemma_4_1", "scanned": scanned,
            "violations": violations, "passed": not violations}


def check_width_formula() -> dict:
    """Coordinate width <= W_rho, with equality exactly at sphere contact."""
    worst_excess = -math.inf
    contact_error = 0.0
    mirror_error = 0.0
    for delta, s in sampled_configurations():
        if delta == 0.0:
            continue
        width = angular_width_coordinates(delta, s)
        claimed = width_formula(RHO, delta)
        worst_excess = max(worst_excess, width - claimed)
        root = math.sqrt(RHO * RHO - delta * delta)
        if s == root:
            contact_error = max(contact_error, abs(width - claimed))
            mirrored = angular_width_coordinates(delta, s)
            left_a = np.array([-(root + 1.0), delta])
            left_b = np.array([-root, delta])
            left_width = abs(math.atan2(left_a[1], left_a[0])
                             - math.atan2(left_b[1], left_b[0]))
            mirror_error = max(mirror_error, abs(left_width - mirrored))
    return {"name": "exact_width_lemma_4_3",
            "worst_excess_over_W_rho": worst_excess,
            "sphere_contact_error": contact_error,
            "left_right_mirror_error": mirror_error,
            "passed": bool(worst_excess <= TOL and contact_error <= TOL
                           and mirror_error <= TOL)}


def check_exterior_area() -> dict:
    """Proposition 4.5, in both the sharp and the simplified form."""
    worst_sharp = math.inf
    worst_simple = math.inf
    worst_sector_identity = 0.0
    for delta, s in sampled_configurations():
        area_ext = exterior_area_coordinates(delta, s, R0)
        sharp = delta / 2.0 - (R0 * R0 / 2.0) * width_formula(RHO, delta)
        simple = delta / 2.0 - (R0 * R0 / 2.0) * math.asin(delta / RHO)
        worst_sharp = min(worst_sharp, area_ext - sharp)
        worst_simple = min(worst_simple, area_ext - simple)
        width = angular_width_coordinates(delta, s)
        identity = interior_area_coordinates(delta, s, R0) - (R0 * R0 / 2.0) * width
        worst_sector_identity = max(worst_sector_identity, abs(identity))
    return {"name": "exterior_area_proposition_4_5",
            "worst_slack_sharp": worst_sharp,
            "worst_slack_simplified": worst_simple,
            "worst_sector_identity_error": worst_sector_identity,
            "passed": bool(worst_sharp >= -TOL and worst_simple >= -TOL
                           and worst_sector_identity <= 1e-10)}


def check_payment_inequality() -> dict:
    """Proposition 5.3: area_ext >= C_ext * H(delta) for 0 <= delta <= h0."""
    worst = math.inf
    worst_config = None
    for delta, s in sampled_configurations():
        area_ext = exterior_area_coordinates(delta, s, R0)
        slack = area_ext - C_EXT * half_width(delta)
        if slack < worst:
            worst, worst_config = slack, (delta, s)
    return {"name": "payment_proposition_5_3",
            "C_ext": C_EXT,
            "worst_slack": worst,
            "worst_configuration": {"delta": worst_config[0],
                                    "s": worst_config[1]},
            "passed": bool(worst >= -TOL)}


def _adversarial(objective, seed: int) -> tuple[float, tuple[float, float]]:
    """Minimise a slack functional over legal configurations."""
    def wrapped(x):
        delta = float(min(max(x[0], 0.0), H0))
        root = math.sqrt(RHO * RHO - delta * delta)
        offset = float(max(x[1], 0.0))
        return objective(delta, root + offset)

    result = differential_evolution(
        wrapped, [(0.0, H0), (0.0, 60.0)], seed=seed, maxiter=400,
        popsize=25, tol=1e-12, polish=True, workers=1, updating="immediate")
    delta = float(min(max(result.x[0], 0.0), H0))
    root = math.sqrt(RHO * RHO - delta * delta)
    return float(result.fun), (delta, root + float(max(result.x[1], 0.0)))


def check_adversarial() -> dict:
    """Adversarially search for a violation of 4.5 and of 5.3."""
    def sharp_slack(delta, s):
        return (exterior_area_coordinates(delta, s, R0)
                - (delta / 2.0 - (R0 * R0 / 2.0) * width_formula(RHO, delta)))

    def payment_slack(delta, s):
        return exterior_area_coordinates(delta, s, R0) - C_EXT * half_width(delta)

    findings = []
    for seed in (0, 1, 2):
        value, config = _adversarial(sharp_slack, seed)
        findings.append({"objective": "proposition_4_5", "seed": seed,
                         "min_slack": value,
                         "delta": config[0], "s": config[1]})
        value, config = _adversarial(payment_slack, seed + 100)
        findings.append({"objective": "proposition_5_3", "seed": seed,
                         "min_slack": value,
                         "delta": config[0], "s": config[1]})
    worst = min(item["min_slack"] for item in findings)
    return {"name": "adversarial_optimisation", "findings": findings,
            "worst_min_slack": worst, "passed": bool(worst >= -1e-10)}


def check_monte_carlo_cross_validation() -> dict:
    """Cross-check the analytic exterior area against Monte-Carlo sampling.

    The tolerance is the statistical one: for a triangle of area `A` and `N`
    uniform samples the estimator has standard deviation at most
    `A * sqrt(1/(4N))`, and we allow six of those.
    """
    samples = 250000
    entries = []
    worst_ratio = 0.0
    for delta in (1e-3, 0.02, H0 / 2.0, H0):
        root = math.sqrt(RHO * RHO - delta * delta)
        for s in (root, root + 0.25, root + 2.0):
            exact = exterior_area_coordinates(delta, s, R0)
            estimate = exterior_area_monte_carlo(delta, s, R0, samples=samples)
            tolerance = 6.0 * (delta / 2.0) * math.sqrt(0.25 / samples) + 1e-15
            error = abs(exact - estimate)
            worst_ratio = max(worst_ratio, error / tolerance)
            entries.append({"delta": delta, "s": s, "exact": exact,
                            "monte_carlo": estimate, "abs_error": error,
                            "tolerance": tolerance,
                            "within_tolerance": bool(error <= tolerance)})
    return {"name": "monte_carlo_cross_validation", "samples": samples,
            "entries": entries,
            "worst_error_over_tolerance_ratio": worst_ratio,
            "passed": all(item["within_tolerance"] for item in entries)}


def check_falsification_power() -> dict:
    """The test must be able to reject an over-claim.

    Halving the sector term claims a strictly larger exterior area than the
    truth.  Because the sector identity is an equality at sphere contact, the
    over-claim must be violated there; if it were not, this test would have no
    power and the suite fails.
    """
    counterexamples = []
    for delta, s in sampled_configurations():
        if delta <= 0.0:
            continue
        area_ext = exterior_area_coordinates(delta, s, R0)
        overclaim = delta / 2.0 - (R0 * R0 / 4.0) * width_formula(RHO, delta)
        if area_ext < overclaim - TOL:
            counterexamples.append({"delta": delta, "s": s,
                                    "deficit": overclaim - area_ext})
    two_sided_is_weaker = all(
        width_formula(RHO, d) < 2.0 * math.asin(d / RHO)
        for d in (1e-6, 0.01, H0 / 2.0, H0))
    return {"name": "falsification_power_control",
            "overclaim_counterexamples": len(counterexamples),
            "example": counterexamples[0] if counterexamples else None,
            "sharp_width_below_two_sided_bound": bool(two_sided_is_weaker),
            "passed": bool(counterexamples) and bool(two_sided_is_weaker)}


def main() -> int:
    checks = [
        check_one_sidedness(),
        check_width_formula(),
        check_exterior_area(),
        check_payment_inequality(),
        check_adversarial(),
        check_monte_carlo_cross_validation(),
        check_falsification_power(),
    ]
    passed = all(item["passed"] for item in checks)
    summary = {
        "evidence_level": "falsification test, not a proof",
        "parameters": {"h0": H0, "r_lambda": R_LAMBDA, "r0": R0,
                       "rho": RHO, "m": M, "C_ext": C_EXT},
        "checks": checks,
        "all_passed": passed,
    }
    print(json.dumps(summary, indent=2, sort_keys=True, default=float))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
