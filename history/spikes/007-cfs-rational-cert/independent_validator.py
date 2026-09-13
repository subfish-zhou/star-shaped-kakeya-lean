#!/usr/bin/env python3
"""Independent fail-closed validator for the frozen finite schedule.

It deliberately does not import the optimiser or exact_certificate.  It cuts
at every radial switch and every class cap, reconstructs complete eligibility
on each atom, and then integrates the resulting simple function.
"""
from __future__ import annotations

from fractions import Fraction as Q
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
LOG_TERMS = 4
PI_LOWER = Q(333, 106)


class ValidationError(Exception):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def frac(x: str) -> Q:
    try:
        return Q(x)
    except Exception as exc:
        raise ValidationError(f"bad rational: {x!r}") from exc


def upper_log(y: Q, count: int) -> Q:
    need(count == LOG_TERMS, "fixed positive log truncation")
    need(y >= 1, "log direction")
    z = (y - 1) / (y + 1)
    need(0 <= z < 1, "atanh domain")
    body = Q(0)
    for h in range(count):
        body += z ** (2 * h + 1) / (2 * h + 1)
    remainder = z ** (2 * count + 1) / ((2 * count + 1) * (1 - z * z))
    return 2 * (body + remainder)


def atom_integral(left: Q, right: Q, radius: Q, count: int) -> Q:
    need(0 <= left <= right <= radius, "atom outside window radius")
    log_bound = upper_log((radius + right) / (radius + left), count)
    return (-(right * right - left * left) / 2 + 2 * radius * (right - left)
            - 2 * radius * radius * log_bound)


def validate(data: dict[str, Any]) -> dict[str, Any]:
    try:
        n = int(data["N"])
        eta, target, common = frac(data["eta"]), frac(data["target"]), frac(data["common"])
        alpha = [frac(v) for v in data["alpha"]]
        radii = [frac(v) for v in data["R"]]
        t = [frac(v) for v in data["t"]]
        terms = int(data["log_terms"])
        pi_lower = frac(data["pi_lower"])
    except KeyError as exc:
        raise ValidationError(f"missing field {exc}") from exc

    need(n == 64 and len(alpha) == n + 1 and len(radii) == n and len(t) == n + 1,
         "index closure")
    need(terms == LOG_TERMS, "log_terms contract")
    need(pi_lower == PI_LOWER, "pi_lower contract")
    need(alpha[0] == 0 and alpha[-1] == eta, "partition endpoints")
    need(all(alpha[j] < alpha[j + 1] for j in range(n)), "gap-free class partition")
    need(radii[0] == Q(1, 2), "R0")
    need(all(radii[j] <= radii[j + 1] for j in range(n - 1)), "radius direction")
    for j in range(n):
        need(radii[j] * radii[j] <= Q(1, 4) + alpha[j] * alpha[j],
             f"geometry eligibility {j}")
    need(t[0] == alpha[1], "t0 index")
    need(all(t[j] < t[j + 1] for j in range(n)), "radial overlap")
    need(t[1] >= eta, "first long window")
    need(all(t[j + 1] <= radii[j] for j in range(n)), "load/window cap")
    need(t[-1] < eta + Q(1, 2), "low/high separation")

    # Re-atomise from primary schedule data.  No cached per-class rows are read.
    cuts = sorted(set(alpha[1:]) | set(t[1:]))
    need(cuts[0] == alpha[1] and cuts[-1] == t[-1], "radial atom coverage")
    totals = [Q(0) for _ in range(n)]
    max_load = 0
    atom_rows = []
    for left, right in zip(cuts, cuts[1:]):
        mid = (left + right) / 2
        active = []
        if alpha[1] <= mid < t[1]:
            active.append(0)
        for i in range(1, n):
            if t[i] <= mid < t[i + 1]:
                active.append(i)
        max_load = max(max_load, len(active))
        need(len(active) <= 1, "load exceeds one")
        if not active:
            continue
        i = active[0]
        if i == 0:
            eligible = [j for j in range(n) if alpha[j + 1] <= left]
        else:
            eligible = list(range(i, n))
        need(bool(eligible), "active atom has no complete eligible class")
        # Independently check every credited class against the geometry cap.
        for j in eligible:
            need(i <= j, "incomplete class credited")
            need(radii[i] * radii[i] <= Q(1, 4) + alpha[j] * alpha[j],
                 "credited class fails geometry")
        value = atom_integral(left, right, radii[i], terms)
        need(value >= 0, "negative atom lower bound")
        for j in eligible:
            totals[j] += value
        atom_rows.append((left, right, i, tuple(eligible)))

    for j, total in enumerate(totals):
        need(total > common, f"class floor {j}")

    # Complete symbolic high-tail contract.  This is a universal-in-A proof,
    # not evaluation of finitely many k values.
    try:
        tail = data["high_tail"]
        need(tail["tail_start"] == 0, "missing tail band")
        r0 = frac(tail["sqrt_one_plus_eta_sq_lower"])
    except KeyError as exc:
        raise ValidationError(f"missing high-tail contract {exc}") from exc
    need(r0 * r0 < 1 + eta * eta, "bad radical lower bound")
    d = r0 - eta
    need(Q(1, 2) < d < 1 and d * d <= 1, "uniform width proof")
    # The radical bound is also exactly the constant term needed below:
    # 1-d^2-2 eta d = 1+eta^2-r0^2 > 0.
    need(1 - d * d - 2 * eta * d > 0, "uniform reach constant")
    # For x=A-eta>=0: A+eta-d^2(A-eta)
    # = 2 eta + (1-d^2)x >= 0, proving sqrt(A^2-eta^2)>=d(A-eta).
    need(2 * eta >= 0 and 1 - d * d >= 0, "tail polynomial coefficients")
    width = d - Q(1, 2)
    factor0 = (eta + Q(1, 2)) / (2 * eta + Q(3, 2))
    high = factor0 * width * width / 2
    need(high > common, "infinite high-tail floor")

    need(eta / 2 > target, "height branch")
    need(common * pi_lower > target, "pi branch")
    need(target > Q(141, 2000), "not stronger than old witness")
    return {
        "class_count": n,
        "atom_count": len(atom_rows),
        "atom_boundaries": [f"{x.numerator}/{x.denominator}" for x in cuts],
        "max_low_load": max_load,
        "minimum_low_payment": min(totals),
        "minimum_low_class": totals.index(min(totals)),
        "high_payment_lower": high,
        "tail_contract_covers_all_k": True,
    }


def main() -> None:
    report = validate(json.loads((ROOT / "frozen_schedule.json").read_text()))
    # The independent atom sum has a deliberately enormous exact denominator;
    # keep it exact in memory and print only a diagnostic decimal here.
    printable = {
        "class_count": report["class_count"],
        "atom_count": report["atom_count"],
        "max_low_load": report["max_low_load"],
        "minimum_low_class": report["minimum_low_class"],
        "minimum_low_payment_decimal": float(report["minimum_low_payment"]),
        "high_payment_lower_decimal": float(report["high_payment_lower"]),
        "tail_contract_covers_all_k": report["tail_contract_covers_all_k"],
        "status": "INDEPENDENT_VALIDATOR_OK",
    }
    print(json.dumps(printable, indent=2))


if __name__ == "__main__":
    main()
