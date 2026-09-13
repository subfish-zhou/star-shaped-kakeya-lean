#!/usr/bin/env python3
"""Primary fail-closed checker for the paired CFS frozen witness."""
from __future__ import annotations
import json
import sys
import hashlib
from decimal import Decimal, localcontext
from fractions import Fraction as Q

sys.set_int_max_str_digits(0)
from pathlib import Path
from typing import Any
from interval_math import ledger_interval, paired_integral_interval, pi_interval, need

ROOT = Path(__file__).resolve().parent
TRUSTED_OLD_Q_TEXT = (
    "120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423/"
    "5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000"
)
TRUSTED_OLD_Q = Q(TRUSTED_OLD_Q_TEXT)
OLD_Q_PROVENANCE = "spikes/007-cfs-rational-cert/README.md:9-10"


PRODUCTION_TEST_FAULTS = {"remove_paired_term", "asin_wrong_direction", "high_tail_start"}


def high_tail_lower(data: dict[str, Any], test_fault: str | None = None) -> Q:
    eta = Q(data["eta"])
    tail = data["high_tail"]
    need(tail["tail_start"] == 0, "frozen high tail provenance")
    need(tail["contract"] == "symbolic_all_real_A_ge_eta_hence_all_integer_k_ge_0",
         "high tail symbolic contract")
    # Reconstruct the first owned high band.  The fault omits k=0 in the
    # production ownership calculation; the coverage gate then sees the gap.
    first_k = 1 if test_fault == "high_tail_start" else 0
    first_A = eta + first_k * Q(tail["band_step"])
    need(first_A == eta, "high-tail ownership must cover the half-open k=0 band")
    r0 = Q(tail["sqrt_one_plus_eta_sq_lower"])
    need(r0 * r0 < 1 + eta * eta, "radical lower direction")
    d = r0 - eta
    need(Q(1, 2) < d < 1, "uniform high width")
    need(1 - d * d - 2 * eta * d > 0, "uniform high reach")
    return (eta + Q(1, 2)) / (2 * eta + Q(3, 2)) * (d - Q(1, 2)) ** 2 / 2


def parse_and_gate(data: dict[str, Any]):
    need(data["schema"] == "paired-cfs-exact-outward-v1", "schema")
    n = int(data["N"]); need(n == 64, "N=64")
    alpha = [Q(x) for x in data["alpha"]]
    radii = [Q(x) for x in data["R"]]
    t = [Q(x) for x in data["t"]]
    eta = Q(data["eta"])
    need(len(alpha) == 65 and len(radii) == 64 and len(t) == 65, "index closure")
    need(alpha[0] == 0 and alpha[-1] == eta, "partition endpoints")
    need(all(alpha[i] < alpha[i + 1] for i in range(64)), "partition order")
    need(radii[0] == Q(1, 2), "R0")
    need(all(radii[i] <= radii[i + 1] for i in range(63)), "radius order")
    need(all(radii[i] ** 2 <= Q(1, 4) + alpha[i] ** 2 for i in range(64)), "geometry")
    need(t[0] == alpha[1] and all(t[i] < t[i + 1] for i in range(64)), "switch order")
    need(t[1] >= eta and all(t[i + 1] <= radii[i] for i in range(64)), "window caps")
    need(t[-1] < eta + Q(1, 2), "low/high separation")
    p = data["paired"]
    H, q = Q(p["H"]), Q(p["q"])
    jl, jr = Q(p["J_left"]), Q(p["J_right"])
    pair_R, rc = Q(p["paired_reach"]), Q(p["complement_radius_lower"])
    need(p["enabled"] is True, "paired term required")
    need(p["replacement_mode"] == "replace", "replacement-only ownership")
    need(p["asin_bound_direction"] == "upper_for_lower_integrand", "asin lower-bound direction")
    need(q > Q(1, 2), "q>1/2")
    need(0 < H < alpha[1] < pair_R and pair_R == 1 - q, "paired reach geometry")
    need(jl == alpha[1] and jl < jr <= alpha[2], "J inside first CFS cell")
    need(rc > Q(1, 2) and rc <= q and rc * rc <= Q(1, 4) + H * H, "complement reach")
    need(t[1] < rc, "replacement reaches first window")
    need(data["log_terms"] == 14 and data["asin_terms"] == 80 and data["paired_subdivisions"] == 128,
         "frozen arithmetic controls")
    need(Q(data["old_q"]) == TRUSTED_OLD_Q, "old_q provenance mismatch")
    return alpha, radii, t, eta, H, jl, jr, pair_R, rc


def check_certificate(data: dict[str, Any], test_fault: str | None = None) -> dict[str, Any]:
    need(test_fault is None or test_fault in PRODUCTION_TEST_FAULTS, "unknown production test fault")
    alpha, radii, t, eta, H, jl, jr, pair_R, rc = parse_and_gate(data)
    terms = data["log_terms"]
    rows: list[tuple[Q, Q]] = []
    for j in range(64):
        lo, hi = ledger_interval(alpha[j + 1], t[1], radii[0], terms)
        for i in range(1, j + 1):
            xlo, xhi = ledger_interval(t[i], t[i + 1], radii[i], terms)
            lo += xlo; hi += xhi
        need(lo > 0 and lo <= hi, f"original row {j}")
        rows.append((lo, hi))

    old_j = ledger_interval(jl, jr, Q(1, 2), terms)
    new_j = ledger_interval(jl, jr, rc, terms)
    pair = paired_integral_interval(
        H, H, alpha[1], pair_R, data["paired_subdivisions"], data["asin_terms"],
        "asin_wrong_direction" if test_fault == "asin_wrong_direction" else None,
    )
    if test_fault == "remove_paired_term":
        pair = (Q(0), Q(0))
    near = (rows[0][0] - old_j[1] + pair[0], rows[0][1] - old_j[0] + pair[1])
    comp = (rows[0][0] + new_j[0] - old_j[1], rows[0][1] + new_j[1] - old_j[0])
    need(near[0] > 0 and comp[0] > 0, "refined split columns")
    refined = [near, comp] + rows[1:]
    names = ["N", "C"] + [f"D{i}" for i in range(1, 64)]
    high = high_tail_lower(data, test_fault)
    pi_l, pi_u = pi_interval()
    low_l = min(x[0] for x in refined); low_u = min(x[1] for x in refined)
    validated_lower = min(eta / 2, pi_l * low_l, pi_l * high)
    implicit_upper = min(eta / 2, pi_u * low_u)
    old_q = TRUSTED_OLD_Q
    need(validated_lower > old_q * pi_u, "strict improvement over old q*pi")
    need(validated_lower <= implicit_upper, "nonempty validated enclosure")
    return {
        "refined_atoms": names,
        "original_64_low_intervals": rows,
        "refined_intervals": dict(zip(names, refined)),
        "paired_interval": pair,
        "old_J_interval": old_j,
        "replacement_J_interval": new_j,
        "high_lower": high,
        "pi_lower": pi_l, "pi_upper": pi_u,
        "old_q": old_q,
        "old_q_provenance": OLD_Q_PROVENANCE,
        "exact_rational_witness": validated_lower,
        "validated_lower": validated_lower,
        "implicit_upper": implicit_upper,
        "lower_active_atom": names[[x[0] for x in refined].index(low_l)],
        "upper_active_atom": names[[x[1] for x in refined].index(low_u)],
    }


def fs(x: Any) -> Any:
    if isinstance(x, Q): return f"{x.numerator}/{x.denominator}"
    if isinstance(x, tuple): return [fs(v) for v in x]
    if isinstance(x, list): return [fs(v) for v in x]
    if isinstance(x, dict): return {k: fs(v) for k, v in x.items()}
    return x


def public_certificate(report: dict[str, Any]) -> dict[str, Any]:
    """Serialize the full checker witness and bind its canonical rational W."""
    public = fs(report)
    public["status"] = "PAIRED_CFS_EXACT_CERTIFICATE_OK"
    witness_text = public["exact_rational_witness"]
    public["exact_rational_witness_sha256"] = hashlib.sha256(
        witness_text.encode("ascii")
    ).hexdigest()
    return public


def main() -> None:
    data = json.loads((ROOT / "primary_data.json").read_text())
    report = check_certificate(data)
    public = public_certificate(report)
    (ROOT / "results").mkdir(exist_ok=True)
    (ROOT / "results/certificate.json").write_text(json.dumps(public, indent=2) + "\n")
    with localcontext() as ctx:
        ctx.prec = 45
        witness_decimal = str(Decimal(report["exact_rational_witness"].numerator) /
                              Decimal(report["exact_rational_witness"].denominator))
    print(json.dumps({
        "status": public["status"],
        "lower_active_atom": public["lower_active_atom"],
        "validated_lower_decimal": witness_decimal,
        "exact_rational_witness_sha256": public["exact_rational_witness_sha256"],
    }, indent=2))


if __name__ == "__main__": main()
