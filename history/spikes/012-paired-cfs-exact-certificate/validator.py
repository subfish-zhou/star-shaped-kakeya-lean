#!/usr/bin/env python3
"""Independent radial re-atomizing validator; never reads checker rows/caches."""
from __future__ import annotations
import hashlib
import json
import sys
from fractions import Fraction as Q
from pathlib import Path
from typing import Any
from interval_math import ledger_interval, paired_integral_interval, pi_interval

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parent
TRUSTED_OLD_Q_TEXT = (
    "120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423/"
    "5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000"
)
TRUSTED_OLD_Q = Q(TRUSTED_OLD_Q_TEXT)
OLD_Q_PROVENANCE = "spikes/007-cfs-rational-cert/README.md:9-10"


class ValidationError(Exception): pass


def need(ok: bool, message: str) -> None:
    if not ok: raise ValidationError(message)


def validate_certificate(data: dict[str, Any], certificate: dict[str, Any]) -> dict[str, Any]:
    try:
        need(data["schema"] == "paired-cfs-exact-outward-v1", "schema")
        n = int(data["N"]); alpha = [Q(x) for x in data["alpha"]]
        radii = [Q(x) for x in data["R"]]; t = [Q(x) for x in data["t"]]
        eta = Q(data["eta"]); terms = int(data["log_terms"])
        p = data["paired"]; H = Q(p["H"]); q = Q(p["q"])
        jl, jr = Q(p["J_left"]), Q(p["J_right"])
        pair_R, rc = Q(p["paired_reach"]), Q(p["complement_radius_lower"])
    except (KeyError, ValueError, ZeroDivisionError) as exc:
        raise ValidationError(f"malformed primary data: {exc}") from exc
    need(n == 64 and len(alpha) == 65 and len(radii) == 64 and len(t) == 65, "index closure")
    need(alpha[0] == 0 and alpha[-1] == eta and all(alpha[i] < alpha[i+1] for i in range(n)), "partition")
    need(radii[0] == Q(1,2) and all(radii[i] <= radii[i+1] for i in range(63)), "radii")
    need(all(radii[i]**2 <= Q(1,4)+alpha[i]**2 for i in range(n)), "geometry")
    need(t[0] == alpha[1] and all(t[i] < t[i+1] for i in range(n)), "switches")
    need(t[1] >= eta and all(t[i+1] <= radii[i] for i in range(n)), "window caps")
    need(t[-1] < eta + Q(1,2), "low/high separation")
    need(terms == 14 and data["asin_terms"] == 80 and data["paired_subdivisions"] == 128, "arithmetic controls")
    need(Q(data["old_q"]) == TRUSTED_OLD_Q, "old_q provenance mismatch")
    need(p["enabled"] is True, "missing paired action")
    need(p["replacement_mode"] == "replace", "J must be replacement-only")
    need(p["asin_bound_direction"] == "upper_for_lower_integrand", "asin direction")
    need(q > Q(1,2), "q>1/2")
    need(H > 0 and H < alpha[1] and pair_R == 1-q and alpha[1] < pair_R, "paired geometry")
    need(jl == alpha[1] and jl < jr <= alpha[2], "J endpoint/cell gate")
    need(rc > Q(1,2) and rc <= q and rc**2 <= Q(1,4)+H**2 and t[1] < rc, "replacement reach")

    # Independently reconstruct original D0..D63 on all cap/switch atoms.
    cuts = sorted(set(alpha[1:]) | set(t[1:]))
    original = [[Q(0), Q(0)] for _ in range(n)]
    atom_count = 0; max_load = 0
    for left, right in zip(cuts, cuts[1:]):
        mid = (left + right) / 2
        active = []
        if alpha[1] <= mid < t[1]: active.append(0)
        for i in range(1, n):
            if t[i] <= mid < t[i+1]: active.append(i)
        max_load = max(max_load, len(active)); need(len(active) <= 1, "radial load")
        if not active: continue
        i = active[0]
        eligible = ([j for j in range(n) if alpha[j+1] <= left] if i == 0 else list(range(i,n)))
        need(bool(eligible), "empty eligible set")
        lo, hi = ledger_interval(left, right, radii[i], terms)
        need(lo >= 0, "negative atom")
        for j in eligible: original[j][0] += lo; original[j][1] += hi
        atom_count += 1
    need(all(x[0] > 0 for x in original), "all 64 original rows")

    # Rebuild N,C directly from owned atoms, not from cached/original D0 total.
    pair = paired_integral_interval(H, H, alpha[1], pair_R, data["paired_subdivisions"], data["asin_terms"])
    old_rest = ledger_interval(jr, t[1], Q(1,2), terms)
    replacement = ledger_interval(jl, jr, rc, terms)
    near = (pair[0]+old_rest[0], pair[1]+old_rest[1])
    comp = (replacement[0]+old_rest[0], replacement[1]+old_rest[1])
    refined = [near, comp] + [tuple(x) for x in original[1:]]
    names = ["N","C"]+[f"D{i}" for i in range(1,n)]
    need(all(x[0] > 0 for x in refined), "refined atom floors")

    tail = data["high_tail"]
    need(tail["tail_start"] == 0, "high tail start")
    need(tail["contract"] == "symbolic_all_real_A_ge_eta_hence_all_integer_k_ge_0", "tail universal contract")
    r0 = Q(tail["sqrt_one_plus_eta_sq_lower"]); need(r0*r0 < 1+eta*eta, "radical direction")
    d = r0-eta; need(Q(1,2)<d<1 and 1-d*d-2*eta*d>0, "tail polynomial")
    high = (eta+Q(1,2))/(2*eta+Q(3,2))*(d-Q(1,2))**2/2
    pi_l, pi_u = pi_interval()
    low_l=min(x[0] for x in refined); low_u=min(x[1] for x in refined)
    witness=min(eta/2,pi_l*low_l,pi_l*high)
    implicit_upper=min(eta/2,pi_u*low_u)
    need(witness>TRUSTED_OLD_Q*pi_u,"strict old q*pi improvement")

    # Bind the independently reconstructed enclosure to the complete checker artifact.
    try:
        need(certificate["status"] == "PAIRED_CFS_EXACT_CERTIFICATE_OK", "checker status")
        witness_text = certificate["exact_rational_witness"]
        claimed_witness = Q(witness_text)
        claimed_upper = Q(certificate["implicit_upper"])
        claimed_validated_lower = Q(certificate["validated_lower"])
        claimed_atoms = certificate["refined_atoms"]
        claimed_active = certificate["lower_active_atom"]
        claimed_upper_active = certificate["upper_active_atom"]
        claimed_intervals = certificate["refined_intervals"]
        claimed_original = certificate["original_64_low_intervals"]
        claimed_pair = certificate["paired_interval"]
        claimed_old_j = certificate["old_J_interval"]
        claimed_replacement = certificate["replacement_J_interval"]
        claimed_old_q = Q(certificate["old_q"])
    except (KeyError, TypeError, ValueError, ZeroDivisionError) as exc:
        raise ValidationError(f"malformed checker certificate: {exc}") from exc
    canonical_witness = f"{claimed_witness.numerator}/{claimed_witness.denominator}"
    need(witness_text == canonical_witness, "noncanonical rational witness")
    need(certificate["exact_rational_witness_sha256"] == hashlib.sha256(
        witness_text.encode("ascii")
    ).hexdigest(), "rational witness SHA-256")
    need(claimed_witness <= witness, "claimed W exceeds independent lower bound")
    need(claimed_upper >= implicit_upper, "claimed upper misses independent upper bound")
    need(claimed_validated_lower == claimed_witness, "validated lower/witness mismatch")
    need(claimed_witness <= claimed_upper, "claimed enclosure order")
    need(claimed_old_q == TRUSTED_OLD_Q and
         certificate.get("old_q_provenance") == OLD_Q_PROVENANCE, "certificate old_q provenance")
    need(claimed_atoms == names and len(claimed_atoms) == 65, "complete 65-atom witness")
    active = names[[x[0] for x in refined].index(low_l)]
    upper_active = names[[x[1] for x in refined].index(low_u)]
    need(claimed_active == active, "active atom binding")
    need(claimed_upper_active == upper_active, "upper active atom binding")
    need(isinstance(claimed_intervals, dict) and set(claimed_intervals) == set(names),
         "complete refined interval witness")
    for name, independent in zip(names, refined):
        try:
            claimed_lo, claimed_hi = map(Q, claimed_intervals[name])
        except (TypeError, ValueError, ZeroDivisionError) as exc:
            raise ValidationError(f"malformed interval for {name}: {exc}") from exc
        need(claimed_lo <= independent[0] <= independent[1] <= claimed_hi,
             f"checker interval does not contain independent {name}")
    need(isinstance(claimed_original, list) and len(claimed_original) == 64,
         "complete original-row witness")
    for j, independent in enumerate(original):
        try:
            claimed_lo, claimed_hi = map(Q, claimed_original[j])
        except (TypeError, ValueError, ZeroDivisionError) as exc:
            raise ValidationError(f"malformed original row {j}: {exc}") from exc
        need(claimed_lo <= independent[0] <= independent[1] <= claimed_hi,
             f"checker row does not contain independent D{j}")

    def bind_interval(label: str, claimed: Any, independent: tuple[Q, Q]) -> None:
        try:
            claimed_lo, claimed_hi = map(Q, claimed)
        except (TypeError, ValueError, ZeroDivisionError) as exc:
            raise ValidationError(f"malformed {label}: {exc}") from exc
        need(claimed_lo <= independent[0] <= independent[1] <= claimed_hi,
             f"checker {label} does not contain independent interval")

    bind_interval("paired interval", claimed_pair, pair)
    bind_interval("old J interval", claimed_old_j, ledger_interval(jl, jr, Q(1,2), terms))
    bind_interval("replacement J interval", claimed_replacement, replacement)
    return {"original_row_count":64,"refined_atom_count":65,"radial_atom_count":atom_count,
            "max_radial_load":max_load,"paired_replacement_overlap":Q(0),
            "tail_contract_covers_all_k":True,"exact_rational_witness":witness,
            "implicit_upper":implicit_upper,"active_atom":active,
            "certificate_witness_bound":True}


def f(x: Any) -> Any:
    if isinstance(x,Q): return f"{x.numerator}/{x.denominator}"
    if isinstance(x,dict): return {k:f(v) for k,v in x.items()}
    return x


def main() -> None:
    data=json.loads((ROOT/"primary_data.json").read_text())
    certificate=json.loads((ROOT/"results/certificate.json").read_text())
    report=validate_certificate(data,certificate)
    out=f(report);out["status"]="INDEPENDENT_VALIDATOR_OK"
    (ROOT/"results").mkdir(exist_ok=True);(ROOT/"results/validation.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({k:out[k] for k in ("status","original_row_count","refined_atom_count","active_atom")},indent=2))

if __name__ == "__main__": main()
