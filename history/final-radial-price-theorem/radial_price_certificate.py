#!/usr/bin/env python3
"""Pure-rational, outward verifier for the radial-price witness.

No floating-point arithmetic or numerical quadrature is used in any proof
check.  asin/log/atan are enclosed by rational power-series remainders;
Machin's formula encloses pi.  High kernel integrals are exact Fractions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

TARGET = F(224552, 10_000_000)       # requested 0.0224552
M0, H = F(99, 100), F(1, 5)
S_TEXT = ["0.99", "1.45628085", "2.01689132", "2.70060055",
          "3.55177018", "4.71011205", "6.83593359"]
A_TEXT = ["0.36434005", "0.90208096", "1.36854204", "1.92904040",
          "2.61222500", "3.46096510", "4.60835052", "6.83593359"]
S, A = [F(x) for x in S_TEXT], [F(x) for x in A_TEXT]
DPLACES = 18
SCALE10 = 10 ** DPLACES


@dataclass(frozen=True)
class IV:
    lo: F
    hi: F
    def __post_init__(self):
        assert self.lo <= self.hi
    @staticmethod
    def point(x: F | int) -> "IV":
        return IV(F(x), F(x))
    def __add__(self, o):
        o = as_iv(o); return IV(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__
    def __neg__(self): return IV(-self.hi, -self.lo)
    def __sub__(self, o): return self + (-as_iv(o))
    def __rsub__(self, o): return as_iv(o) - self
    def __mul__(self, o):
        o = as_iv(o)
        q = (self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi)
        return IV(min(q), max(q))
    __rmul__ = __mul__
    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return IV(1/self.hi, 1/self.lo)
    def __truediv__(self, o): return self * as_iv(o).reciprocal()
    def __rtruediv__(self, o): return as_iv(o) / self
    def sq(self):
        if self.lo <= 0 <= self.hi: return IV(F(0), max(self.lo*self.lo, self.hi*self.hi))
        q = (self.lo*self.lo, self.hi*self.hi); return IV(min(q), max(q))


def as_iv(x) -> IV: return x if isinstance(x, IV) else IV.point(F(x))


def atan_unit(x: F, n: int = 32) -> IV:
    """Alternating atan series enclosure, exact for 0<=x<=1."""
    assert 0 <= x <= 1
    total, power = F(0), x
    for k in range(n):
        total += (-1 if k & 1 else 1) * power / (2*k+1)
        power *= x*x
    nxt = (-1 if n & 1 else 1) * power / (2*n+1)
    return IV(min(total, total+nxt), max(total, total+nxt))


def pi_iv() -> IV:
    """Machin identity pi=16 atan(1/5)-4 atan(1/239)."""
    return 16*atan_unit(F(1, 5)) - 4*atan_unit(F(1, 239))


def asin_point(x: F, n: int = 40) -> IV:
    """Positive Taylor series plus a geometric majorant for its tail."""
    assert 0 <= x < 1
    coeff, power, total = F(1), x, F(0)
    for k in range(n):
        term = coeff * power / (2*k+1)
        total += term
        coeff *= F(2*k+1, 2*k+2)
        power *= x*x
    next_term = coeff * power / (2*n+1)
    return IV(total, total + next_term/(1-x*x))


def log_point_pos(x: F, n: int = 50) -> IV:
    """log(x)=2 atanh((x-1)/(x+1)), with rational tail bound."""
    assert x > 0
    if x < 1:
        y = log_point_pos(1/x, n)
        return -y
    z = (x-1)/(x+1)
    total, power = F(0), z
    for k in range(n):
        total += power/F(2*k+1)
        power *= z*z
    total *= 2
    tail = 2*power / (F(2*n+1)*(1-z*z))
    return IV(total, total+tail)


def log_iv(x: IV) -> IV:
    assert x.lo > 0
    return IV(log_point_pos(x.lo).lo, log_point_pos(x.hi).hi)


def low_enclosure() -> IV:
    m = 1-M0
    alpha = 2*asin_point(F(50, 99))
    # atan(20)=pi/2-atan(1/20), avoiding a slow large-argument series.
    beta = pi_iv()/2 - atan_unit(F(1, 20))
    c_h = 2*alpha/(alpha+2*beta)
    r0 = m*beta/(alpha+beta)
    assert r0.hi < H
    a = r0

    def p(r: IV) -> IV:
        return -r.sq() + 4*m*r - 4*m*m*log_iv(1+r/m)
    base = c_h*a.sq()/2 + p(IV.point(m)) - p(a)

    k_h = alpha/(alpha + 2*asin_point(F(2, 5)))
    cross = F(1, 2)*(1-k_h)/(1+k_h)
    cut = IV.point(A[0])
    assert m < cross.lo and cross.hi < A[0]

    def q(r: IV) -> IV:
        return -r.sq()/2 + r - F(1, 2)*log_iv(F(1, 2)+r)
    outer = k_h*(cross.sq()-m*m)/2 + q(cut)-q(cross)
    return base+outer


def poly_integral(s: F, lo: F, hi: F) -> F:
    """Exact integral of min(r,1)*min(1/2,max(0,s-r))."""
    mid = (lo+hi)/2
    mr = mid if mid < 1 else F(1)
    d = s-mid
    if d <= 0: return F(0)
    ramp = d if d < F(1,2) else F(1,2)
    if mr == mid and ramp == F(1,2):       # r/2
        return (hi*hi-lo*lo)/4
    if mr == mid:                           # r(s-r)
        return s*(hi*hi-lo*lo)/2-(hi**3-lo**3)/3
    if ramp == F(1,2):                     # 1/2
        return (hi-lo)/2
    return s*(hi-lo)-(hi*hi-lo*lo)/2       # s-r


def high_integral(s: F, lo: F, hi: F) -> F:
    cuts = sorted({lo, hi, F(1), s-F(1,2), s})
    cuts = [x for x in cuts if lo <= x <= hi]
    return sum((poly_integral(s,x,y) for x,y in zip(cuts,cuts[1:])), F(0))


def floor_decimal(x: F) -> str:
    n = x.numerator*SCALE10 // x.denominator
    return f"{n//SCALE10}.{n%SCALE10:0{DPLACES}d}"


def ceil_decimal(x: F) -> str:
    n = -((-x.numerator*SCALE10)//x.denominator)
    return f"{n//SCALE10}.{n%SCALE10:0{DPLACES}d}"


def fstr(x: F) -> str: return f"{x.numerator}/{x.denominator}"


def build_receipt() -> dict:
    assert len(S)==7 and len(A)==8
    assert all(x<y for x,y in zip(S,S[1:])); assert all(x<y for x,y in zip(A,A[1:]))
    assert all(A[j+1] <= S[j] for j in range(6)) and A[-1] == S[-1]

    piv = pi_iv(); low = low_enclosure()
    ints, coeff_lbs = [], []
    for j in range(7):
        upper = S[j+1] if j < 6 else 2*S[6]
        integ = high_integral(S[j], A[j], A[j+1])
        ints.append(integ); coeff_lbs.append(integ/(piv.hi*upper))
    tail_int = high_integral(2*S[6], S[6], 2*S[6])
    tail_lb = tail_int/(piv.hi*4*S[6])

    # Exact strict inequalities: these assertions compare Fractions only.
    assert low.lo > TARGET
    assert all(x > TARGET for x in coeff_lbs)
    assert tail_lb > TARGET
    min_lb = min([low.lo, *coeff_lbs, tail_lb])

    atoms = [{"lo": "0", "hi": A_TEXT[0], "owner": "low", "price": "1"}]
    atoms += [{"lo": A_TEXT[j], "hi": A_TEXT[j+1], "owner": f"high_{j}", "price": "1"} for j in range(7)]
    # Finite atoms are disjoint; tail starts at A[-1], and its dyadic bands
    # [2^(n-1)S6,2^n S6) are pairwise disjoint. Hence pointwise sum <=1.
    assert all(F(atoms[j]["hi"]) <= F(atoms[j+1]["lo"]) for j in range(7))

    source_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return {
      "certificate_type": "pure_rational_outward_interval_radial_price_v1",
      "status": "PROVED_STRICTLY_ABOVE_TARGET_AND_PRICE_AT_MOST_ONE",
      "verifier_sha256": source_hash,
      "arithmetic": "Python Fraction only; exact polynomial integrals; rational Taylor remainder enclosures; no float/quadrature",
      "target_exact": fstr(TARGET), "target_decimal": "0.0224552",
      "parameters": {"M0": "99/100", "H": "1/5"},
      "scale_boundaries_exact_decimals": S_TEXT,
      "radial_boundaries_exact_decimals": A_TEXT,
      "scale_breakpoint_intervals": [{"lo":x,"hi":x} for x in S_TEXT],
      "radial_breakpoint_intervals": [{"lo":x,"hi":x} for x in A_TEXT],
      "pi_outward": {"lo": floor_decimal(piv.lo), "hi": ceil_decimal(piv.hi), "method":"Machin + alternating rational series"},
      "low_outward": {"lo": floor_decimal(low.lo), "hi": ceil_decimal(low.hi), "proved_gt_target": True},
      "high_bins": [{"bin":j, "kernel_integral_exact":fstr(ints[j]),
                     "coefficient_lower":floor_decimal(coeff_lbs[j]), "proved_gt_target":True} for j in range(7)],
      "dyadic_tail": {"first_kernel_integral_exact":fstr(tail_int),
                       "first_coefficient_lower":floor_decimal(tail_lb),
                       "all_later_bins_ge_first_by_exact_scaling":True,
                       "proved_gt_target":True},
      "minimum_proved_lower": floor_decimal(min_lb),
      "strict_margin_lower": floor_decimal(min_lb-TARGET),
      "price_certificate": {"finite_half_open_atoms":atoms,
          "tail":"for n>=1, high tail n owns [2^(n-1) S6, 2^n S6) at price 1",
          "pointwise_total_price_upper_exact":"1", "proved":True},
      "proof_notes": [
        "Decimal breakpoints are interpreted as exact base-10 rationals (degenerate rational intervals).",
        "Each high integral is split at 1, s-1/2, s and integrated as an exact polynomial.",
        "High coefficient lower bounds divide by the rigorously enclosed upper endpoint of pi.",
        "Low transcendental expressions use outward rational intervals throughout.",
        "For tail kernel scale s>=2*S6, the normalized coefficient is exactly 1/(8*pi)-1/(16*pi*s), hence increases with s; the first tail bin is worst."
      ]
    }


def main() -> None:
    ap=argparse.ArgumentParser(); ap.add_argument("--write", action="store_true")
    args=ap.parse_args(); receipt=build_receipt()
    path=Path(__file__).with_name("radial_price_certificate_receipt.json")
    if args.write:
        path.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+"\n")
        print(f"wrote {path}")
    else:
        assert path.exists(), f"missing {path}; run with --write once"
        stored=json.loads(path.read_text())
        assert stored == receipt, "receipt does not exactly match recomputation"
    print("low lower =",receipt["low_outward"]["lo"])
    print("high lowers =",*[x["coefficient_lower"] for x in receipt["high_bins"]])
    print("tail lower =",receipt["dyadic_tail"]["first_coefficient_lower"])
    print("minimum proved lower =",receipt["minimum_proved_lower"])
    print("strict margin lower =",receipt["strict_margin_lower"])
    print("RADIAL_PRICE_EXACT_CERTIFICATE_OK")

if __name__ == "__main__": main()
