#!/usr/bin/env python3
"""One preregistered rational control, no numerical trig or search.

The continuum argument is in COUNTEREXAMPLE.md. This checker only verifies
its exact rational guards and its polynomial identity. Checks survive -O.
"""
from fractions import Fraction as Q


def require(name, predicate, value=None):
    if not predicate:
        raise RuntimeError(f"FAIL {name}: {value}")
    print(f"PASS {name}" + (f": {value}" if value is not None else ""))


def main():
    e, r, a, delta, d, g = Q(1, 100), Q(1, 4), Q(4, 5), Q(2, 5), Q(5, 2), Q(3, 2)
    k = 1 - e * e
    print("CONTROL B2-PL-01: epsilon=1/100 r=1/4 a=4/5 delta=2/5 d=5/2 g=3/2")
    require("small-angle domain", Q(7, 4) * e < 1)
    require("uniform sine factor", Q(7, 4) ** 2 / 6 < 1)
    require("uniform cosine factor", delta ** 2 / 2 < 1)
    outer_margin = (1 + delta) * k * k - (a / r) * delta
    require("outer-host inclusion", outer_margin > 0, outer_margin)
    h_outer = a * delta * e / k
    require("outer height < epsilon", h_outer < e, h_outer)
    require("outer near inactive", (1-a)**2 + e**2 < r**2, r**2 - (1-a)**2 - e**2)
    require("outer far low", a**2 + e**2 < Q(99,100)**2, Q(99,100)**2-a**2-e**2)
    require("outer far orientation", a > Q(1,2))
    # Exact coefficient identity in w, ordered constant, linear, quadratic.
    lhs = [Q(1,4), Q(1,4)-Q(1), 1/g]
    rhs = [Q(2,3)*Q(9,16)**2 + Q(5,128), -Q(4,3)*Q(9,16), Q(2,3)]
    require("central square-completion identity", lhs == rhs, lhs)
    central_margin = Q(5,128) - Q(7,8)*e**2
    require("central paired-host inclusion", central_margin > 0, central_margin)
    endpoint_max = Q(11,15)/k
    endpoint_min = Q(4,15)*k
    require("central endpoints low", endpoint_max < Q(99,100), endpoint_max)
    require("central both lobes active", endpoint_min > r, endpoint_min)
    h_central = Q(3,8)*e/k
    require("central height", h_central < min(r,Q(1,5)), h_central)
    require("all angles acute where used", g*e < 1)
    # Host singleton rows are inside the corresponding exterior pieces.
    require("left host covered", -delta <= 0 and 1 <= 1+delta)
    require("right host covered", d-delta <= d and d+1 <= d+1+delta)
    source = 2*e
    demand = (d+1+2*delta)*e
    coefficient = min(Q(11,15),1-2*r)
    deficit = coefficient*demand-source
    require("candidate coefficient", coefficient == Q(1,2), coefficient)
    require("cut length", demand == Q(43,1000), demand)
    require("literal union length", source == Q(1,50), source)
    require("strict PL counterexample", deficit == Q(3,2000) and deficit > 0, deficit)
    print("RESULT: one fixed control PASS; PL FALSE for the analytically proved literal Borel family; IL NOT DECIDED.")


if __name__ == "__main__":
    main()
