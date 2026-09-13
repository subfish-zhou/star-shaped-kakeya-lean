#!/usr/bin/env python3
"""Seven preregistered exact controls, not a numerical search or geometry proof."""
from fractions import Fraction as F

HALF = F(1, 2)


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def collar_ratio(M, r):
    return min(HALF, max(F(0), M-r))/M


def old(m, R, r):
    return min(HALF, max(F(0), m-r))/R


def joint(m, R, r):
    return min(1/(2*R), max(F(0), 1-r/m))


# All cases and expected answers are fixed in ADMISSION.md before execution.
CASES = (
    (F(1), F(2), F(1, 3), F(1, 4), F(1, 4)),
    (F(1), F(2), F(1, 2), F(1, 4), F(1, 4)),
    (F(1), F(2), F(3, 4), F(1, 8), F(1, 4)),
    (F(1), F(2), F(7, 8), F(1, 16), F(1, 8)),
    (F(1), F(2), F(1), F(0), F(0)),
    (F(1), F(1), F(3, 4), F(1, 4), F(1, 4)),
)

for i, (m, R, r, expected_old, expected_joint) in enumerate(CASES, 1):
    actual_old, actual_joint = old(m, R, r), joint(m, R, r)
    check(actual_old == expected_old, f"old control {i}")
    check(actual_joint == expected_joint, f"joint control {i}")
    check(actual_joint == min(collar_ratio(m, r), collar_ratio(R, r)),
          f"endpoint evaluation {i}")
    check(actual_joint >= actual_old, f"dominance {i}")
    strict = m < R and max(F(0), m-HALF) < r < m
    check((actual_joint > actual_old) == strict, f"strict region {i}")
    print(f"PASS {i}: (m,R,r)=({m},{R},{r}); pi*old={actual_old}; pi*joint={actual_joint}")

m, R, u, v = F(99, 100), F(8, 5), F(49, 100), F(5, 8)
switch = m*(1-1/(2*R))
check(switch > v, "new plateau does not cover accepted terminal support")
check(u == m-HALF, "old plateau endpoint")


def primitive(r):
    return r**3/3-u*r**2/2


gain = (primitive(v)-primitive(u))/R
d = v-u
independent_gain = (u*d**2/2+d**3/3)/R
check(gain == independent_gain and gain > 0, "fixed accepted-price gain")
print(f"PASS 7: r_*={switch}; pi*terminal_payment_gain={gain}")
print("PASS: 7 fixed rational controls; no search; geometry proof is in PROOF.md")
