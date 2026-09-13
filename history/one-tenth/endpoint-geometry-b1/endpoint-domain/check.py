#!/usr/bin/env python3
"""Six fixed exact controls; human all-cut proofs are not formalized here."""
from fractions import Fraction as F
from time import perf_counter
import sympy as S

start = perf_counter()
count = 0


def require(condition, description):
    if not bool(condition):
        raise RuntimeError(description)


def passed(description):
    global count
    count += 1
    print(f"PASS control {count}: {description}")


x, h, t, A, r, m = S.symbols("x h t A r m", positive=True)
M2 = x*x + h*h
N2 = (x-1)**2 + h*h
require(S.expand(N2 - (M2 + 1 - 2*x)) == 0, "joint endpoint identity")
require(S.simplify(S.diff(S.atan(t/h), t) - h/(t*t+h*h)) == 0,
        "cone-angle primitive")
num = x*x+h*h-A*((1-x)**2+h*h)
require(S.expand(S.diff(num, x) - (2*x+2*A*(1-x))) == 0,
        "single-minimum derivative numerator")
Q = -r*r/2 + 2*m*r - 2*m*m*S.log(1+r/m)
require(S.simplify(S.diff(Q, r)-r*(m-r)/(m+r)) == 0,
        "radial primitive")
print("PASS symbolic identities: joint endpoints, cone integral, endpoint maximum, radial primitive")


def point_in_triangle(x, h, px, py):
    lam = py/h
    return 0 <= lam <= 1 and lam*(x-1) <= px <= lam*x


# 1: centered chord, full cone below its minimum radius.
x, h, r = F(1,2), F(3,20), F(1,10)
M2, N2 = x*x+h*h, (x-1)**2+h*h
require(r*r < h*h < N2 == M2, "centered radius order")
require(point_in_triangle(x, h, F(0), r), "centered radial filling")
passed("centered: r^2<h^2<N^2=M^2; (0,r) belongs to triangle")

# 2: exterior foot, full cone with r>h but r<N.
x, h, r = F(3,2), F(1,5), F(1,4)
M2, N2 = x*x+h*h, (x-1)**2+h*h
px, py = F(6,25), F(7,100)
require(h*h < r*r < N2 < M2, "exterior radius order")
require(px*px+py*py == r*r, "exterior circle point")
require(point_in_triangle(x, h, px, py), "exterior radial filling")
passed("exterior: h^2<r^2<N^2<M^2; exact circle point (6/25,7/100) lies in triangle")

# 3: closest point becomes an endpoint.
x, h, r = F(1), F(1,5), F(1,10)
M2, N2 = x*x+h*h, (x-1)**2+h*h
require(N2 == h*h and M2-h*h == x*x, "foot endpoint boundary")
require(N2 == M2+1-2*x, "boundary joint endpoints")
require(point_in_triangle(x, h, F(0), r), "boundary radial filling")
passed("foot boundary: a^2=N^2=h^2 and circle point remains in triangle")

# 4: old and new low-cap guards, without evaluating any trig function.
M0, H = F(99,100), F(1,5)
sin_half_alpha = 1/(2*M0)
cos_alpha = 1-2*sin_half_alpha*sin_half_alpha
require(cos_alpha > 0, "alpha<pi/2")
require(cos_alpha*cos_alpha > F(1,401), "alpha<atan(20)=beta")
require(F(22,7) < F(16,5), "pi/2<8/5 using pi<22/7")
require(F(2,3) < F(11,15) < F(13,17), "low cap rational separation")
require(F(49,51) > F(11,15), "small-radius far branch")
passed("low: alpha<pi/2, alpha<beta; old caps<2/3<11/15<new caps")

# 5: exact finite-high cap K=5*sqrt(63)/(5*sqrt(63)+128).
m, R, H, r = F(99,100), F(8,5), F(1,5), F(5,8)
require(R*R-H*H == F(63,25), "finite-high joint maximum")
f = (m-r)/(m+r)
require(f == F(73,323), "window coefficient")
# K>f iff sqrt(63) > 128*f/(5*(1-f)); square only positive terms.
threshold = 128*f/(5*(1-f))
require(threshold > 0 and F(63) > threshold*threshold, "cone cap retains window")
passed("finite-high: K=5sqrt(63)/(5sqrt(63)+128)>73/323=f(5/8)")

# 6: log bound comes from the positive atanh series in the paper proof.
log_lower = 2*(F(1,3)+F(1,81))
ceiling = F(22,7)*(F(3,8)-log_lower/2)
require(log_lower == F(56,81), "log lower rational identity")
require(ceiling == F(209,2268) < F(1,10), "low full-price obstruction")
passed("low full-price ceiling <209/2268<1/10")

require(count == 6, "registered control count")
print("RESULT: PASS; 6/12 fixed controls used; no searches or numerical quadratures")
print(f"Script wall seconds: {perf_counter()-start:.6f}")
