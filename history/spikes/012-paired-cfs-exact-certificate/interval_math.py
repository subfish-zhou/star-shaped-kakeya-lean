"""Auditable rational outward bounds used by the frozen certificate."""
from fractions import Fraction as Q
from math import isqrt


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def atan_interval(x: Q, count: int) -> tuple[Q, Q]:
    need(0 <= x < 1 and count > 0, "atan series domain")
    s = sum(((-1 if k % 2 else 1) * x ** (2 * k + 1) / (2 * k + 1)
             for k in range(count)), Q(0))
    nxt = x ** (2 * count + 1) / (2 * count + 1)
    return (s, s + nxt) if count % 2 == 0 else (s - nxt, s)


def pi_interval() -> tuple[Q, Q]:
    """Machin: pi=16 atan(1/5)-4 atan(1/239), alternating outward bounds."""
    a_l, a_u = atan_interval(Q(1, 5), 12)
    b_l, b_u = atan_interval(Q(1, 239), 4)
    lo, hi = 16 * a_l - 4 * b_u, 16 * a_u - 4 * b_l
    need(lo < hi, "pi enclosure")
    return lo, hi


def log_interval(y: Q, count: int) -> tuple[Q, Q]:
    need(y >= 1 and count == 14, "frozen log contract")
    z = (y - 1) / (y + 1)
    need(0 <= z < 1, "atanh domain")
    body = sum((z ** (2 * k + 1) / (2 * k + 1) for k in range(count)), Q(0))
    tail = z ** (2 * count + 1) / ((2 * count + 1) * (1 - z * z))
    return 2 * body, 2 * (body + tail)


def ledger_interval(a: Q, b: Q, radius: Q, count: int) -> tuple[Q, Q]:
    need(0 <= a <= b <= radius, "ledger interval")
    ll, lu = log_interval((radius + b) / (radius + a), count)
    polynomial = -(b * b - a * a) / 2 + 2 * radius * (b - a)
    return polynomial - 2 * radius * radius * lu, polynomial - 2 * radius * radius * ll


def sqrt_interval(x: Q, digits: int = 40) -> tuple[Q, Q]:
    need(x >= 0, "sqrt domain")
    scale = 10 ** digits
    floor = isqrt(x.numerator * scale * scale // x.denominator)
    while Q((floor + 1) ** 2, scale * scale) <= x:
        floor += 1
    while Q(floor * floor, scale * scale) > x:
        floor -= 1
    lo = Q(floor, scale)
    return lo, lo if lo * lo == x else Q(floor + 1, scale)


def asin_direct_interval(x: Q, count: int) -> tuple[Q, Q]:
    need(0 <= x < 1 and count == 80, "asin direct contract")
    coeff = Q(1)
    body = Q(0)
    for k in range(count):
        if k:
            coeff *= Q((2 * k - 1) ** 2, (2 * k) * (2 * k + 1))
        body += coeff * x ** (2 * k + 1)
    # All coefficients are <=1, so this geometric majorant is outward.
    tail = x ** (2 * count + 1) / (1 - x * x)
    return body, body + tail


def asin_interval(x: Q, count: int) -> tuple[Q, Q]:
    need(0 <= x <= 1, "asin domain")
    pi_l, pi_u = pi_interval()
    if x <= Q(1, 2):
        return asin_direct_interval(x, count)
    y_l, y_u = sqrt_interval(1 - x * x)
    yl_l, _ = asin_direct_interval(y_l, count)
    _, yu_u = asin_direct_interval(y_u, count)
    return pi_l / 2 - yu_u, pi_u / 2 - yl_l


def paired_integral_interval(H: Q, a: Q, b: Q, radius: Q,
                             subdivisions: int, asin_terms: int,
                             test_fault: str | None = None) -> tuple[Q, Q]:
    need(0 < H == a < b < radius, "paired support")
    need(subdivisions == 128 and asin_terms == 80, "frozen paired quadrature")
    need(test_fault in (None, "asin_wrong_direction"), "unknown paired test fault")
    # On this frozen range g(u)=2u(R-u)/(R+u) and the angular factor increase.
    need(radius * radius - 2 * radius * b - b * b > 0, "paired monotonicity")
    pi_l, pi_u = pi_interval()
    step = (b - a) / subdivisions

    def factor_interval(u: Q) -> tuple[Q, Q]:
        al, au = asin_interval(H / u, asin_terms)
        # Test-only production-tooth mutation: reverse the lower-integrand asin
        # enclosure itself, rather than changing a descriptive JSON label.
        lower_asin = al if test_fault == "asin_wrong_direction" else au
        return 1 - 2 * lower_asin / pi_l, 1 - 2 * al / pi_u

    def g(u: Q) -> Q:
        return 2 * u * (radius - u) / (radius + u)

    lower = Q(0)
    upper = Q(0)
    for k in range(subdivisions):
        left, right = a + k * step, a + (k + 1) * step
        fl, _ = factor_interval(left)
        _, fu = factor_interval(right)
        lower += step * g(left) * max(Q(0), fl)
        upper += step * g(right) * min(Q(1), fu)
    return lower, upper
