"""Independent fixed seven-row arithmetic checker. No receipt-file writes."""
from fractions import Fraction as F
from pathlib import Path
import json

FIXED = dict(zip(('H', 'M0', 'R', 'x', 'y', 'z', 'epsilon', 'target'), (
    '1/5', '99/100', '8/5', '316269962741/999999000000',
    '96233328491/142857000000', '9039395633/111111000000',
    '1/999999000000', '0.082812499999972190')))


def load():
    return json.loads(Path(__file__).with_name('witness.json').read_text())


def validate(data):
    if set(data) != set(FIXED) or any(type(x) is not str for x in data.values()):
        raise ValueError('fixed witness: exact rational strings required')
    q = {k: F(x) for k, x in data.items()}
    if q != {k: F(x) for k, x in FIXED.items()}:
        raise ValueError('fixed witness parameters/prices changed')
    return q


def rows(data):
    q = validate(data)
    x, y, z, e = (q[k] for k in ('x', 'y', 'z', 'epsilon'))
    grid = tuple(map(F, ('0', '17/40', '9/20', '19/40', '5/8', '31/40', '4/5', '8/5')))
    prices = ((1, 0, 0, 0, 0), (x, 1-x-e, 0, 0, 0),
              (y, 1-y-e, 0, 0, 0), (0, 1, 0, 0, 0),
              (0, 0, 1, 0, 0), (0, 0, z, 1-z-e, 0), (0, 0, 0, 0, 1))
    return [(a, b, tuple(map(F, p))) for a, b, p in zip(grid, grid[1:], prices)]


def source_load(rows):
    loads = [sum(prices, F(0)) for _, _, prices in rows]
    if any(q < 0 for _, _, prices in rows for q in prices):
        raise ValueError('negative price')
    if any(q > 1 for q in loads):
        raise ValueError('source overload')
    return max(loads)


from flint import arb, ctx
ctx.prec = 192
BRANCHES = ('low', 'positive+terminal', 'pole+terminal', 'first-tail', 'later-tail')


def A(q):
    q = F(q)
    return arb(q.numerator) / arb(q.denominator)


def Q(m, r):
    """Primitive of r(m-r)/(m+r); m and r are Arb balls."""
    return -r*r/2 + 2*m*r - 2*m*m*(1+r/m).log()


def terminal_integral(s, a, b):
    """Exact integral min(r,1) min(1/2,(s-r)_+) over [a,b]."""
    s, a, b = map(F, (s, a, b))
    cuts = sorted({a, b} | {t for t in (F(1), s-F(1, 2), s) if a < t < b})
    total = F(0)
    for u, v in zip(cuts, cuts[1:]):
        mid = (u+v)/2
        c, d = (F(1, 2), F(0)) if mid < s-F(1, 2) else (s, F(-1))
        if mid >= s:
            continue
        if mid < 1:
            total += c*(v*v-u*u)/2 + d*(v**3-u**3)/3
        else:
            total += c*(v-u) + d*(v*v-u*u)/2
    return total


def receipts(data):
    q = validate(data)
    table = rows(data)
    source_load(table)  # Rational sums, NOT upper endpoints of rounded Arb sums.
    H, M0, R = (q[k] for k in ('H', 'M0', 'R'))
    # N(M,H)^2 < (5/8)^2: square only after checking a positive RHS.
    for M in (M0, R):
        rhs = (M*M+1-F(5, 8)**2)/2
        if not (rhs > 0 and M*M-H*H > rhs*rhs):
            raise ValueError('positive support guard')
    if not (max(1-M0, R-1) < F(31, 40) < F(4, 5) < M0):
        raise ValueError('pole support guard')
    m = A(1-M0)
    alpha = 2*(1/(2*A(M0))).asin()
    beta = (A(H)/m).atan()
    ch = 2*alpha/(alpha+2*beta)
    a = m*beta/(alpha+beta)
    kh = alpha/(alpha+2*(2*A(H)).asin())
    c = (1-kh)/(2*(1+kh))
    if not (0 < a < m < c < A('17/40') and a < A(H)):
        raise ValueError('low splice order')
    base = ch*a*a/2 + 2*(Q(m, m)-Q(m, a)) + kh*(c*c-m*m)/2

    def low_primitive(r):
        if r == 0:
            return arb(0)
        if not c < A(r) < A('1/2'):
            raise ValueError('low endpoint outside fixed primitive branch')
        return base + Q(A('1/2'), A(r))-Q(A('1/2'), c)

    low = arb(0)
    terminal, pole_mass, first = F(0), F(0), F(0)
    positive = arb(0)
    for u, v, (pl, pt, pp, pz, pf) in table:
        if pl:
            low += A(pl)*(low_primitive(v)-low_primitive(u))
        terminal += pt*terminal_integral(M0, u, v)/R
        if pp:
            positive += A(pp)*(Q(A(M0), A(v))-Q(A(M0), A(u)))
        pole_mass += pz*(v*v-u*u)/2
        first += pf*terminal_integral(R, u, v)/(2*R)
    # Return pi times each per-radian payment, so the target is the area floor.
    return dict(zip(BRANCHES, (arb.pi()*low,
        A(terminal)+arb.pi()*positive,
        A(terminal)+arb.pi()*A(pole_mass),
        A(first), A(F(1, 8)-1/(16*(2*R))))))


def certify(values):
    if set(values) != set(BRANCHES):
        raise ValueError('arithmetic: branch coverage')
    target = A(FIXED['target'])
    for key in BRANCHES:
        if not arb(values[key]) > target:
            raise ValueError('arithmetic: ' + key)
    return True
