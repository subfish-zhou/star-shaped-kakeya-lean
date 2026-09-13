"""Canonical coefficient replay for THEOREM_01.md; geometry is a paper proof.
Arb reconstruction is independent of the IL checker's rational log series.
"""
from fractions import Fraction as F
from flint import arb, ctx
ctx.prec = 192
BRANCHES = {'low', 'finite_high', 'first_tail', 'later_tail'}


def A(q):
    q = F(q)
    return arb(q.numerator) / q.denominator


def build():
    C4 = A('61/750') - A('8/25') * A('5/4').log()
    C5 = A('87/800') - A('1/2') * A('17/14').log()
    C6 = A('93/800') - A('18/25') * A('22/19').log()
    D5 = A('69/800') - A('1/2') * A('20/17').log()
    if not 0 < C4 < C6 or not D5 > 0:
        raise ValueError('low integral/price guards')
    lam = C4 / C6
    low = 2*C4 + C5 + (1-lam)*D5
    if not low > A('637/20000') > A('71/2230'):
        raise ValueError('low coefficient comparison')
    pi = arb.pi()
    if not pi > A('223/71'):
        raise ValueError('pi bound')
    m = F(99,100)
    rows = ((F(1,2), F(3,5), F(7,30)),
            (F(3,5), F(7,10), F(29,169)),
            (F(7,10), F(4,5), F(19,179)))
    f = F(7,30)
    threshold = 128*f/(5*(1-f))
    if not threshold > 0 or not 63 > threshold**2:
        raise ValueError('finite-high cap guard')
    for _, b, k in rows:
        if not min(f, (m-b)/(m+b)) >= k:
            raise ValueError('finite-high step guard')
    finite = sum((k*(b*b-a*a)/2 for a,b,k in rows), F(0))
    if finite != F(446059,13962000):
        raise ValueError('finite-high integral')
    if not 35**2*255 > 512**2 or not F(1,7) > F(1,8):
        raise ValueError('first-tail cap guard')
    first = ((1-F(4,5)**2)/2 + F(6,5)-1)/8
    if first != F(19,400):
        raise ValueError('first-tail integral')
    values = {'low':pi*low, 'finite_high':pi*A(finite),
              'first_tail':pi*A(first), 'later_tail':A('27/256')}
    return values, lam, pi*(2*C4+C5)


def certify(values, lam):
    if set(values) != BRANCHES:
        raise ValueError('branch coverage')
    if not 0 < lam < 1:
        raise ValueError('complementary price parameter')
    # The other price is symbolically 1-lambda, not a separately rounded load.
    for name in sorted(BRANCHES):
        if not values[name] > A('1/10'):
            raise ValueError('underpaid branch: '+name)


if __name__ == '__main__':
    values, lam, _ = build()
    certify(values, lam)
    print('lambda=C4/C6', lam)
    for name in sorted(values):
        print(name, values[name], '> 1/10')
    print('PASS_ONE_TENTH_COEFFICIENTS; human geometric proof and reviews are separate; not Lean')
