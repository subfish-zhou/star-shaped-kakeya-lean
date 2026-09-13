"""Fixed arithmetic for CONDITIONAL_TENTH_BRIDGE.md; no geometric promotion."""
from fractions import Fraction as F
from flint import arb, ctx
ctx.prec = 192


def need(value, message):
    if not value:
        raise ValueError(message)


pi = arb.pi()
need(pi > arb(223)/71, 'rational lower bound for pi')
m = F(99, 100)
rows = [(F(1,2), F(3,5), F(7,30)),
        (F(3,5), F(7,10), F(29,169)),
        (F(7,10), F(4,5), F(19,179))]
f = F(7,30)
threshold = 128*f/(5*(1-f))
need(threshold > 0 and 63-threshold**2 == F(30359,13225), 'finite-high cap')
for a, b, k in rows:
    need((m-b)/(m+b) >= k and f >= k, 'step below both cap branches')
raw = sum((k*(b*b-a*a)/2 for a,b,k in rows), F(0))
need(raw == F(446059,13962000), 'finite-high integral')
excess = F(223,71)*raw-F(1,10)
need(excess == F(340957,991302000) and excess > 0, 'finite-high payment')
need(35**2*255-512**2 > 0, 'first-tail cap')
need((F(8,5)-F(6,5))/(F(8,5)+F(6,5)) == F(1,7) > F(1,8), 'tail rational branch')
tail_raw = ((1-F(4,5)**2)/2 + F(6,5)-1)/8
need(tail_raw == F(19,400) and 3*tail_raw > F(1,10), 'tail subband')
k = F(11,15)
a = (1-k)/2
primitive = lambda r: r*r/2-2*r**3/3
low_raw = k*a*a/2+primitive(F(1,2))-primitive(a)
need(low_raw == F(3311,81000) and 3*low_raw-F(1,10) == F(611,27000), 'conditional low integral')
need(F(27,256) > F(1,10), 'inherited later-tail minimum')
print('finite_high_per_radian', raw)
print('finite_high_certified_excess_over_tenth', excess)
print('first_tail_per_radian', tail_raw)
print('conditional_low_per_radian', low_raw)
print('PASS_FIXED_CONDITIONAL_BRIDGE_ARITHMETIC; PL/IL unproved; universal_0p1_proved=false')
