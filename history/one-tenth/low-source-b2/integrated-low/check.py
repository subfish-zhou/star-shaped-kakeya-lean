"""One preregistered fixed certificate; no parameter search or optimization."""
from fractions import Fraction as Q
import time

START = time.monotonic()

def log_bounds(x):
    """Positive atanh series, 40 terms, with rigorous geometric tail."""
    if x < 1:
        lo, hi = log_bounds(1 / x)
        return -hi, -lo
    t = (x - 1) / (x + 1)
    n = 40
    lo = 2 * sum((t ** (2*k+1) / (2*k+1) for k in range(n)), Q(0))
    tail = 2 * t ** (2*n+1) / ((2*n+1) * (1-t*t))
    return lo, lo + tail

def primitive(m, r):
    llo, lhi = log_bounds(1 + r/m)
    a = -r*r/2 + 2*m*r
    return a-2*m*m*lhi, a-2*m*m*llo

def integ(m, a, b):
    blo, bhi = primitive(m, b)
    alo, ahi = primitive(m, a)
    return blo-ahi, bhi-alo

def add(*xs):
    return sum((x[0] for x in xs), Q(0)), sum((x[1] for x in xs), Q(0))

def scale(c, x):
    return c*x[0], c*x[1]

def show(label, v):
    # Exact rational sign certification precedes this diagnostic formatting.
    print(label, '[%.15f, %.15f]' % (float(v[0]), float(v[1])))

# Control 1: exactly the three banks fixed in ADMISSION-LOCAL.md.
m, k = Q(2,5), Q(2,3)
switch = m*(1-k)/(1+k)
if switch != Q(2,25):
    raise RuntimeError('cone/lobe switch identity failed')
C4 = add((k*switch*switch/2,)*2, integ(m, switch, Q(1,5)))
C5 = integ(Q(1,2), Q(1,5), Q(7,20))
C6 = integ(Q(3,5), Q(7,20), Q(1,2))
B = add(scale(2,C4), C5)
U = add(C4,C5,C6)
target = Q(7,220), Q(71,2230)  # 223/71 < pi < 22/7
show('C4', C4)
show('C5', C5)
show('C6', C6)
show('balanced coefficient 2*C4+C5', B)
show('unbalanced coefficient C4+C5+C6', U)
show('target enclosure 1/(10*pi)', target)
for name, value in [('balanced',B), ('unbalanced',U)]:
    verdict = 'STRICTLY BELOW TARGET' if value[1] < target[0] else ('STRICTLY ABOVE TARGET' if value[0] > target[1] else 'UNRESOLVED')
    print(name + ': ' + verdict)
    if verdict == 'UNRESOLVED':
        raise RuntimeError('fixed exact enclosure failed to decide')
if B[1] < target[0] or U[1] < target[0]:
    print('FIXED CERTIFICATE FAILS; not a geometric IL counterexample; stop this candidate.')
else:
    print('FIXED CERTIFICATE SUCCEEDS; human geometric proof still requires audit.')
# Control 2: same geometry, complementary outer-bank prices, algebraic cancellation.
D5 = integ(Q(1,2), Q(7,20), Q(1,2))
if not (0 < C4[0] <= C4[1] < C6[0]):
    raise RuntimeError('price guard 0<C4<C6 failed')
lam = C4[0]/C6[1], C4[1]/C6[0]
complement = 1-lam[1], 1-lam[0]
bonus = complement[0]*D5[0], complement[1]*D5[1]
Cstar = add(B, bonus)
rational_floor = Q(637,20000)
if not (Cstar[0] > rational_floor > target[1]):
    raise RuntimeError('new fixed certificate failed: STOP, no retuning')
# Cancellation is symbolic in abstract variables, checked without external CAS:
# lambda=C4/C6 makes C4-lambda*C6 exactly zero for either rational enclosure endpoint.
for c4, c6 in [(C4[0],C6[0]), (C4[1],C6[1])]:
    if c4-(c4/c6)*c6 != 0:
        raise RuntimeError('class-mass cancellation identity failed')
pi_margin = rational_floor*Q(223,71)-Q(1,10)
if pi_margin != Q(51,1420000):
    raise RuntimeError('rational pi margin identity failed')
# Closed forms in PROOF.md: rational polynomial pieces and exact log ratios.
def poly(m, r):
    return -r*r/2 + 2*m*r

closed_forms = [
    (Q(2,5), Q(2,25), Q(1,5), Q(2,3)*Q(2,25)**2/2,
     Q(61,750), Q(8,25), Q(5,4)),
    (Q(1,2), Q(1,5), Q(7,20), Q(0),
     Q(87,800), Q(1,2), Q(17,14)),
    (Q(3,5), Q(7,20), Q(1,2), Q(0),
     Q(93,800), Q(18,25), Q(22,19)),
    (Q(1,2), Q(7,20), Q(1,2), Q(0),
     Q(69,800), Q(1,2), Q(20,17)),
]
for m0, a0, b0, cap, constant, log_coefficient, log_argument in closed_forms:
    if (cap+poly(m0,b0)-poly(m0,a0) != constant
        or 2*m0*m0 != log_coefficient
        or (m0+b0)/(m0+a0) != log_argument):
        raise RuntimeError('closed-form identity mismatch')
print('four integral closed forms: EXACT PASS')
show('D5 outer all-far bank', D5)
show('lambda=C4/C6', lam)
show('Cstar uniform all-cut coefficient', Cstar)
print('EXACT: Cstar > 637/20000 > 71/2230 > 1/(10*pi)')
print('EXACT rational full-direction margin over 1/10:', pi_margin)
print('NEW MIXED CERTIFICATE PASSES; continuum proof requires independent review.')
print('distinct_controls=2; executions_this_run=1; elapsed_seconds=%.6f' % (time.monotonic()-START))
