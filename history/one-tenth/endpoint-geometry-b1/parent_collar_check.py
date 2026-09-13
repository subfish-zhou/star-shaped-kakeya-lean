"""Two fixed scalar checks conditional on the unreviewed parent collar lemma.
No geometry verification, parameter search, or bound promotion.
"""
from flint import arb, ctx
ctx.prec = 192
finite_gain = arb.pi() * arb(2001).sqrt() / 98
tail_gain = arb.pi() * arb(117).sqrt() / 22
tail_area = arb(53) / 640 * tail_gain
if not finite_gain > 1:
    raise ValueError('finite-high gain not outward certified')
if not tail_area > arb(1) / 10:
    raise ValueError('conditional tail coefficient not outward certified')
print('finite_high_linear_gain', finite_gain)
print('first_tail_linear_gain', tail_gain)
print('conditional_first_tail_area', tail_area)
print('PASS_TWO_FIXED_SCALARS: parent geometry remains unreviewed; 0.1 unproved')
