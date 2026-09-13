# ATTACKS — small-radius paired persistence

| gate | outcome |
|---|---|
| `h=0` diameter | survives: `beta=0`, no discarded mass, antipodal singleton tracks are retained |
| foot endpoint | excluded by `M<=q<1`, since its far endpoint has radius `sqrt(h^2+1)>=1` |
| `M=q` boundary | belongs to the closed near class; common reach `1-q` is non-strict and valid |
| `M>q` complement | used only with conservative reach `q`; strictness is not converted into a fake gap |
| legal high-frequency alternating selector | survives: proof is pointwise plus outer measure, with no continuity/BV/measurable sign |
| cross-direction swapped tracks | exact overlap exists, but both anchors lie in the adaptive bad cut-ball and are paid for by proportional discarded mass |
| nonmeasurable `A` | handled by a measurable hull `G superset A`, `|G|=|A|*`, then Caratheodory splitting by the cut-ball |
| projective quotient | cut is on `T_pi`; canonical lifts only label the two branches, and their union is invariant when the cut changes |
| `H=u` | coefficient is zero because the bad ball is the whole projective circle; no false positive width |
| `u=R` | shell width and coefficient are zero |
| zero direction mass | proportional right side is zero; no atom is assigned positive direction mass |

## 1. Why the averaged cut is legal for nonmeasurable classes

Averaging `|A intersect B(c,beta)|*` directly would be unjustified.  Instead take
a measurable hull `G` with `A subset G` and `|G|=|A|*`.  Fubini is applied only
to measurable `G`:

```text
integral_{T_pi} |G intersect B(c,beta)| dc = 2 beta |G|.
```

For one cut the intersection is at most `(2 beta/pi)|A|*`.  Because the ball is
measurable, Caratheodory gives an exact outer-measure split of `A` into good and
bad directions.  No selector is integrated.

## 2. Swapped-track control

For fixed `h,u,R`, put `a_R=asin(h/R)`, `a_u=asin(h/u)` and
`k=a_R+a_u`.  The positive arc anchored at `pi-k/2` equals the negative arc
anchored at `k/2`.  Relative to the projective cut `0`, both anchors have distance
`k/2<=a_u=beta`; hence both are in the discarded ball.  This shows simultaneously
that global track disjointness is false and that the adaptive theorem charges the
actual obstruction proportionally rather than subtracting the whole cut strip.

## 3. Double-count attack

The paired payment occupies `(H,alpha_1)`.  The CFS low support begins at
`alpha_1`.  A complement upgrade is allowed only by replacing the old `R=1/2`
action on `J subset [alpha_1,alpha_2)` with the `R_c` action; it is never added on
top.  Therefore the first-class columns are literally

```text
near:       p0 - integral_J K(u,1/2) du + P_pair,
complement: p0 + integral_J (K(u,R_c)-K(u,1/2)) du.
```

All later rows are unchanged because their first-window integrals start at
`alpha_2` or later.  A mutation moving `J` past `alpha_2`, taking `H=alpha_1`, or
using an oversized slice fails in tests.

## 4. What is and is not proved

The adaptive-cut theorem and the existence of a sufficiently short improving
replacement interval are continuum statements.  The displayed floating witness
is not an exact transcendental certificate.  This spike does not claim optimality,
a quantified new headline, or simultaneous same-shell R+paired capacity.
