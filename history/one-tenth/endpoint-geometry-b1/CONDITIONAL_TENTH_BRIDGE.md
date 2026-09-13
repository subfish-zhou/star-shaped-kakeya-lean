# Conditional one-tenth bridge: one precise low-source obligation

Status: **conditional implication, not a proof of0.1**. B1 endpoint-domain Theorem2 has passed independent review; the paired low statement below remains unproved. The full conditional assembly is separately being audited. This note freezes a small hand-chosen disjoint-bank composition so that a successful new low lemma has an explicit path to the original target. No price search or optimizer was used.

## 1. One sufficient low obligation, not an imposed necessary surrogate

For every Borel unit-chord selector with |h|<=1/5, let L be its directions with far radius M<99/100. All such chords straddle their perpendicular foot. Let W(L) be their **literal** anchored-triangle union and S_r(L) its physical-circle section.

The pointwise candidate is

`|S_r(V)| >= min(11/15,1-2r)|V|`, for every Borel V⊆L and 0<r<1/2.       (PL)

This is NOT proved by the scalar calculation below. A strictly weaker alternative sufficient for the same final bridge is the integrated statement

`integral_0^{1/2} r |S_r(L)| dr >= |L|/(10*pi)`.                         (IL)

A counterexample to(PL) does not refute(IL), and a failure of this fixed-bank(IL) would not refute area0.1 by other accounting. Do not replace the original problem by the strongest candidate as a matter of habit.

If(PL) holds, integrating gives coefficient `3311*pi/81000>1/10`; the weaker bound pi>3 already leaves margin611/27000. Thus(PL) implies(IL).

## 2. Why a paired lemma is plausible, and where its proof is missing

The low endpoints have opposite longitudinal signs and radii M,N with M+N>=1. For r<1/2, elementary algebra gives

`((M-r)_+)/(M+r) + ((N-r)_+)/(N+r) >= 1-2r`.                         (S)

If one radius is below r, the other exceeds1-r and its sole summand suffices. If both exceed r, monotonicity lets us reduce their sum to1. With x=M, N=1-x, the difference from1-2r is

`(x-r)(1+2r)(1-r-x) / ((x+r)(1+r-x)) >=0`, for r<=x<=1-r.

For an individual positive-height straddling chord, at r>|h| each existing endpoint lobe has the one-sided extension coefficient underlying its corresponding summand. The endpoint constraints prevent simultaneously using the far-radius minimum1/2 and a vanished near lobe.

**The missing step is a physical-union theorem:** variable per-label endpoint coefficients cannot simply be summed and integrated. Need one source-once estimate for the actual two lobes with their common height, opposite ideal anchors, endpoint relation, changing active lobe, and collisions with other labels. At r<=|h| the two pieces merge into the cone and cannot be charged twice. The fixed cone cap handles such labels individually, but mixing them with lobe labels still belongs to the proposed all-cut proof.

This is an explicit proof obligation, not an inferred transport theorem. Arbitrary independent arc pairs need not satisfy it.

## 3. Finite-high can be paid on [1/2,4/5] without low or tail overlap

Let F={99/100<=M<8/5}. B1 endpoint-domain Theorem2, if accepted, gives on all F

`g_F(r)=min(K_F,(99/100-r)/(99/100+r))`,
`K_F=5sqrt(63)/(5sqrt(63)+128)>7/30`.

The latter follows by a positive-square comparison with residual30359/13225. Use only the following lower step profile, at radial price1:

| Physical radial bank | Guaranteed section coefficient |
|---|---|
| [1/2,3/5) | 7/30 |
| [3/5,7/10) | 29/169 |
| [7/10,4/5) | 19/179 |

The decreasing rational branch at each right endpoint proves the row bound. The total coefficient per radian is exactly446059/13962000. Therefore the area coefficient is

`pi*446059/13962000 > (223/71)*446059/13962000`
`= 1/10 + 340957/991302000 >1/10`.

The source is the union for F once, including pole directions. This is not three copies of F: the banks are disjoint.

## 4. First tail: a fixed subband already suffices with the new cone kernel

Let D0={8/5<=M<16/5}. The same candidate theorem gives

`g_D0(r)=min(K_D0,(8/5-r)/(8/5+r))`,
`K_D0=5sqrt(255)/(5sqrt(255)+512)>1/8`.

The positive-square test is `35^2*255-512^2>0`. On [4/5,6/5], the other branch is at least1/7, so the section coefficient is at least1/8. Using price1 only there gives area coefficient

`pi*(1/8)*integral_[4/5,6/5] min(r,1) dr =19*pi/400 >1/10`.

This is an alternative to the parent collar candidate and requires only the endpoint-domain theorem already used for F. No payment is taken on [6/5,8/5].

For D_n={2^n*(8/5)<=M<2^(n+1)*(8/5)}, n>=1, retain the OLD accepted terminal receipt on [2^(n-1)*(8/5),2^n*(8/5)]. Its least area coefficient is27/256>1/10 and monotonicity proves every later scale. No new infinite-tail computation is needed.

## 5. Conditional continuum implication

Take an arbitrary open G covering the original star-shaped unit-chord Kakeya set, recover a Borel selector as in the accepted baseline, and rerun the height dichotomy. A triangle of height>=1/5 already gives |G|>=1/10. Otherwise partition the recovered directions into L,F,D0,D1,... as above.

The proposed low bank [0,1/2], the finite-high bank [1/2,4/5], the first-tail bank [4/5,6/5], and all later bands [8/5,16/5],... are disjoint (endpoints null). For dnu=min(r,1)dr dtheta, every class receipt is paid from its actual subunion at price1 on its bank. Hence their sum is at mostnu(W)<=|G|. If(IL) and the finite-high endpoint theorem are valid, each class receives at least |class|/(10*pi); classes partitionRP1 of measurepi. Monotone convergence gives |G|>=1/10, then outer regularity gives |E|*>=1/10.

No centered/equal-height assumption, cardinality bound or finite C2+C5 reduction occurs in this implication. The actual unproved bridge is(IL), with(PL) one attractive sufficient route. The high-side theorem is now independently accepted, but the assembly and low-source gates are separate. Until those gates pass, the global retained lower bound remains0.082812499999972190.

## Fixed arithmetic controls

Only the displayed hand-derived coefficients, cap guards, exact integrals and the known rational pi comparison are checked by `conditional_bridge_check.py`. These controls do not sample or prove(PL)/(IL). No optimizer or candidate sweep was run.
