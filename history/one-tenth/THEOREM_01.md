# A universal one-tenth lower bound for planar star-shaped Kakeya sets

**Status: ACCEPTED human mathematical proof with rigorous arithmetic checks.** Independent IL geometry, arithmetic, and end-to-end reviews are archived in [tenth-reviews/](tenth-reviews/). The end-to-end verdict is `ACCEPT_UNIVERSAL_0P1`. The reviewed mathematical authorities are the IL proof at `ed84c269e743177aaf1d3776df6ec5eefa05a9f6` and the assembly at `d9a3f3c1b9718fd68b9f95cf10bb2cdd32bb16da`; this document is a parent-checked exposition of that unchanged proof chain.

## Theorem

If E⊆R² is star-shaped with respect to one point and contains a closed unit segment in every unoriented direction, then its Lebesgue outer area satisfies

**|E|* ≥ 1/10.**

No measurability or boundedness of E, regularity of its original selector, common chord height, centering of chords, or bound on the number of directions is assumed. The proof below is a human geometric proof with exact/outward arithmetic, not a Lean kernel certificate.

## 1. Recover a measurable family inside an arbitrary open cover

Translate the star center to0 and fix any open G⊇E. Every selected original unit segment and its anchored triangle lie in E. The triangle is compactly contained in G. Keeping the segment midpoint fixed and varying its direction slightly changes the triangle continuously in Hausdorff distance, so it remains in G on a direction neighborhood. A finite cover of RP¹ and a first-index rule produce a Borel selector with every anchored triangle in G. This uses no regularity of the original selection.

The triangle union W and its direction-restricted unions are analytic and Lebesgue measurable. Rerun the height dichotomy on this recovered selector: if any chord has |h|≥1/5, its triangle already has area≥1/10. Otherwise all |h|<1/5.

The complete recovery and polar-measure justification is [baseline/PROOF.md](baseline/PROOF.md), §§1 and6. G itself need not be star-shaped.

## 2. Physical source and direction classes

Let M,N be the farther/nearer endpoint radii. Use direction measure |RP¹|=π, ordinary physical angles of total length2π, and

`dν=min(1,1/|x|)dx = min(r,1)dr dθ`, so ν(W)≤|G|.

Partition all directions into

- L: M<99/100;
- F: 99/100≤M<8/5;
- D_n: m_n≤M<2m_n, m_n=(8/5)2ⁿ, n≥0.

The classes are Borel and exhaustive. No P/Z split or reflected copy of W is introduced.

## 3. Low bank: the integrated eligible-anchor lemma

For every Borel V⊆L, put B={q∈V:N≥2/5}, U=V\B. The proof in [low-source-b2/integrated-low/PROOF.md](low-source-b2/integrated-low/PROOF.md) establishes

`|W(V)∩D(0,1/2)| ≥ C*|V| > (637/20000)|V| > |V|/(10π)`

for positive-measure V; null cuts satisfy the non-strict inequality.

Its actual source-once mechanism is as follows. For r<2/5, select the far ideal anchor for every q and the opposite near ideal anchor only for B. One simultaneous interval-union estimate on all actual circular bases gives

`|S_r(V)| ≥ min(2/3,(2/5-r)/(2/5+r)) (|V|+|B|)`.

The ideal lifts are disjoint; the physical bases need not be. Duplicate cones and overlapping lobes are merged before measuring the source. On outer radii r>1/5, the all-far coefficients are `(1/2-r)/(1/2+r)` on V and `(3/5-r)/(3/5+r)` on U, because M+N≥1.

Write

- C4 = 61/750 − (8/25)log(5/4);
- C5 = 87/800 − (1/2)log(17/14);
- C6 = 93/800 − (18/25)log(22/19);
- D5 = 69/800 − (1/2)log(20/17).

Then 0<C4<C6, λ=C4/C6∈(0,1), and `C*=2C4+C5+(1−λ)D5>637/20000`.

The inner bank(0,1/5) uses the eligible-anchor estimate; [1/5,7/20) uses the all-far V estimate. On [7/20,1/2), charge U at priceλ and V at price1−λ. Pointwise,

`λ1_W(U)+(1−λ)1_W(V) ≤ 1_W(V)`.

The B and U coefficients both equal C*, proving the integrated lemma. This is not the false pointwise paired inequality PL.

## 4. Finite-high and first-tail banks

The independently reviewed [endpoint-domain Theorem2](endpoint-geometry-b1/endpoint-domain/PROOF.md) supplies, for `0<H≤1/2`, `m≥1/2`, `R≥max(m,sqrt(1/4+H²))`, on a Borel class with m≤M≤R and |h|≤H,

`|S_r(V)| ≥ min(K(R,H),(m−r)/(m+r)) |V|`, 0<r<m,

where `K(R,H)=sqrt(R²−H²)/(sqrt(R²−H²)+2R²)` and its stated domain conditions hold for both classes below. Full radial filling, including radii below the segment, is included.

For F, use m=99/100,R=8/5,H=1/5. Its cap exceeds7/30. The following disjoint radial rows therefore pay F at price1:

| Bank | Section coefficient |
|---|---|
| [1/2,3/5) | 7/30 |
| [3/5,7/10) | 29/169 |
| [7/10,4/5) | 19/179 |

The receipt per direction radian is `446059/13962000`. It exceeds1/(10π), since π>223/71 and

`(223/71)(446059/13962000)−1/10 =340957/991302000>0`.

For D₀, take m=8/5,R=16/5,H=1/5. Its cap exceeds1/8, while its rational branch is at least1/7 throughout[4/5,6/5]. Price1 there pays per radian

`(1/8)∫_[4/5,6/5]min(r,1)dr=19/400>1/(10π)`.

No source is charged on[6/5,8/5).

## 5. All later tails

For n≥1, use the already proved terminal receipt on the fresh half-band[m_n/2,m_n):

`|S_r(D_n)| ≥ min(1/2,m_n−r)|D_n|/(2πm_n)`.

Since m_n≥16/5, this bank lies above radius1. Its receipt per direction radian is

`(1/π)(1/8−1/(16m_n)) ≥ (1/π)(27/256) >1/(10π)`.

This monotonic formula covers every later scale. No finite sample is being extrapolated to infinity.

## 6. Sum one physical budget and recover outer area

The low bank[0,1/2), finite-high bank[1/2,4/5), first-tail bank[4/5,6/5), and later half-bands[8/5,16/5),[16/5,32/5),… are pairwise disjoint up to null boundary circles. The only overlapping low subunions have the complementary prices already accounted for in§3.

Thus total charged density is at most1_W at every physical point. Every direction class receives at least its length divided by10π. Nonnegative monotone convergence and total direction lengthπ give

`|G| ≥ ν(W) ≥ (|L|+|F|+Σ_n|D_n|)/(10π)=1/10`.

This holds for every open G⊇E, hence |E|*≥1/10. QED.

## Proof and execution boundary

- IL is the new load-bearing lemma. Its complete geometry is in the linked proof; the coefficient checker alone does not prove it.
- Both IL and the complete composition are independently accepted: see [the end-to-end review](tenth-reviews/b2_universal_tenth_end_to_end_review.md), [IL geometry](tenth-reviews/b2_IL_geometry_review.md), and [IL arithmetic](tenth-reviews/b2_IL_arithmetic_review.md). Their verdicts apply to the pinned mathematical sources, not a claim that this later exposition or the result was checked by Lean.
- The stronger candidate PL has a literal positive-measure counterexample in `low-source-b2/paired-pointwise/COUNTEREXAMPLE.md`. It is not used anywhere above.
- The frozen0.082812499999972190 baseline and historical34/441 closeout remain preserved. No0.25 work or push is part of this result.
