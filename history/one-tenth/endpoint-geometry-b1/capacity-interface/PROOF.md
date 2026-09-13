# The one-tenth source-capacity interface: exact tail and finite-high obstructions

**Status: analytic interface/obstruction, not a proof of area 1/10.**
The accepted `../../baseline/PROOF.md` and `verifier.py` are unchanged.
All unconditional geometry used here is their arbitrary-selector Borel recovery,
height dichotomy, and direct radial terminal inclusion. No result from the
parallel endpoint-domain or coupled-arcs lanes is assumed.

## 1. Normalization and the terminal receipt

After recovery in an arbitrary open superset G, take the measurable union W of
anchored unit-chord triangles. If any recovered height satisfies |h|>=1/5,
its triangle already has area >=1/10. Otherwise retain |h|<1/5. Let

    w(r)=min(r,1),       dν=w(r) dr dθ,       ν(W)<=|G|.

For a Borel direction cut V with m<=M<=U, m>1/2, the accepted theorem gives

    |S_r(V)| >= min(1/2,(m-r)_+) |V| / (π U).                 (1)

This is a statement about one physical angular union, for every cut, not a
sum of triangle or endpoint receipts. It follows by taking a far-end collar
of length min(1/2,m-r), projecting its angular union, and radially filling
inside each actual triangle. In particular, the smaller endpoint radius N
is not being mistaken for the minimum radius on the chord.

Normalize a kernel by writing |S_r(V)| >= K(r)|V|/π. For a radial price p,
the **area coefficient** paid to this class is

    A[p]=∫ p(r) w(r) K(r) dr.

The class contributes A[p]|V|/π to the final area ledger. Thus every exhaustive
direction class must receive coefficient at least c=1/10 in the classwise
certificate. This convention explains why π disappears from the tail formulas.

## 2. Exact fresh dyadic-tail formula, including all radial branches

Let R>1/2, D_n={2^n R<=M<2^(n+1)R}, and reserve the fresh half-band
[2^(n-1)R,2^n R) for D_n. Define the full-price first coefficient

    A(R) = (1/(2R)) ∫[R/2,R] min(r,1) min(1/2,R-r) dr.        (2)

**Lemma 1.** Exactly,

    A(R) = R²/24                                      (1/2<R<=1),
           (-8R³+33R²-30R+9)/(96R)                   (1<=R<=3/2),
           (-R²+8R-6)/(32R)                         (3/2<=R<=2),
           1/8 - 1/(16R)                           (R>=2).  (3)

The formulas agree on shared boundaries. Consequently

    A(R)>=1/10   if and only if   R>=5/2.                    (4)

**Proof.** The integrand changes at r=1 and r=R-1/2. If R<=1, the entire
band is below 1 and above R-1/2, giving ∫r(R-r)dr=R³/12. For 1<R<3/2,
R/2<R-1/2<1<R; integrate successively r/2, r(R-r), R-r. For 3/2<R<2,
R/2<1<R-1/2<R; integrate r/2, 1/2, R-r. For R>=2 the whole band is at or
above 1; integrate 1/2 and R-r, obtaining R/4-1/8 before division by 2R.
These integrations give (3).

The derivatives in these four regimes are respectively

    R/12,
    (-16R³+33R²-9)/(96R²),
    (6-R²)/(32R²),
    1/(16R²).

All are positive: on [1,3/2], R²(33-16R)>9 (the two lower bounds cannot
both be equal); the other signs are immediate on their stated domains.
At R=2, A=3/32<1/10. Solving the last branch of (3) gives R>=5/2. ∎

For every later dyadic class the coefficient is A(2^n R). Monotonicity,
not an extrapolation from finite checks, shows that (4) pays all tail classes.
At R=5/2 the first tail is exactly saturated. Any price 0<=p_D<=1 on this
band attaining 1/10 must be 1 almost everywhere in (5/4,5/2), because its
kernel and w are strictly positive there. There is no shared-bank reserve
on that band for low or finite-high columns under this fixed architecture.

For R>5/2, a constant price

    ρ_R = (1/10)/A(R) = 8R/[5(2R-1)]

pays the first tail, and the remaining fraction is available if a valid
other kernel has support there. At R=3 this fraction is 1/25. A class-global
finite-high kernel with lower endpoint cutoff 99/100 cannot use this far
reserve at all; splitting the class would be necessary. This is an analytic
observation, not a recommendation to optimize R or old prices.

### Truncation guards

For a reserved interval [a,b], first set l=max(0,a), u=min(b,R). If l>=u,
the receipt is zero. Otherwise

    A(R;a,b)=(1/(2R))∫[l,u] w(r)min(1/2,R-r)dr.              (5)

Split only at interior points among 1 and R-1/2. The four primitives are
r²/4, r/2, Rr²/2-r³/3, Rr-r²/2 in the cap/linear and below/above-one
regions respectively. Use primitive differences separately on each piece;
do not continue a polynomial past r=R or use r in place of w above 1.
The theorem requires R>1/2 even though the algebraic expression has a
continuation below that domain. Boundaries of radial price bands are null.
For 1<=a<=R-1/2, R>=3/2, (5) with b=R simplifies to

    A(R;a,R)=1/4-a/(4R)-1/(16R).

In that regime the condition for 1/10 is a<=3R/5-1/4; it cannot be used
when a<1 without restoring the r-weighted branch.

### Important scope: 5/2 is not a universal geometric cutoff

It is the exact requirement for the *full-price fresh half-band terminal*
architecture (2). One can start the first band earlier, at a cost to the
finite bank. For the unchanged R=8/5 and 0<=a<=1,

    A(8/5;a,8/5)=(85-50a²)/640,
    A(8/5;a,8/5)>=1/10 iff a²<=21/50.                       (6)

Thus the fixed choice a=5/8 gives 419/4096>1/10. Later dyadic bands still
meet 1/10 by (3), since their first scale is 16/5>5/2. But this reserves
all r>=5/8 and removes **all** of the old positive-height finite-high
window [5/8,4/5]. It is a different budget split, not a better low lemma
repairing the unchanged old ledger. In contrast, keeping the old band
[4/5,8/5] leaves A=53/640<1/10, regardless of the low improvement.

## 3. Why moving the cutoff alone breaks finite-high payment

Fix the old lower cutoff m=99/100 and move the upper cutoff to R=5/2.
Let F={m<=M<R}; it includes both zero and nonzero heights.

### 3.1 The old common endpoint window is unavailable

The identity

    N(M,h)²=M²+1-2 sqrt(M²-h²)

has N(M,0)=|M-1|. As M approaches 5/2 from below, N approaches 3/2,
which is greater than m. Hence there is no common radial interval
sup_F N < r < inf_F M=m. This blocks the *old* common full far-component
window argument. It does not show that S_r(F) is empty below N, or rule out
new radial-filling estimates. In particular at h=0 a radial triangle fills
all radii below its far endpoint: the old N<r condition is not necessary
for this separate literal ray fact.

### 3.2 Old terminal payment fails even before low spends anything

The full-price old common terminal coefficient is

    T_old = (1/R)∫[0,m] r min(1/2,m-r)dr
          = (m²/4-m/8+1/48)/R
          = 17053/300000 < 1/10.                            (7)

Thus no allocation of that column alone can pay finite-high, even with
an infinitely good low branch. The proof is a singleton-class full-price
obstruction, not an optimized price bound.

### 3.3 Even the proposed endpoint-ratio improvement is not enough alone

**Conditional only:** suppose someone proves the all-cut union kernel

    K_joint(r)=inf_{M∈[m,R]} min(1/2,(M-r)_+)/M.              (8)

Pointwise single-chord geometry does not prove (8). The calculation here
only determines the capacity of this hypothetical universal kernel.
For fixed r, the uncapped ratio 1-r/M increases with M, while 1/(2M)
on the capped branch decreases. Its minimum on a compact interval is
at an endpoint. Since R>=m+1/2, for r<m this becomes

    K_joint(r)=min(q,(m-r)/m),     q=1/(2R),

and it is zero for r>=m. Its full coefficient, for m<1, is

    ∫[0,m] r K_joint(r)dr = m² q(q²-3q+3)/6.                (9)

At (m,R)=(99/100,5/2), (9) equals

    199287/2500000 < 1/10.                                 (10)

If the low class reserves [0,1/2], the remainder is only

    ∫[1/2,m] r K_joint(r)dr = 136787/2500000.                (11)

A uniform multiplicative repair of precisely this residual kernel would
need factor at least 250000/136787. Equations (10)–(11) are capacity
obstructions even if (8) is eventually proved; they are not counterexamples
to (8), nor to the original one-tenth conjecture.

### 3.4 One fixed two-tier split still has a source competition obstruction

As an illustrative *conditional* split, use F1={m<=M<3/2} and
F2={3/2<=M<5/2}, and assume (8) separately on each tier. On the available
bank [0,5/4] their normalized kernels are

    K1(r)=min(1/3,(m-r)_+/m),
    K2(r)=min(1/5,(3/2-r)_+/(3/2)).

The first formula follows because 3/2>=m+1/2. K1>=K2 precisely up to
r=4m/5, apart from zero ties beyond both supports outside the bank. A
source split p1+p2<=1 satisfies

    ∫ w(p1 K1+p2 K2) <= ∫[0,5/4] w max(K1,K2)
                      = 691507/3750000 < 1/5.              (12)

But paying both tiers 1/10 requires the sum to be at least 1/5. The
shortfall is 58493/3750000, **before any low payment**. This is one fixed
all-ones dual obstruction, not an LP/search, and excludes only this pair
of assumed columns. More tiers, a valid joint-union column, different
geometry, or a different reserve split are not excluded by (12).

## 4. Exact necessary and sufficient gate for NEW source kernels

This section gives a finite-dimensional theorem about radial source
allocation, not an extra geometric theorem.

Choose R=5/2, pay all dyadic tails on their disjoint half-bands, and let
B=5/4. Partition {M<R} into finitely many exhaustive Borel classes E_i.
A legitimate column j consists of a union of classes J_j and a nonnegative
kernel K_j such that, **for every recovered selector with |h|<1/5 and every
Borel cut V of that union**, one has

    |S_r(V)| >= K_j(r)|V|/π     for almost every r.           (13)

The assertion is about the union over V. It must retain the actual feasible
unit-chord endpoint data, pole directions, angular normalization, and radial
filling. A bound proved only separately for individual labels is not (13).
The scalar ledger only needs the full class-union cuts for a fixed selector;
(13) is the stronger reusable arbitrary-cut interface requested here.

Put a_ij(r)=K_j(r) if i∈J_j, and zero otherwise. Assume finitely many columns,
each wK_j integrable on [0,B]. A price family is measurable, p_j>=0,
Σ_j p_j<=1 almost everywhere. Its class coefficients are

    A_i=∫[0,B] w(r) Σ_j p_j(r)a_ij(r)dr.                    (14)

**Lemma 2 (exact source-capacity gate).** Such prices with every A_i>=1/10
exist if and only if, for every vector λ_i>=0,

    ∫[0,B] w(r) max_j {K_j(r) Σ_{i∈J_j}λ_i} dr
          >= (1/10) Σ_i λ_i.                              (15)

Include a zero column if the menu is empty at a radius. This is an exact
analytic gate; no numerical optimization is required or performed here.

**Proof.** Necessity follows by multiplying (14) by λ_i and using Σp_j<=1
pointwise. For sufficiency the image of this price simplex in the finite
coefficient space is compact and convex: the bounded L∞ price set is
weak-* compact, and the finitely many integrable kernels define weak-*
continuous functionals. Its downward closure is closed and convex. If
(1/10,...,1/10) is outside it, finite-dimensional separation supplies a
nonnegative λ, since the set is downward closed. The support function is
exactly the left side of (15), by measurably choosing the first maximizing
column among the finite menu. This contradicts (15). ∎

Given (13) and (14), summing the column receipts yields

    Σ_i A_i |E_i|/π <= ∫_W Σ_j p_j(r) dν <= ν(W).

The tail prices occupy a disjoint radial bank. Adding them and using the
exhaustive total direction length π gives area >=1/10 for G. The accepted
outer-recovery argument then yields |E|*>=1/10. **This conclusion is
conditional on actually proving kernels satisfying (13) and (15).**

For two separate new low/high kernels K_L,K_F, (15) reads explicitly

    ∫[0,B] w max(t K_L,(1-t)K_F)dr >= 1/10
                                      for every 0<=t<=1.   (16)

The endpoint tests require full-price coefficients >=1/10 individually;
t=1/2 requires ∫w max(K_L,K_F)>=1/5. Thus merely proving two full-price
bounds >=1/10 is not sufficient. Equation (12) is the latter failure for
the fixed two-tier high example.

This necessity is for the specified source-price/column architecture. It
is not a necessary condition on all conceivable proofs or geometric sets.
A direct aggregate argument may exploit correlations not present in these
columns. There is no invocation of infinite-dimensional measurable marriage
or a hidden Hall-to-transport promotion in Lemma 2.

## 5. Explicit simple sufficient reserves, and the universal lemma still missing

Here is a fixed, transparent sufficient architecture without searching
prices. Retain R=5/2 and the fresh tails. Prove two new universal kernels
as in (13), one on L={M<m}, one on F={m<=M<5/2}, with

    ∫[0,1/2] r K_L(r)dr >= 1/10,
    ∫[1/2,5/4] w(r) K_F(r)dr >= 1/10.                      (17)

Use price one for low on [0,1/2], and price one for finite-high on
[1/2,5/4]. These inequalities are sufficient, and necessary for precisely
this fixed split. A universal class-global F kernel cannot have positive
support above m: for m<r<R choose a positive-length small direction cut
with one constant midpoint and all M in [m,r), |h|<1/5. Such a cut exists
by continuity near a radial chord with far radius strictly between m and r;
S_r is empty. This is compatible even with finite-valued Borel midpoint
recovery. For r>=R the assertion is immediate from the endpoint cap.
Therefore the second integral in (17) reduces to [1/2,m].
Similarly a universal low kernel vanishes above 1/2, as shown by centered
radial unit diameters. The exact weighted-mean requirements in (17) are

    mean_[0,1/2](K_L; r dr) >= 4/5,
    mean_[1/2,m](K_F; r dr) >= 2000/7301.                   (18)

These are integral gates, not assertions that the kernels have positive
constant lower bounds up to their terminal radius. Equations (10)–(11)
show why the candidate ratio kernel does not clear the second gate.
A different reserve a gives the equally explicit conditions
∫[0,a]wK_L>=1/10 and ∫[a,B]wK_F>=1/10; no a is optimized here.

There is also a genuinely joint route. If a **single mixed all-cut lemma**
proves a kernel K_mix for every V⊂{M<5/2}, and

    ∫[0,5/4] w(r) K_mix(r)dr >= 1/10,                      (19)

it can pay both low and high with one receipt, eliminating their artificial
price competition. This is a column J={L,F} in (15), not permission to
add their independently proved kernels. Such a mixed kernel is necessarily
zero above 1/2 because this class includes centered diameters. Consequently
(19) needs the same weighted-mean threshold 4/5 on [0,1/2], uniformly over
all bounded-radius cuts including mixed low/high cuts. No such lemma is
proved in this lane. It is a precise alternative geometry target.

For the earlier-tail alternative (6), replace the bank [0,5/4] in Lemma 2
by [0,5/8]. The rest of the gate is unchanged, but the old high window is
lost. This makes explicit how tail and finite-high budgets trade places;
it is not a free tail improvement.

### What cannot be promoted

* A per-chord lower estimate is not a physical-union all-cut kernel.
* For the same cut, two valid lower kernels can be replaced by their
  pointwise maximum. They cannot be added without an extra source theorem.
* For disjoint direction classes, physical triangle unions may overlap.
  Their angular receipts cannot be added at full price on the same radius.
  Even taking the minimum of separately proved class kernels does **not**
  by itself prove a mixed-class union kernel; that requires its own theorem.
* A shared terminal column on P∪Z is issued once, and contributes the same
  coefficient to both direction classes. Reissuing it as two independently
  charged source integrals would double-spend physical area.
* Taking inf_M at each radius, then integrating, is the uniform-kernel
  capacity considered here. Moving inf_M outside the radial integral can
  give a larger number and is not justified by this interface.

**Conclusion (OLD kernels and reservations only).** A low-only improvement
cannot fix the unchanged first tail. If its old geometric kernel is retained,
the fresh-half-band cutoff must move to at least 5/2, or the first tail
must borrow earlier radii with an explicit debit. A stronger tail/full-cone
kernel is a separate valid repair not excluded by this conclusion. At cutoff 5/2 both the
old whole finite-high terminal kernel and even the proposed common ratio
kernel fail their singleton full-price gate. One fixed conditional two-tier
refinement additionally fails a shared-source gate. A complete architecture
is available *conditionally* through (13)+(15), with simple sufficient
reserve tests (17) or the mixed-cut alternative (19). The missing universal
lemma within this OLD-kernel architecture must strengthen finite-high or
genuinely mixed physical-union payment, not merely improve the low branch.
Once new finite-high and tail kernels have paid those classes, this statement
is not an obstruction to finishing through a remaining low-source lemma. No new universal one-tenth
lower bound has been established.
