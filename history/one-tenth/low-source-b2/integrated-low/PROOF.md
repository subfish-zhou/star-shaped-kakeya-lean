# Integrated low-source inequality by eligible anchors and a split outer bank

**Status: complete human proof of IL, submitted for independent review.**
The stronger pointwise candidate PL is neither imported nor asserted. This
file does not promote the global area bound: the separate high/low assembly
and this new proof must pass independent review first.

## 1. The theorem and the one genuinely new union receipt

Let L be any Borel family of directions in RP^1, with a Borel unit-chord
selector, common star center 0, |h|<=1/5 and far endpoint radius M<99/100.
For every Borel V subset L put

    W(V) = union_{q in V} conv(0,A_q,B_q),
    B(V) = {q in V : N(q)>=2/5},
    U(V) = V \ B(V).

Here N is the near **endpoint** radius, not the nearest segment radius.
Direction length is normalized by |RP^1|=pi, whereas physical angles live on
the ordinary circle of length 2*pi.

**Theorem.** With one absolute constant C* defined in Section 4,

    area(W(V) intersect {|x|<=1/2}) >= C* |V|
                                  > (637/20000)|V|
                                  > |V|/(10*pi)                 (1)

whenever |V|>0; the corresponding non-strict inequalities include null cuts.
Thus IL holds, and in fact it holds hereditarily for every Borel subcut.
The exact checker encloses C* in a tiny rational interval whose displayed
approximation is 0.031885183965120. No decimal is used as a proof bound.

The new geometric receipt is

    |S_r(V)| >= k_4(r) (|V|+|B(V)|),     0<r<2/5,
    k_4(r) = min(2/3,(2/5-r)/(2/5+r)).                         (2)

It counts eligible *ideal endpoint anchors*, whose physical lifts really are
disjoint. It does not add areas or arc lengths of individual triangles.
This extra near-endpoint census, followed by complementary outer-bank
prices, is what escapes the accepted common-uniform single-far ceiling.

## 2. Proof of the eligible-anchor receipt (2)

The accepted prerequisites are the interval-union lemma in
`../../baseline/PROOF.md`, Section 2, and the exact sections and far cone cap
in `../../endpoint-geometry-b1/endpoint-domain/PROOF.md`, Sections 1-3 and 5-6.
Only their stated mathematics is used, not another lane's proposed PL.

Orient each chord toward its far endpoint by a fixed Borel choice, including
ties. In local signed coordinates its endpoints are

    (x-1,h), (x,h),       1/2<=x<1,       z=|h|<=1/5.

The strict upper bound x<1 follows from M<99/100. Both longitudinal signs are
therefore opposite. For z>0 set

    b = atan(z/x) = asin(z/M),
    c = atan(z/(1-x)) = asin(z/N),
    gamma = pi-b-c.

On the actual side of the chord, the full cone is [b,pi-c]. Reflection for a
negative signed height merely describes the original physical coordinates;
no reflected copy of W is introduced.

Select the far endpoint for every q in V. Select also the near endpoint
exactly for q in B(V). Every selected endpoint has radius at least 2/5.
For each selected endpoint construct the following *actual* circular base
and its one-sided extension to that endpoint's ideal chord-direction anchor.

* If 0<r<=z, take the whole cone [b,pi-c] as the base. If both endpoints are
  selected this base appears twice as a label, but remains one physical set.
  For the far endpoint, the accepted low cone cap gives

      b/gamma <= B_L,     1/(1+2 B_L)>11/15>2/3,

  so in particular b/gamma<1/4. For a selected near endpoint N>=2/5,
  z/N<=1/2 and z/M<=1/2. Hence b,c<=pi/6 and gamma>=2*pi/3, giving

      c/gamma <= 1/4.

  Thus every selected extension has length at most gamma/4. The far cone cap
  is needed for far-only labels: one must NOT presume their near radius is
  at least 2/5.

* If z<r<2/5, let a=asin(z/r). The selected far lobe is [b,a] and the selected
  near lobe is [pi-a,pi-c]. These are genuine complete endpoint lobes: the
  chord straddles its perpendicular foot and the selected endpoint radius
  R is at least 2/5>r. Write beta=asin(z/R), equal to b or c. Extension to
  the ideal anchor costs beta and the real base has length a-beta.
  Monotonicity of asin(t)/t gives

      beta/a <= r/R,
      beta/(a-beta) <= r/(R-r) <= r/(2/5-r).

* If z=0, take the actual singleton ray anchor for each selected endpoint.
  Its radial extent is at least 2/5, so the anchor really belongs to S_r(V).
  No positive extension is required. Zero-height directions are not removed.

All bases, across labels, endpoint signs, cone cases and lobe cases, lie in
S_r(V). Apply the interval-union lemma ONCE to this whole family with

    rho = max(1/4, r/(2/5-r)),
    |union extended bases| <= (1+2*rho)|union real bases|.

The extended union contains the far ideal lift of V and the opposite near
ideal lift of B(V). These lifts are disjoint: physical equality of two such
anchors forces equality of their projective directions, while the two
anchors for one q are antipodal, not equal. A Borel choice of one lift
preserves direction length. Their union therefore has measure

    |V|+|B(V)|.

Consequently

    |V|+|B(V)| <= (1+2*rho)|S_r(V)|,

which is exactly (2). Duplicate full cones and cross-label lobe collisions
have already been merged on the right side. No separate cone or near-lobe
payment is added afterwards. This proves the new physical-union lemma.

## 3. The two outer receipts and source-once physical prices

The unit-chord relation implies M+N>=1. Thus N<2/5 on U(V) implies M>3/5.
Every q in V has M>=1/2.

For r>1/5 all labels have z<r, so the far lobe has no full-cone cap. The same
one-family extension argument, now with one far anchor per direction, gives

    |S_r(V)| >= k_5(r)|V|,      1/5<r<1/2,
    k_5(r) = (1/2-r)/(1/2+r),

    |S_r(U(V))| >= k_6(r)|U(V)|,  1/5<r<1/2,
    k_6(r) = (3/5-r)/(3/5+r).                            (3)

These also follow directly from accepted endpoint-domain Theorem 3 or
Theorem 1 with m=3/5. The direct argument above makes clear that no cone
constant is needed on these banks. Radial endpoint equalities are null and
may be assigned either way.

Use the following physical banks; all prices are fixed before V is chosen:

| Radial bank | Actual union charged | Receipt | Price |
|---|---|---|---|
| (0,1/5) | W(V) | eligible endpoints, (2) | 1 |
| [1/5,7/20) | W(V) | all far endpoints, k_5 | 1 |
| [7/20,1/2) | W(U(V)) | large far endpoints, k_6 | lambda |
| [7/20,1/2) | W(V) | all far endpoints, k_5 | 1-lambda |

The first two banks are disjoint. On the last bank, W(U(V)) is a subset of
W(V); hence at every physical point the total charged density is

    lambda*1_{W(U(V))} + (1-lambda)*1_{W(V)} <= 1_{W(V)}

provided 0<=lambda<=1. This is the only overlap on the bank ledger, and it is
explicitly paid by complementary prices. It is not legal to set both prices
to one. There are no triangle-labelled area receipts anywhere in the table.

All triangle unions and sections are analytic and hence Lebesgue measurable,
as in the accepted recovery/section argument. Polar integration is valid.
Inside this disk the physical area element is r dr dtheta, without any outer
radial weight. Let

    C4 = integral_0^{1/5} r k_4(r) dr,
    C5 = integral_{1/5}^{7/20} r k_5(r) dr,
    C6 = integral_{7/20}^{1/2} r k_6(r) dr,
    D5 = integral_{7/20}^{1/2} r k_5(r) dr.

The table and (2)-(3) give, writing b_V=|B(V)| and u_V=|U(V)|,

    area(W(V) intersect disk(1/2))
      >= C4(2 b_V+u_V) + C5(b_V+u_V)
         +lambda*C6*u_V+(1-lambda)*D5*(b_V+u_V).             (4)

This is a physical source-once inequality, not a proposed matching theorem.

## 4. Algebraic price choice, exact constants, and IL

The primitive

    F_m(r) = -r^2/2 + 2mr - 2m^2 log(1+r/m)

satisfies F_m'(r)=r(m-r)/(m+r). The switch in k_4 is r=2/25. Therefore

    C4 = 61/750 - (8/25)log(5/4),
    C5 = 87/800 - (1/2)log(17/14),
    C6 = 93/800 - (18/25)log(22/19),
    D5 = 69/800 - (1/2)log(20/17).                        (5)

Exact rational log enclosures verify 0<C4<C6. Set, once and for all,

    lambda = C4/C6.

This choice is derived by cancelling the difference between b_V and u_V
coefficients in (4); it is not a numerical optimization. In fact lambda*C6=C4,
so both coefficients in (4) become exactly

    C* = 2*C4+C5+(1-C4/C6)*D5.                            (6)

The exact arithmetic certificate proves

    C* > 637/20000 > 71/2230 > 1/(10*pi),                 (7)

where the final inequality uses the same accepted pi>223/71 as the
conditional bridge. Thus (4) proves (1), including every Borel V subset L.
In particular V=L is exactly the requested IL. If |L|=0 it is immediate.

For clarity, the all-low/full-direction rational margin from (7) alone is

    (637/20000)*(223/71)-1/10 = 51/1420000 > 0.

This is NOT a promoted global theorem: it is only a scalar check relevant to
this low-bank lemma. The actual global theorem still requires independently
accepted composition with the separately audited high-side banks.

## 5. Failed precursor and the scope of the improvement

The initial fixed pure-price certificate set lambda=1. It yields the valid
class-dependent lower bound

    (2*C4+C5)|B(V)| + (C4+C5+C6)|U(V)|.

The first coefficient is strictly below 1/(10*pi), and the second is strictly
above it. The exact first control records this failure and retires that
certificate; it is not a counterexample to IL or to the union receipt (2).

The final proof changes no endpoint threshold or radial boundary. Its one
additional ingredient is the accepted all-far receipt D5 on the SAME outer
bank, charged only at the complementary price 1-lambda. The price C4/C6 is
specified by the exact source-class cancellation. No search, grid, random
scout, LP, numerical optimization, or geometry sweep was used.

The improvement is genuinely outside the known one-common-far ceiling:
(2) uses the two disjoint ideal source lifts when the near endpoint is
eligible, while every real target arc is still counted only once. Neither
the scalar endpoint coefficient sum nor labelwise addition is used.

## 6. Verification and review boundary

`ADMISSION-LOCAL.md` preregisters both controls before their executions.
`check.py` uses Fraction arithmetic and the positive series

    log x = 2 sum_{j>=0} t^(2j+1)/(2j+1),  t=(x-1)/(x+1),

with 40 terms and tail at most

    2*t^81/(81*(1-t^2))       for x>=1.

The exact Fraction comparisons prove the signs in (7), not the printed
rounded decimals. All four log arguments are positive and exceed one.
The checker uses explicit exceptions, not assert-only verification; normal
and optimized executions are retained in CHECK-RESULT.txt.

Review should focus on: (i) disjointness and measure of eligible ideal lifts;
(ii) the near-cone cap versus the separate far-only cone cap; (iii) lobe
existence on the stated real straddling chords; (iv) the complementary prices
on one physical outer bank; (v) constants and quantifiers. No remaining
physical-union lemma is assumed by this proof. Its status is a new complete
proof awaiting independent adversarial review, not an already accepted
campaign bound.
