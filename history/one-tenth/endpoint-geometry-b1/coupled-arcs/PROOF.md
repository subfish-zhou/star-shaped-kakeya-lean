# Joint length/radius terminal collars: a universal physical-union improvement

**Verdict: PROVED, avenue A.** The proposed joint infimum is valid for arbitrary
unit-chord selectors. It strictly improves the old terminal kernel on an explicit
radial interval whenever the endpoint-radius interval is nontrivial. This is not
a two-lobe theorem, a new optimized area bound, or a proof of the 0.1 target.
The accepted floor `0.082812499999972190` and all accepted files are unchanged.

## 1. Literal statement and normalization

Let V be any set of unoriented directions in RP¹ (total length π). For each
q in V choose an arbitrary unit segment [A_q,B_q], with one common star center
0, and set

    T_q = conv(0,A_q,B_q),    W(V) = union_{q in V} T_q,
    M_q = max(|A_q|,|B_q|),   1/2 <= m <= M_q <= R < infinity.

No regularity of the original selector, symmetry, sign restriction on its
midpoint s, or bound on its height h is needed. In particular the theorem
applies in the admitted |h|<=1/5 regime. Let S_r(V) be the actual angular
section {theta: r e_theta in W(V)}, on the ordinary circle of length 2π.
For r>0 define

    t_r(M) = min(1/2,(M-r)_+),
    a_{m,R}(r) = inf_{m<=M<=R} t_r(M)/M.

Then, with outer angular and direction lengths if necessary,

    |S_r(V)|* >= k_joint(r) |V|*,
    k_joint(r) = a_{m,R}(r)/π
               = (1/π) min{1/(2R), (1-r/m)_+}.                (J)

The infimum is taken at each fixed radius; it is NOT moved through an integral.
For every Borel selector and Borel cut, these are measurable sets and the same
inequality holds with ordinary length. The arbitrary-selector outer-length
version is proved directly below, not by assuming Borel recovery preserves an
original selector's endpoint data.

## 2. Variable-ratio component lemma (the union-level step)

Consider any family of straight collars I_q of length t_q>0, whose endpoints
and all intervening points have radii at most M_q, avoiding 0. Suppose

    t_q/M_q >= a > 0,    a <= 1,

and q is the collar's unoriented direction. Let P be the union of their
connected angular images. We claim

    |P|* >= (a/π)|V|*.                                      (C)

Take an open angular superset O of P. If O is the whole circle, the assertion
|V|* <= (π/a)|O| is immediate. Otherwise each connected collar image lies in
one component C of O, of length ell. Cover the directions of collars assigned
to C by a projective set D_C as follows.

* If ell>=a, take D_C=RP¹; its length π is <=π ell/a.
* If ell<a<=1, let c be the midpoint angle of C. Both collar endpoints have
  transverse coordinate in [-M_q sin(ell/2), M_q sin(ell/2)]. Consequently

      t_q |sin(q-c)| <= 2 M_q sin(ell/2),
      |sin(q-c)| <= 2 sin(ell/2)/a = z < 1.

  The SAME containing direction set D_C={q: |sin(q-c)|<=z} works for all
  collars assigned to C, despite their varying t_q and M_q. Its projective
  length is 2 arcsin(z), hence

      |D_C| = 2 arcsin(z) <= π z <= π ell/a.

  Here arcsin(z)<=π z/2 follows from convexity and the endpoint chord bound;
  2 sin(ell/2)<=ell supplies the last inequality.

The countably many D_C cover V, so outer subadditivity gives

    |V|* <= sum_C |D_C| <= (π/a) sum_C |C| = (π/a)|O|.

Infimize over O. This proves (C) for arbitrary index sets, overlapping collars,
repeated angular intervals, and singleton images of radial collars. It neither
sums per-label angular lengths nor enlarges the physical source by reflection.
In particular no measurability of the assignment q -> C is used.

## 3. Direct radial inclusion with a variable collar

For 0<r<m, choose an actual far endpoint F_q of radius M_q (ties arbitrary).
Take the first t_q=t_r(M_q) units of the unit segment starting at F_q and
moving towards its other endpoint. This is a subsegment since t_q<=1/2.
Every point x of this collar obeys

    |x| >= |F_q|-|F_q-x| >= M_q-t_q >= r > 0,
    |x| <= M_q.

The upper bound follows from convexity of the norm on the original chord,
whose two endpoints have norm <=M_q. Radial projection of x to radius r is
in [0,x] subset T_q. Thus its connected angular image lies in S_r(V).
The variable-ratio lemma with a=inf_M t_r(M)/M>0 proves (J). This argument
includes h=0 and collar points lying exactly on the radius-r circle. When
r>=m the claimed coefficient is zero and needs no nonzero collar.

To evaluate a, put f_r(M)=min{1/(2M),(1-r/M)_+}. For r<m it is increasing
up to M=r+1/2 and decreasing afterwards, so its infimum on [m,R] is the
smaller endpoint value. Equivalently, taking the minimum of the two branch
infima gives directly

    inf_M f_r(M) = min{1/(2R),1-r/m}.

This is an infimum of a minimum of scalar functions, not an exchange of
infimum and integration. It also gives the positive-part formula for r>=m.

## 4. Exact comparison with the accepted terminal kernel

The accepted baseline/PROOF.md, equation (5), uses

    k_old(r) = min{1/2,(m-r)_+}/(πR).

Set r_* = m(1-1/(2R)). The new coefficient is 1/(2πR) for 0<r<=r_*, then
(m-r)/(πm) for r_*<=r<m, and zero for r>=m. Since

    r_* - (m-1/2) = (R-m)/(2R) >= 0,

we have k_joint>=k_old everywhere. Precisely:

* If m=R, the kernels coincide everywhere.
* If m<R, strict improvement holds exactly at positive radii satisfying
  m-1/2 < r < m. Below this interval both have the same plateau, and at or
  above m both are zero.

For a more explicit difference, write delta=m-r. On 0<r<m with
0<delta<1/2,

    π(k_joint-k_old) =
      (1/2-delta)/R,                  delta >= m/(2R),
      delta (R-m)/(mR),              delta <= m/(2R).          (D)

Both formulas agree at their shared boundary. On the remaining radii the
difference is zero. Example: m=1,R=2,r=3/4 gives πk_old=1/8 and πk_joint=1/4.
This is a strict improvement of guaranteed coefficients, not a sharpness claim
for the physical union.

## 5. Price interface and the original-selector quantifier

For a Borel selected family, W(V) and its circular sections are analytic by
the triangle parameterization, hence Lebesgue measurable. Let

    dν = min(r,1) dr dtheta.

For any fixed bounded nonnegative measurable radial price p, (J) and Tonelli give

    integral_{W(V)} p(|x|) dν >= C_joint[p] |V|,
    C_joint[p] = (1/π) integral_0^infinity
                    p(r) min(r,1) min{1/(2R),(1-r/m)_+} dr.   (P)

This is integral-of-infimum, established by the pointwise union theorem.
No infimum-of-integral bound is asserted. Its gain over the old payment is
the integral of (D), and is strict if m<R and p>0 on a positive-measure subset
of (max(0,m-1/2),m).

For a genuinely arbitrary star-shaped Kakeya set and arbitrary original
selector, apply the accepted open-cover/Borel-midpoint recovery separately in
each open G containing it. Rerun the height dichotomy AFTER recovery; in the
low-area case partition the recovered directions by their recovered M_q, and
apply (P) to those cuts. The triangle unions lie in G. This preserves the
accepted outer-area passage without claiming that a prescribed original cut
survives recovery unchanged.

The physical source in (P) is exactly W(V). To combine this estimate with
other subunions, retain pointwise sum-of-prices <=1 in the common source ν,
just as in baseline/PROOF.md §6. Replacing the old terminal coefficient by
(J) uses the SAME price and source once; it does not create a second bank.
Other estimates on the same source may be combined by maximum, not addition.

For the accepted finite-high window m=99/100,R=8/5, the new plateau extends
beyond 5/8. All accepted terminal prices therefore lie on the new plateau.
The only gain is on [49/100,5/8], where the accepted terminal price is one:

    π(C_joint[p_T]-C_old[p_T])
       = (1/R) integral_{49/100}^{5/8} r(r-49/100) dr
       = 21141/6400000 > 0.                                 (F)

`replay.py` independently checks this exact rational value. No price optimization or new
universal numerical floor is claimed; the unchanged low branch can still be
the bottleneck. The separate two-lobe avenue was not pursued.

## Verification boundary

The geometric component and measurability arguments are human proofs.
`replay.py` checks only the seven preregistered rational controls, including an
independent polynomial evaluation of (F). `REPLAY.md` records actual execution.
Parent review is required before this lemma is accepted into the main proof.
