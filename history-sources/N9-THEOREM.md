# THEOREM — frozen exact/outward paired-CFS lift

## 1. Frozen schedule and refined direction atoms

Take the rational `N=64` schedule in `primary_data.json`, with original low
classes `D_0,...,D_63`, cuts `alpha_0,...,alpha_64`, window radii
`R_0,...,R_63`, and switches `t_0,...,t_64`.  Put

\[
 H={931611\over10^8},\quad q={51\over100},\quad R_p=1-q={49\over100},
\]
\[
 J=[\alpha_1,\alpha_1+3/500),\qquad
 \underline R_c={250043391187\over500000000000}.
\]

The exact rational gates verify

\[
0<H<\alpha_1<R_p,
\quad q>1/2,
\quad J\subset[\alpha_1,\alpha_2),
\]
\[
{1\over2}<\underline R_c\le q,
\quad \underline R_c^2\le {1\over4}+H^2,
\quad t_1<\underline R_c.
\]

Refine only `D_0` into the arbitrary disjoint atoms

\[
 N=\{m\le H,M\le q\},\qquad C=D_0\setminus N.
\]

The complete finite direction atom list is therefore

\[
             N,C,D_1,\ldots,D_{63}.                 \tag{A}
\]

No measurability or outer-measure additivity of these direction atoms is used.

## 2. One-action radial ownership

Write

\[
 K(u,R)={u(R-u)\over R+u},\qquad
 F_R(a,b)=\int_a^b K(u,R)\,du.
\]

For radial ownership, all supports are half-open.  Thus on `[H,alpha_1)`, `N`
receives the adaptive paired payment

\[
 P=\int_H^{\alpha_1}2u{R_p-u\over R_p+u}
 \left(1-{2\over\pi}\arcsin{H\over u}\right)du.       \tag{P}
\]

On `J=[alpha_1,alpha_1+3/500)`, the old `R=1/2` action is deleted.  `C` receives exactly one
`R=R_c` action there; it is not added to the old action.  Thus the two refined
coefficients are

\[
 p_N=F_{1/2}(\alpha_1,t_1)-F_{1/2}(J)+P,
\]
\[
 p_C=F_{1/2}(\alpha_1,t_1)-F_{1/2}(J)+F_{R_c}(J).       \tag{B}
\]

All `D_j`, `1<=j<=63`, retain their complete original coefficients

\[
 p_j=F_{1/2}(\alpha_{j+1},t_1)
       +\sum_{i=1}^j F_{R_i}(t_i,t_{i+1}).              \tag{C}
\]

The supports `[H,alpha_1)`, `J`, the remainder `[sup J,t_1)`, later low
windows `[t_i,t_{i+1})`, and high bands
`[eta+k/2,eta+(k+1)/2)` are pairwise owned as specified above.  Each shared
right endpoint belongs to the next atom, so radial load is at most one
pointwise.  This half-open endpoint convention does not change the definite
integrals in `(B),(C)`.

## 3. Finite Choquet assembly

Apply the finite simple-payment/Lovasz--Choquet lemma to the arbitrary disjoint
list `(A)`.  The lemma is a pointwise layer-cake statement: each radial action
credits its complete eligible suffix of direction atoms, and a pointwise floor
`lambda` on all columns implies area at least `pi*lambda` for the low branch.
It does not replace `|N|*+|C|*` by `|D_0|*`.

The independent validator sorts all `alpha` and `t` boundaries, reconstructs
the unique action and complete eligible suffix on each half-open radial atom,
and rebuilds all 64 original rows plus `(B)` from primary data.  It then binds
the production checker artifact by recomputing the canonical rational-string
SHA, checking the complete 65-atom witness and active atoms, and requiring the
claimed enclosure to contain its independently derived enclosure.  Hence the
finite Choquet hypotheses hold for the frozen schedule.

## 4. Exact modified-schedule constant

Let `p_N,p_C,p_1,...,p_63` denote the **true** coefficients `(B),(C)` with true
`log`, `asin`, and `pi`.  For the unchanged high-tail ledger put

\[
 A_k=\eta+{k\over2},\qquad B_k=A_k+{1\over2},
\]
\[
 R_\eta(A)=\sqrt{A^2+1+2\sqrt{A^2-\eta^2}},
\qquad
 p_{\rm high}=\inf_{k\in\mathbb N}
 F_{R_\eta(A_k)}(B_k,R_\eta(A_k)).                 \tag{H}
\]

This is the true coefficient of the complete infinite high ledger.  The
polynomial contract below gives one uniform rational lower bound for every
term of `(H)`; it does not replace `(H)` by a finite sample.  Define the exact
implicit constant of this one modified schedule by

\[
 \boxed{C_{\mathrm{pair},64}=
 \min\left\{{\eta\over2},\ \pi p_{\rm high},\
 \ \pi p_N,\pi p_C,\pi p_1,\ldots,\pi p_{63}\right\}.} \tag{D}
\]

This is an exact definition, not a decimal and not a claim of global finite-
mechanism optimality.

The paper-level adaptive paired-persistence theorem from spike 011, the
one-action ownership above, and the finite Choquet lemma imply the lower-bound
theorem with constant `(D)` for the enlarged support-separated mechanism.

## 5. Outward certificate

The checker uses only rational arithmetic:

1. Machin's identity
   `pi=16 atan(1/5)-4 atan(1/239)` with alternating remainders;
2. `log y=2 sum z^(2k+1)/(2k+1)`, `z=(y-1)/(y+1)`, with an explicit positive
   tail after 14 terms;
3. 80-term rational `asin` series bounds, complementary angles near one, and
   integer-square-root enclosures;
4. 128 monotone rational rectangles for `(P)`, after proving the derivative
   sign `R_p^2-2R_p alpha_1-alpha_1^2>0`;
5. the universal high-tail polynomial contract for every real `A>=eta`.

It proves

\[
0.07054487627351847246750992457726307620733
 \le C_{\mathrm{pair},64}
\]
\[
 \le0.07054487627351847251573589552953391541289.       \tag{E}
\]

Both enclosure ends are exact rationals.  The lower endpoint `W` is printed in
full in `results/certificate.json`; no shorter cosmetic rational replaces it.
The active lower and upper low row is `D_49`.  In particular the outward
intervals for the new split columns are

```text
N: [0.02246291981285233820172826418111784131754,
    0.02246459546552845341797923114181669070378]
C: [0.02245513340817754294092873060032676636456,
    0.02245513340817754296186992012821121915681].
```

Let `q_old` be the full exact coefficient of the previous strongest exported
`q_old*pi` witness.  Its trusted provenance is
`spikes/007-cfs-rational-cert/README.md:9-10`; both checker and validator
hard-code that complete fraction and reject a different primary-data value.
The checker proves

\[
 W-q_{old}\pi_{upper}
 >8.19415539625998221856467191145889\times10^{-9}.      \tag{F}
\]

Since `pi<pi_upper`, `(F)` gives the strict theorem-level comparison

\[
                  W>q_{old}\pi.
\]

## 6. Scope

The theorem uses the paper-level geometric and finite-Choquet bridges; those
bridges are not Lean-formalized here.  The certificate proves this frozen
witness and enclosure.  It does not prove global optimality of `(D)` over all
modified schedules or identify it with a continuum limit.
