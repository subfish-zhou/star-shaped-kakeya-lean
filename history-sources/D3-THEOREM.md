# THEOREM — adaptive-cut small-radius full-chord paired persistence

## 1. Literal geometry

Let `T_pi=R/pi Z` carry arclength outer measure.  Let `A subset T_pi` be
arbitrary, with no measurability assumption.  For each projective direction
`theta in A`, choose one physical closed unit chord.  After choosing a canonical
lift on any proof cut, write

\[
 N_\theta=\{d_\theta n_\theta+t e_\theta:-s_\theta\le t\le1-s_\theta\},
 \qquad 0\le s_\theta\le1,
\]

and put `h_theta=|d_theta|`.  The two branches below always belong to this same
complete chord.

Fix

\[
 0\le H\le u<R,\qquad u>0.
\]

and assume for every `theta in A` that

\[
 h_\theta\le H,\qquad
 \sqrt{h_\theta^2+s_\theta^2}\ge R,\qquad
 \sqrt{h_\theta^2+(1-s_\theta)^2}\ge R.       \tag{1}
\]

Let `E_A` be the union of the origin triangles of these chords and set

\[
 Q_u=\{\phi\in\mathbb T_{2\pi}:u e_\phi\in E_A\}.
\]

The strict shell portions `u<|x|<R` contract radially into `Q_u`.  For
`h_theta>0` their two angular arcs are, up to reversing orientation,

\[
 W^+_\theta=\theta+\operatorname{sgn}(d_\theta)
 (\arcsin(h_\theta/R),\arcsin(h_\theta/u)),
\]
\[
 W^-_\theta=\theta+\pi-\operatorname{sgn}(d_\theta)
 (\arcsin(h_\theta/R),\arcsin(h_\theta/u)).   \tag{2}
\]

At `h_theta=0` these are the singleton limits `{theta}` and `{theta+pi}`;
they are not deleted as empty open intervals.

## 2. Adaptive cut lemma

> **Lemma 1 (outer-measure cut averaging).**  If `A subset T_pi` is arbitrary,
> `L=|A|*`, and `0<=beta<=pi/2`, then there is `c in T_pi` such that
> \[
> |A\setminus \overline B(c,\beta)|^*
> \ge \left(1-{2\beta\over\pi}\right)L.       \tag{3}
> \]

**Proof.** Choose a Lebesgue-measurable hull `G superset A` with `|G|=L`.
Tonelli is applied to `G`, not to `A`:

\[
 \int_{\mathbb T_\pi}|G\cap\overline B(c,\beta)|\,dc
 =2\beta |G|.
\]

Thus one `c` has intersection measure at most `(2 beta/pi)L`.  The ball is
measurable, so Carathéodory splitting gives

\[
 L=|A\cap\overline B(c,\beta)|^*
   +|A\setminus\overline B(c,\beta)|^*.
\]

Use `A subset G` for the first term.  This proves `(3)`.  The endpoint cases
`beta=0,pi/2` follow literally. `square`

## 3. Proportional paired persistence

We use the following established scale-free interval lemma, stated here to make
the dependency explicit.

> **Radial-sliver covering lemma.** Let `B subset T_pi` be arbitrary.  For each
> `theta in B`, let `I_theta` be the angular interval cut out by one branch of a
> line at radii `(u,R)`, with its ideal direction anchored at `theta`; retain the
> singleton ideal ray when the interval has zero width.  If the branch reaches
> `R`, then
> \[
> \left|\bigcup_{\theta\in B}I_\theta\right|^*
> \ge {R-u\over R+u}|B|^*.                    \tag{S}
> \]

For positive-width intervals, direct line geometry gives
`dist(theta,I_theta)<=mu |I_theta|`, where `mu=u/(R-u)`.  Enlarging each interval
toward its anchor is contained in its centred `(1+2mu)`-dilate.  The
one-dimensional component-envelope inequality, first on open components and
then by outer regularity, bounds the enlarged union by `(1+2mu)` times the
original union.  Since the enlarged union covers `B`, `(S)` follows.  A
zero-width interval has its anchor as the retained singleton and is unchanged
by dilation.  This is the sharp outer-measure lemma used and proved in
`spikes/002-endpoint-capacity/` and reused in
`spikes/006-near-diameter-overlap/THEOREM.md`; it requires neither measurable
`B` nor a measurable branch choice.

> **Theorem 2 (selector-independent full-chord paired level theorem).** Under
> `(1)`,
> \[
> \boxed{
> |Q_u|^*\ge
> 2{R-u\over R+u}
> \left(1-{2\over\pi}\arcsin{H\over u}\right)|A|^*.}
>                                                               \tag{PP}
> \]
> The right side is nonnegative for the complete closed range `H<=u<R`.
> It is positive for every `|A|*>0` when `H<u<R`.

**Proof.** Put `beta=asin(H/u)` and apply Lemma 1.  Use the resulting `c` as a
canonical projective cut and retain

\[
 A_c=A\setminus\overline B(c,\beta).
\]

Every positive branch arc in `(2)` stays strictly inside the oriented
half-circle `(c,c+pi)`, while every negative branch arc stays in the opposite
half-circle `(c+pi,c+2pi)`.  Therefore the two global unions for `A_c` are
contained in disjoint measurable half-circle cores.  Their outer measures add
exactly by Carathéodory splitting.  This is the only role of the cut; the union
of physical branches and `Q_u` do not depend on it.

Apply the sharp one-track radial-sliver covering lemma separately to the two
branch families.  It allows arbitrary side deflection and the singleton
`h=0` limit, and gives for each track

\[
 \left|\bigcup_{\theta\in A_c}W^\pm_\theta\right|^*
 \ge {R-u\over R+u}|A_c|^*.
\]

The two cores are disjoint, `(3)` bounds `|A_c|*`, and both unions lie in
`Q_u`.  Combining these facts proves `(PP)`. `square`

The improvement over the old fixed-cut theorem is structural:

\[
 2{R-u\over R+u}|A|^*-4\arcsin(H/u)
\]

is replaced by a proportional coefficient.  In particular, no activation
threshold remains as `|A|* downarrow 0`.

## 4. Literal annular theorem

> **Corollary 3 (fixed inner-annulus payment).**  Suppose `(1)` holds with one
> fixed `R`, and let `H<=a<b<=R`.  Then
> \[
> \boxed{
> \mathcal L^{2*}\bigl(E_A\cap\{a<|x|<b\}\bigr)
> \ge P(H;a,b,R)|A|^*,}                         \tag{4}
> \]
> where the exact mechanism coefficient is
> \[
> P(H;a,b,R)=
> \int_a^b 2v{R-v\over R+v}
> \left(1-{2\over\pi}\arcsin{H\over v}\right)dv.             \tag{5}
> \]

**Proof.** For each `v in (a,b)`, apply Theorem 2 to the shell `(v,R)`.
Take an arbitrary open cover of the indicated part of `E_A`.  Its polar
sections are measurable open sets containing `Q_v`; polar Tonelli gives `(4)`
after integration, and infimizing over open covers gives outer measure.  There
is no direction integral. `square`

The coefficient is strictly positive when `H<b` and the interval contains
positive length above `H`.  For exact diameters,

\[
 P(0;a,b,R)=\int_a^b2v{R-v\over R+v}\,dv.       \tag{6}
\]

## 5. Near-balanced specializations

Assume `m_theta<=H` and `M_theta<=q<1`.  The cap `M<1` forces the perpendicular
foot to lie in the chord, hence `m_theta=h_theta`.  Under the cap `M<=q`, the
smaller endpoint radius is **at least** the lower envelope

\[
 C_q(h)^2=1+q^2-2\sqrt{q^2-h^2}
\]

for the smaller endpoint radius gives

\[
 C_q(h)\ge C_q(0)=1-q.                          \tag{7}
\]

Thus Theorem 2 and Corollary 3 apply with `R=1-q` whenever
`H<=a<b<=1-q`.  The closed boundary `M=q` is included and `(7)` remains
non-strict.

For an exactly balanced chord, write on a canonical lift

\[
 N_\theta=d_\theta n_\theta+[-1/2,1/2]e_\theta,
 \qquad |d_\theta|=h_\theta,
\]

with the signed lift chosen anti-periodically so that this denotes one physical
chord on the projective quotient.  Both endpoints have radius

\[
 M_\theta=\sqrt{h_\theta^2+1/4}.
\]

Consequently every class `h=m<=H` has uniform common reach `R=1/2`; this is the
literal small-radius theorem for the balanced obstruction, including the
centered diameter `h=0,M=1/2`.

## 6. Support-separated CFS insertion

This subsection gives a literal replacement theorem, not a same-shell bonus.
Consider a finite CFS low schedule whose first two cuts and first switch satisfy

\[
 0<\alpha_1<\alpha_2<t_1<1/2.
\]

Its first class `D_0={m<=alpha_1}` receives

\[
 p_0=F_{1/2}(\alpha_1,t_1),\qquad
 F_R(a,b)=\int_a^b v{R-v\over R+v}\,dv.          \tag{8}
\]

Choose

\[
 0<H<\alpha_1<1-q,
 \qquad {1\over2}<q,\qquad
 t_1< R_c:=\min\{\sqrt{1/4+H^2},q\}.
\]

Split, without assuming measurability,

\[
 N=\{m\le H,M\le q\},\qquad C=D_0\setminus N.
\]

The near class `N` gets the paired payment

\[
 P=P(H;H,\alpha_1,1-q)>0                         \tag{9}
\]

in the inner annulus `(H,alpha_1)`, which is disjoint from the CFS support.
Every chord in `C` either has `m>H`, giving endpoint reach at least
`sqrt(1/4+H^2)`, or has `M>q`; hence it has conservative one-track reach `R_c`.

Let `J subset [alpha_1,alpha_2)` be a nonempty half-open interval.  On `J`,
**replace** the old `R=1/2` action on `D_0` by the `R=R_c` action on `C`.
All later low rows are untouched because their first-window support starts at
`alpha_2` or later.  The two first-class coefficients become

\[
 p_N=p_0-\int_JK(v,1/2)dv+P,                     \tag{10}
\]
\[
 p_C=p_0+\int_J\bigl(K(v,R_c)-K(v,1/2)\bigr)dv, \tag{11}
\]

where `K(v,R)=v(R-v)/(R+v)`.

> **Corollary 4 (exact qualitative bottleneck lift).**  If `p_0` is the unique
> weakest coefficient of the original finite schedule, there exists a nonempty
> sufficiently short `J subset [alpha_1,alpha_2)` for which every coefficient
> of the modified schedule is strictly larger than `p_0`.

Indeed, `(9)` is positive, so `(10)>p_0` for all sufficiently short `J`.
Because `R_c>1/2`, the integrand in `(11)` is strictly positive and hence
`p_C>p_0` for every nonempty `J`.  The finitely many untouched coefficients
already exceed `p_0`; taking the minimum proves the claim.

This attacks the hybrid balanced-state obstruction at its literal support:
paired persistence pays below `alpha_1`, while the complement upgrade consumes
one old radial action by replacement.  Neither `(10)` nor `(11)` double counts a
radial atom.

For the checked 64-class frozen rational surrogate, interpret the modified
`p_N,p_C` as certified lower columns and reapply the finite Lovasz--Choquet
assembly to the refined direction atoms `N,C,D_1,...`.  Then
`paired_persistence.py` verifies by exact `Fraction` arithmetic that class zero
is the unique minimum.  Floating quadrature at

```text
H=alpha_1/2, q=0.51, J=[alpha_1,alpha_1+0.0034]
```

raises the two split columns to the untouched-row floor.  This numerical row is
SCOUT evidence only.  Corollary 4 therefore gives a strict qualitative lift of
the previously certified `q*pi` witness.  It does **not** say that the true-log
frozen minimum (numerically class 49) has been optimized, nor that the original
finite-schedule action class or `C_FS` optimizer has changed.  A new explicit
headline requires outward-rounded `asin/log` bounds and a frozen rational interval.

## 7. Evidence boundary

Theorem 2, Corollary 3, the near-balanced specialization, and Corollary 4 are
paper-level arguments.  The executable artifact checks formulas, exact frozen
surrogate ordering, support separation, and adversaries.  It does not supply a
Lean proof, global optimality, or a certified improved decimal constant.
