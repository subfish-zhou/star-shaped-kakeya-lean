# A joint inner/outer lower bound for star-shaped Kakeya sets

**Proof note for spike 001.**

**Evidence status.** This note is a *complete paper-level proof of a
conditional theorem, relative to explicitly quoted results of the main paper*
`paper/star_shaped_kakeya_bounds.tex`. It is **not** self-contained. Three
kinds of input are used without being reproved here, and each is flagged at
the point of use:

1. **Quoted main-paper results.** The triangle reduction (paper Lemma 3.3,
   `lem:triangle`), the outer-measure polar slicing lemma (paper Lemma 5.6,
   `lem:polar`) and the aggregate first-arc/section bound (paper
   Proposition 5.3, `prop:endpoint`, together with the same-centre dilation
   Lemma 5.4, `lem:dilation`, and the aggregation display `eq:section`) are
   quoted verbatim in §1 and §9. Their proofs live in the main paper; the
   present note neither reproduces nor re-verifies them. Paper Proposition 5.7
   (`prop:li25`, the strengthened Li Lemma 2.5) is **deliberately not used** —
   see Remark 9.4.
2. **Classical real analysis and measure theory.** Carathéodory measurability
   of Lebesgue-measurable sets, countable subadditivity, the polar-coordinate
   area formula, and elementary calculus.
3. **Four inequalities between explicit real numbers**, isolated as
   Hypothesis C (§10) and discharged by the Arb interval certificate
   `certify.py` / `certificate.json` in this directory. That certificate is
   interval arithmetic, not a machine-checked proof of anything geometric.

Everything else — §§3–8 in particular — is proved here from those inputs.

**Status note (superseded formalisation claims).** This note was written before
the route was formalised, and its statements about the *absence* of a Lean
theorem are **historical**. The conclusion of Theorem 10.1 is now a Lean
theorem: `StarKakeyaLower.universal_annular_lower_bound` in
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean/StarKakeyaLower/AnnularAssembly.lean:233`,
with the constant in normal form at `:243`, proves
`ENNReal.ofReal (131 * Real.pi / 6250) < volume.toOuterMeasure E` for every
star-shaped Kakeya set `E`, unconditionally, with axiom receipt
`[propext, Classical.choice, Quot.sound]`. That development does **not** consume
this note, `certify.py` or `certificate.json`: it reproves every domain
condition, every gate and all of the geometry from scratch in exact rational and
squared-rational arithmetic. The mathematics of §§1–13 below is left exactly as
written and is not revised by this note; only the formalisation-status
statements are superseded. See `LEAN-STATUS.md` §22 for the receipts, and
`LEAN-PLAN.md` for the milestone record (M0–M7 all complete). No claim of
optimality, of a global parameter search, or of a stronger constant than the one
displayed is made.

Paper numbering refers to the current draft of
`paper/star_shaped_kakeya_bounds.tex`; the `\label` names given in
parentheses are the stable identifiers.

---

## 1. Setting, conventions, notation

We work in the Euclidean plane $\mathbb R^2$. For $\theta\in\mathbb R$ put
$e(\theta)=(\cos\theta,\sin\theta)$.

* $\mathbb T_p:=\mathbb R/\pi\mathbb Z$ is the circle of *unoriented*
  directions, with quotient metric $\operatorname{dist}_{\mathbb T_p}$ and
  Haar measure of total mass $\pi$.
* $\mathcal L^{2*}$ denotes planar **Lebesgue outer measure**;
  $\mathcal L^{1*}$ denotes one-dimensional outer measure, used both on
  $\mathbb T_p$ (total mass $\pi$) and on circles via arclength.
* All arithmetic is performed in $[0,+\infty]$. No step converts $+\infty$
  into a real number.
* **Open/closed conventions, fixed once and used consistently.**
  * $B(x,r)=\{y:|y-x|<r\}$ is **open**; $\bar B(x,r)$ is **closed**.
  * The Carathéodory splitting radius uses the **closed** ball
    $\bar B(0,r_0)$, so "interior part" means $E\cap\bar B(0,r_0)$ and
    "exterior part" means $E\setminus\bar B(0,r_0)$.
  * "A needle *avoids* the inner ball" always means
    $N\cap B(0,\rho)=\varnothing$ with $B(0,\rho)$ **open**; i.e. every point
    of $N$ has norm $\ge\rho$. Contact with the sphere $\partial B(0,\rho)$ is
    permitted, and is exactly the extremal case of Lemma 4.3.
  * Triangles $\Delta$ are **closed**; $\operatorname{int}\Delta$ denotes the
    topological interior. Since $\partial\Delta$ and
    $\partial\bar B(0,r_0)$ are Lebesgue null, every area statement below is
    insensitive to which of the two conventions is used, and we say so where
    it is used.

**Star-shaped Kakeya set.** $E\subset\mathbb R^2$ is star-shaped about $O$ if
$[O,x]\subset E$ for all $x\in E$; it is a *star-shaped Kakeya set* if
moreover for each $\alpha\in\mathbb T_p$ it contains a closed unit segment of
direction $\alpha$. **No measurability of $E$ is assumed anywhere.**

**Chosen family.** For a star-shaped Kakeya set $E$ with star centre
translated to $0$, fix once and for all (axiom of choice; no measurability or
continuity in $\alpha$ is assumed or used) a needle
$N_\alpha\subset E$ for each $\alpha\in\mathbb T_p$, and put

$$\Delta_\alpha=\operatorname{conv}(\{0\}\cup N_\alpha),\qquad
h(\alpha)=\operatorname{dist}(0,\operatorname{aff}N_\alpha),\qquad
\operatorname{Tri}(E)=\bigcup_\alpha\Delta_\alpha\subset E .$$

$\Delta_\alpha\subset E$ by star-shapedness, and
$\mathcal L^{2*}(\Delta_\alpha)=h(\alpha)/2$ (base $1$, height $h(\alpha)$;
this is Lemma 3.3 of the paper, the *triangle reduction*).

**Direction classes.** For $R_1>1$ put

$$\mathcal A_{\mathrm{in}}=\{\alpha:\Delta_\alpha\subset\bar B(0,R_1)\},
\qquad
\mathcal A_{\mathrm{out}}=\mathbb T_p\setminus\mathcal A_{\mathrm{in}},$$

$$L_{\mathrm{in}}=\mathcal L^{1*}(\mathcal A_{\mathrm{in}}),\qquad
L_{\mathrm{out}}=\mathcal L^{1*}(\mathcal A_{\mathrm{out}}).$$

These are literal complements; forming them needs no measurability. By finite
subadditivity of outer measure,

$$\pi=\mathcal L^{1*}(\mathbb T_p)\le L_{\mathrm{in}}+L_{\mathrm{out}}.
\tag{1.1}$$

---

## 2. Parameters and standing hypotheses

**Hypothesis A (rational data).** Fix

$$h_0=\frac{13177}{100000},\qquad
r_\lambda=\frac{10227}{50000},\qquad
r_0=\frac{999}{2000},\qquad
\varepsilon_\delta=10^{-10},\qquad m=1-\varepsilon_\delta,$$

and the target $T=\dfrac{131}{6250}$.

Derived quantities, in this order:

$$\lambda=\frac{r_0-r_\lambda}{r_0-h_0},\qquad
Q=4r_\lambda^2(1+h_0^2)-h_0^2,\qquad
d=\frac{h_0\left(1-\sqrt Q\right)}{2(1+h_0^2)},$$

$$R_1=\frac{\sqrt{1+4d^2}}{1-2\sqrt{r_\lambda^2-d^2}},\qquad
\rho=R_1-1 .$$

**Hypothesis B (domain conditions).** All of

$$0<h_0\le r_\lambda\le r_0<\tfrac12,\quad r_0\ge\tfrac3{20},\quad
0\le\lambda\le1,\quad \lambda h_0+(1-\lambda)r_0=r_\lambda,$$
$$0\le Q<1,\quad 0<d<\tfrac{h_0}2,\quad r_\lambda^2-d^2\ge0,\quad
1-2\sqrt{r_\lambda^2-d^2}>0,$$
$$\rho>r_0,\qquad h_0<m\rho,\qquad 0<\tfrac{h_0}{\rho}<1,\qquad
0<\tfrac{h_0}{m\rho}<1 .$$

Hypothesis B is *verified*, not assumed: it is discharged by exact rational
arithmetic and outward Arb intervals in `certify.py` (gates
`domain_*`).

Two further objects are needed. First the *dilation loss* of the confined
branch,

$$g(r)=\max\left\{\frac{1+2r}{1-2r},\ \frac{1+2r_\lambda}{1-2r_\lambda},\
\frac{\pi}{\pi/2-\arctan(2r)}\right\}\qquad (h_0\le r\le r_0),
\tag{2.1}$$

which satisfies $g(r)>1$ on the range because $r_0<\tfrac12$; and the *raw
radial gain*

$$I=\int_{h_0}^{r_0}\frac{r}{g(r)}\,dr .
\tag{2.2}$$

**Remark 2.1.** For the present tuple the frozen entry
$(1+2r_\lambda)/(1-2r_\lambda)=35227/14773=2.38455\ldots$ is dominated on all
of $[h_0,r_0]$ by the increasing large-angle entry, whose value at $r=h_0$ is
$2.392472\ldots$; the maximum in (2.1) therefore switches exactly once, at
$r=0.2352988169\ldots$, between the large-angle and the interior entries. This
affects no proof — $g$ is always the full maximum — but it means $I$ does not
depend on $r_\lambda$ for this tuple; $r_\lambda$ enters only through
$Q,d,R_1,\rho$.

Second, the *escaping weight* and the *exterior payment coefficient*

$$H(\delta)=\arcsin\frac{\delta}{m\rho}\quad(0\le\delta\le h_0),
\qquad
C_{\mathrm{ext}}=\frac{h_0}{2H(h_0)}-\frac{m\,r_0^2}{2},
\tag{2.3}$$

$$C_{\mathrm{fan}}=\frac{\rho^2-r_0^2}{2},
\qquad
C_{\mathrm{out}}=\min\left\{\frac{C_{\mathrm{ext}}}{4},\ C_{\mathrm{fan}}\right\}.
\tag{2.4}$$

$H$ is well defined and $H(\delta)\in[0,\pi/2)$ because $h_0<m\rho$;
$H$ is strictly increasing, and $H(\delta)=0$ iff $\delta=0$.

---

## 3. Elementary escaping geometry

**Lemma 3.1 (escaping needles avoid the inner ball).**
*If $\alpha\in\mathcal A_{\mathrm{out}}$ then
$N_\alpha\cap B(0,\rho)=\varnothing$, where $\rho=R_1-1$.*

*Proof.* Suppose $x\in N_\alpha$ with $|x|<\rho$. The needle has length $1$,
so every $y\in N_\alpha$ satisfies $|y|\le|x|+1<\rho+1=R_1$; hence
$N_\alpha\subset \bar B(0,R_1)$. As $\bar B(0,R_1)$ is convex and contains
$0$, it contains $\operatorname{conv}(\{0\}\cup N_\alpha)=\Delta_\alpha$,
i.e. $\alpha\in\mathcal A_{\mathrm{in}}$ — a contradiction. $\square$

This is the only place where the radius class is converted into geometry; the
escaping branch needs no separately postulated "outside-ball" hypothesis.

---

## 4. The annular triangle lemmas

Throughout this section $\rho>0$ is fixed, $N$ is a **closed unit segment**
with

$$\delta:=\operatorname{dist}(0,\operatorname{aff}N)\in[0,\rho),
\qquad N\cap B(0,\rho)=\varnothing ,$$

and $\Delta=\operatorname{conv}(\{0\}\cup N)$ is its origin triangle. Put

$$L:=\sqrt{\rho^2-\delta^2}\ \in(0,\rho] .$$

Choose Euclidean coordinates, by a rotation about $0$ (and, if $\delta>0$, a
reflection in the $y$-axis), so that
$\operatorname{aff}N=\{(x,y):y=\delta\}$. Write

$$N=[s,s+1]\times\{\delta\}\qquad\text{for a unique }s\in\mathbb R .$$

Rotations and reflections about $0$ preserve $\mathcal L^{2*}$, the balls
$B(0,t)$, and all quantities appearing below, so this normalisation is
harmless.

### Lemma 4.1 (one-sided position)

*Either $s\ge L$ or $s+1\le-L$.*

*Proof.* A point $(x,\delta)$ of the plane has $|(x,\delta)|<\rho$ iff
$x^2<\rho^2-\delta^2$, i.e. iff $x\in(-L,L)$. The hypothesis
$N\cap B(0,\rho)=\varnothing$ therefore says exactly

$$[s,s+1]\cap(-L,L)=\varnothing .$$

Both sets are intervals and $(-L,L)\neq\varnothing$ (here $\delta<\rho$ is
used, giving $L>0$). If $s<L$ and $s+1>-L$, then
$\max(s,-L)<\min(s+1,L)$: indeed $s<L$, $s<s+1$, $-L<L$ and $-L<s+1$, so the
four required strict inequalities hold, and the open interval
$(\max(s,-L),\min(s+1,L))$ is a nonempty subset of both $[s,s+1]$ and
$(-L,L)$ — contradiction. $\square$

Lemma 4.1 is the *connectedness* step: a unit segment cannot straddle the
forbidden disc, no matter how small $2L$ is compared with the needle length.
It is what allows a genuinely one-sided (rather than symmetric) shadow bound.
After the optional reflection we may and do assume

$$s\ge L>0 .
\tag{4.1}$$

### Lemma 4.2 (the direction set of $\Delta$)

*Assume (4.1) and $\delta>0$. Then*

$$\bigl\{\text{polar angle of }z\ :\ z\in\Delta\setminus\{0\}\bigr\}
=\Bigl[\arctan\tfrac{\delta}{s+1},\ \arctan\tfrac{\delta}{s}\Bigr]
=:\Theta(\Delta),$$

*an interval of length*
$A(s):=\arctan\dfrac{\delta}{s}-\arctan\dfrac{\delta}{s+1}>0 .$

*Proof.* Every $z\in\Delta\setminus\{0\}$ is $z=t\,w$ with $t\in(0,1]$ and
$w\in N$, and $z$ has the polar angle of $w$. Conversely each $w\in N$ lies
in $\Delta$. So the angle set of $\Delta\setminus\{0\}$ equals the angle set
of $N$. For $w=(x,\delta)$ with $x\ge L>0$ the polar angle is
$\arctan(\delta/x)\in(0,\pi/2)$, and $x\mapsto\arctan(\delta/x)$ is
continuous and strictly decreasing on $[s,s+1]\subset(0,\infty)$. $\square$

If $\delta=0$ then $\Delta\subset\{(x,0):x\ge0\}$ is a segment and
$\Theta(\Delta)$ is the single angle $0$; we set $A(s)=0$ in that case.

### Lemma 4.3 (exact maximal one-sided angular width)

*Assume (4.1). If $\delta>0$ then $s\mapsto A(s)$ is strictly decreasing on
$[L,\infty)$, hence*

$$A(s)\ \le\ A(L)\ =\ W_\rho(\delta)
:=\arcsin\frac{\delta}{\rho}
-\arctan\frac{\delta}{1+\sqrt{\rho^2-\delta^2}},
\tag{4.2}$$

*with equality **iff** $s=L$, i.e. iff the needle touches the sphere
$\partial B(0,\rho)$. Moreover $0<W_\rho(\delta)<\arcsin(\delta/\rho)$ for
$0<\delta<\rho$. If $\delta=0$ then $A(s)=0=W_\rho(0)$ for every $s\ge L=\rho$,
so (4.2) holds with equality for every legal position and the uniqueness
clause does not apply.*

*Proof.* For $\delta>0$ and $s>0$,

$$A'(s)=-\frac{\delta}{s^2+\delta^2}+\frac{\delta}{(s+1)^2+\delta^2}<0,$$

because $(s+1)^2+\delta^2>s^2+\delta^2>0$. Hence $A$ is strictly decreasing
and attains its supremum on $[L,\infty)$ exactly at $s=L$.
For the closed form, $\arctan(\delta/L)=\arcsin(\delta/\rho)$: both are in
$(0,\pi/2)$ and
$\tan\arcsin(\delta/\rho)=\dfrac{\delta/\rho}{\sqrt{1-\delta^2/\rho^2}}
=\dfrac{\delta}{\sqrt{\rho^2-\delta^2}}=\dfrac{\delta}{L}.$
Substituting $s=L=\sqrt{\rho^2-\delta^2}$ in $A$ gives (4.2).

Finally $\arctan\bigl(\delta/(1+L)\bigr)>0$ for $\delta>0$, so
$W_\rho(\delta)<\arcsin(\delta/\rho)$; and $A(L)>0$ since $A$ is a difference
of two arctangents at distinct positive arguments. For $\delta=0$ every term
vanishes. $\square$

**Remark 4.4.** The naive symmetric bound "the shadow has half-width
$\arcsin(\delta/\rho)$, hence width $2\arcsin(\delta/\rho)$" is valid but
loses a factor of slightly more than $2$. Lemma 4.3 is what makes the
exterior payment large enough to clear the target. The *simpler corollary*
$A(s)\le\arcsin(\delta/\rho)$, obtained by dropping the arctangent term, is
the only consequence actually used in §5; $W_\rho$ itself is recorded because
it is sharp and because the falsification test
`test_annular_geometry.py` checks it.

### Proposition 4.5 (exterior area of one escaping triangle)

*Let $0<r_0<\rho$, and let $N,\Delta,\delta$ be as above. Then*

$$\mathcal L^{2*}\bigl(\Delta\setminus\bar B(0,r_0)\bigr)
\ \ge\ \frac{\delta}{2}-\frac{r_0^2}{2}\,W_\rho(\delta)
\ \ge\ \frac{\delta}{2}-\frac{r_0^2}{2}\arcsin\frac{\delta}{\rho}.
\tag{4.3}$$

*The same bound holds with $\bar B(0,r_0)$ replaced by $B(0,r_0)$ and with
$\Delta$ replaced by $\operatorname{int}\Delta$.*

*Proof.* $\Delta$ is compact and convex, hence measurable, with
$\mathcal L^{2}(\Delta)=\delta/2$. By Lemma 4.2 every point of
$\Delta\setminus\{0\}$ has polar angle in the interval $\Theta(\Delta)$ of
length $A(s)$, so

$$\Delta\cap\bar B(0,r_0)\ \subset\
\{0\}\cup\{t\,e(\theta):0<t\le r_0,\ \theta\in\Theta(\Delta)\},$$

a circular sector of radius $r_0$ and aperture $A(s)$, of area
$r_0^2A(s)/2$. Hence, by additivity of Lebesgue measure on the measurable set
$\Delta$,

$$\mathcal L^{2}\bigl(\Delta\setminus\bar B(0,r_0)\bigr)
=\frac{\delta}{2}-\mathcal L^{2}\bigl(\Delta\cap\bar B(0,r_0)\bigr)
\ \ge\ \frac{\delta}{2}-\frac{r_0^2}{2}A(s),$$

and Lemma 4.3 gives $A(s)\le W_\rho(\delta)\le\arcsin(\delta/\rho)$. The
variants follow because $\partial\Delta$ and $\partial\bar B(0,r_0)$ are
null, so replacing either set by its interior changes no area. $\square$

The right-hand side of (4.3) may be negative; the proposition is then vacuous
but still true. Positivity is exactly what §5 arranges.

**Remark 4.6 (sharpness).** Let $\delta>0$. The first inequality in (4.3) is
an *equality* whenever the needle touches $\partial B(0,\rho)$. Indeed, for
every $\theta\in\Theta(\Delta)$ the ray $\{te(\theta):t\ge0\}$ meets $N$ at
distance $\delta/\sin\theta\ge\rho>r_0$ (note $\sin\theta>0$ on
$\Theta(\Delta)$ because $\Theta(\Delta)\subset(0,\pi/2)$), so $\Delta$
contains the whole sector
$\{te(\theta):0\le t\le r_0,\ \theta\in\Theta(\Delta)\}$; combined with the
inclusion used in the proof this gives
$\mathcal L^{2}(\Delta\cap\bar B(0,r_0))=\tfrac{r_0^2}{2}A(s)$ exactly, for
every legal position. Hence no better constant than $W_\rho$ is available in
(4.3). For $\delta=0$ both sides of (4.3) are $0$ and the identity is trivial.
The falsification test checks the identity numerically
(`worst_sector_identity_error`).

---

## 5. The exterior payment coefficient

Two elementary calculus facts do all the work. Recall $m=1-\varepsilon_\delta
\in(0,1)$ and $H(\delta)=\arcsin\bigl(\delta/(m\rho)\bigr)$.

### Lemma 5.1 (chord form of the concavity of $\sin$)

*Let $0<u\le u_0<\pi/2$. Then $\dfrac{\sin u}{u}\ge\dfrac{\sin u_0}{u_0}$.*

*Proof.* $\varphi(u)=\sin u/u$ has
$\varphi'(u)=\bigl(u\cos u-\sin u\bigr)/u^2$ and
$u\cos u-\sin u<0$ on $(0,\pi/2]$ because $\tan u>u$ there. So $\varphi$ is
strictly decreasing. $\square$

### Lemma 5.2 (arcsine contraction)

*Let $0<m\le1$ and $0\le u\le\pi/2$. Then
$\arcsin(m\sin u)\le m\,u$.*

*Proof.* Both sides vanish at $u=0$. For $u\in(0,\pi/2)$,

$$\frac{d}{du}\arcsin(m\sin u)=\frac{m\cos u}{\sqrt{1-m^2\sin^2u}}\le m,$$

because $\cos^2u=1-\sin^2u\le1-m^2\sin^2u$ and both sides of the last
inequality are nonnegative, so $\cos u\le\sqrt{1-m^2\sin^2u}$; the
denominator is positive since $m\sin u\le\sin u<1$ on $(0,\pi/2)$. Integrate
from $0$ to $u$; the case $u=\pi/2$ follows by continuity. $\square$

### Proposition 5.3 (exterior payment)

*Assume Hypothesis B, let $0\le\delta\le h_0$, and let $N$ be a unit needle
with height $\delta$ and $N\cap B(0,\rho)=\varnothing$, with origin triangle
$\Delta$. Then*

$$\mathcal L^{2*}\bigl(\Delta\setminus\bar B(0,r_0)\bigr)
\ \ge\ C_{\mathrm{ext}}\;H(\delta),
\qquad
C_{\mathrm{ext}}=\frac{h_0}{2H(h_0)}-\frac{m\,r_0^2}{2}.
\tag{5.1}$$

*Proof.* If $\delta=0$ both sides are $0$ (Proposition 4.5 gives $\ge0$, and
$H(0)=0$), so assume $\delta>0$. Write $u=H(\delta)$ and $u_0=H(h_0)$, so
that $0<u\le u_0<\pi/2$ and

$$\delta=m\rho\sin u,\qquad h_0=m\rho\sin u_0 .$$

*Step 1 (the area term).* By Lemma 5.1,
$\sin u/u\ge\sin u_0/u_0$, hence

$$\frac{\delta}{2}=\frac{m\rho\sin u}{2}
\ \ge\ \frac{m\rho\sin u_0}{2u_0}\,u
=\frac{h_0}{2H(h_0)}\,H(\delta).
\tag{5.2}$$

*Step 2 (the sector term).* Since
$\delta/\rho=m\cdot\delta/(m\rho)=m\sin u$ and $u\in(0,\pi/2)$, Lemma 5.2
gives

$$\arcsin\frac{\delta}{\rho}=\arcsin(m\sin u)\ \le\ m\,u=m\,H(\delta).
\tag{5.3}$$

(The argument $\delta/\rho$ lies in $(0,1)$ because $\delta\le h_0<m\rho<\rho$.)

*Step 3.* Combine Proposition 4.5 with (5.2) and (5.3):

$$\mathcal L^{2*}\bigl(\Delta\setminus\bar B(0,r_0)\bigr)
\ \ge\ \frac{\delta}{2}-\frac{r_0^2}{2}\arcsin\frac{\delta}{\rho}
\ \ge\ \frac{h_0}{2H(h_0)}H(\delta)-\frac{m\,r_0^2}{2}H(\delta),$$

which is (5.1). $\square$

**Remark 5.4.** Both steps are applications of concavity: Step 1 is the chord
inequality for the concave function $\sin$ on $[0,u_0]$, Step 2 is the
statement that $u\mapsto\arcsin(m\sin u)$ has derivative at most $m$. No
$\kappa=2\arcsin(m)/\pi$ factor appears: the fixed tolerance $m$ is absorbed
once and for all into $H$ and into $C_{\mathrm{ext}}$. The certificate
verifies $C_{\mathrm{ext}}>0$ (gate `C_ext_positive`); without that,
(5.1) is true but useless.

---

## 6. Shadows, cones and disjointness

### Lemma 6.1 (shadow cone)

*Let $N$ be a unit needle with $N\cap B(0,\rho)=\varnothing$ and height
$\delta\in[0,\rho)$, projective direction $\theta\in\mathbb T_p$, origin
triangle $\Delta$. Then every $z\in\operatorname{int}\Delta$ satisfies*

$$\operatorname{dist}_{\mathbb T_p}\bigl(\operatorname{dir}(z),\theta\bigr)
\ <\ \arcsin\frac{\delta}{\rho},$$

*where $\operatorname{dir}(z)\in\mathbb T_p$ is the unoriented direction of
$z\ne0$. In particular $\operatorname{int}\Delta\subset S(\theta,\delta)$,
where*

$$S(\theta,\delta):=\Bigl\{z\ne0:\
\operatorname{dist}_{\mathbb T_p}(\operatorname{dir}(z),\theta)
<\arcsin\tfrac{\delta}{\rho}\Bigr\}$$

*is an open cone (empty when $\delta=0$).*

*Proof.* If $\delta=0$ then $\Delta$ is a segment and
$\operatorname{int}\Delta=\varnothing$. Let $\delta>0$ and
$z\in\operatorname{int}\Delta$. The ray $[0,z)$ extended meets the relative
interior of $N$ at a point $y$ (in the coordinates of §4 with $z=t(x,\delta)$,
$t\in(0,1)$, $x\in(s,s+1)$; take $y=(x,\delta)$). By Lemma 4.1 and (4.1),
$|y|^2=x^2+\delta^2>L^2+\delta^2=\rho^2$, so $|y|>\rho$ strictly. Let $\phi$
be the angle between the ray $[0,y)$ and the line of $N$; then
$\sin\phi=\delta/|y|<\delta/\rho$, and $\phi\in[0,\pi/2)$, so
$\phi<\arcsin(\delta/\rho)$. Since $\operatorname{dir}(z)=\operatorname{dir}(y)$
and the projective distance to $\theta$ equals $\phi$, the claim follows.
$\square$

### Lemma 6.2 (separation implies disjointness)

*Let $N_1,N_2$ be unit needles avoiding $B(0,\rho)$, with heights
$\delta_1,\delta_2\in[0,\rho)$ and directions $\theta_1,\theta_2$. If*

$$\operatorname{dist}_{\mathbb T_p}(\theta_1,\theta_2)
\ \ge\ \arcsin\frac{\delta_1}{\rho}+\arcsin\frac{\delta_2}{\rho},$$

*then the open cones $S(\theta_1,\delta_1)$ and $S(\theta_2,\delta_2)$ are
disjoint; consequently $\operatorname{int}\Delta_1$ and
$\operatorname{int}\Delta_2$ are disjoint.*

*Proof.* If $z$ lay in both cones then, by the triangle inequality in
$\mathbb T_p$,
$\operatorname{dist}(\theta_1,\theta_2)
<\arcsin(\delta_1/\rho)+\arcsin(\delta_2/\rho)$, contradicting the
hypothesis. Apply Lemma 6.1. $\square$

Note that the cones are **open and hence Lebesgue measurable**, which is what
§7 needs; the triangles themselves need not be separated by a positive
distance.

---

## 7. Outer-measure additivity across a disjoint measurable family

The only measure-theoretic tool used, besides monotonicity and countable
subadditivity, is Carathéodory splitting.

### Lemma 7.1 (Carathéodory)

*If $M\subset\mathbb R^2$ is Lebesgue measurable and $A\subset\mathbb R^2$ is
arbitrary, then
$\mathcal L^{2*}(A)=\mathcal L^{2*}(A\cap M)+\mathcal L^{2*}(A\setminus M)$.*

This is the definition of measurability in Carathéodory's sense, which for
Lebesgue outer measure coincides with Lebesgue measurability. It requires no
measurability of $A$.

### Lemma 7.2 (separated countable superadditivity)

*Let $A\subset\mathbb R^2$ be arbitrary and let $(M_j)_{j\in J}$, $J$
countable, be pairwise disjoint measurable sets. Then*

$$\sum_{j\in J}\mathcal L^{2*}(A\cap M_j)\ \le\ \mathcal L^{2*}(A).$$

*Proof.* For a finite subfamily $M_1,\dots,M_n$ apply Lemma 7.1 repeatedly:
$\mathcal L^{2*}(A)=\mathcal L^{2*}(A\cap M_1)+\mathcal L^{2*}(A\setminus M_1)$,
then split $A\setminus M_1$ by $M_2$ (using
$(A\setminus M_1)\cap M_2=A\cap M_2$ by disjointness), and so on; the
remainder term is nonnegative. Take the supremum over finite subfamilies.
$\square$

### Corollary 7.3 (the exterior ledger)

*Let $(M_j)_{j\in J}$ be pairwise disjoint measurable sets, $J$ countable, and
let $M_\ast$ be measurable with $M_\ast\cap M_j=\varnothing$ for all $j$. Let
$A$ be arbitrary and suppose $P_j\subset A\cap M_j$ and
$P_\ast\subset A\cap M_\ast$. Then*

$$\sum_{j\in J}\mathcal L^{2*}(P_j)+\mathcal L^{2*}(P_\ast)
\ \le\ \mathcal L^{2*}(A).$$

*Proof.* Lemma 7.2 applied to the family $(M_j)_j$ together with $M_\ast$,
followed by monotonicity. $\square$

In the application $M_j=S(\theta_j,\delta_j)$ are the shadow cones of the
selected triangles, and
$M_\ast=\mathbb R^2\setminus\bigcup_j S(\theta_j,\delta_j)$ is measurable
(complement of an open set) and disjoint from every $M_j$ by construction.
No measurability of the residual direction set is needed at any point.

---

## 8. The exterior greedy budget

Assume Hypotheses A and B and the **height cap**

$$h(\alpha)<h_0\qquad\text{for every }\alpha\in\mathbb T_p .
\tag{8.1}$$

Let $A\subset\mathcal A_{\mathrm{out}}$ be *any* subset of the escaping class
(we will take $A=\mathcal A_{\mathrm{out}}$); by Lemma 3.1 every
$\alpha\in A$ has $N_\alpha\cap B(0,\rho)=\varnothing$.

### 8.1 The selection

Set $S_0=A$. Given $S_j$, let $\sigma_j=\sup\{h(\alpha):\alpha\in S_j\}$
(with $\sup\varnothing=0$).

* **Stop** if $\sigma_j=0$ (in particular if $S_j=\varnothing$). Put
  $\mathcal R=S_j$; every residual direction then has height $0$.
* Otherwise choose $\theta_j\in S_j$ with $h(\theta_j)>m\,\sigma_j$ — possible
  since $m<1$ and $\sigma_j>0$ — and set

  $$\delta_j=h(\theta_j)\in(0,h_0),\qquad H_j=H(\delta_j)\in(0,\pi/2),$$
  $$S_{j+1}=S_j\setminus B_{\mathbb T_p}(\theta_j,2H_j).$$

If the process never stops, put $\mathcal R=\bigcap_j S_j$. The choices use
the axiom of choice only; no measurability of any $S_j$ is used or claimed.
Write $R=\mathcal L^{1*}(\mathcal R)$ and $B=\sum_j 4H_j\in[0,\infty]$.

### 8.2 The three budget inequalities

**(B1) Cover.** $\mathcal L^{1*}(A)\le R+B$.

*Proof.* Every $\alpha\in A$ either lies in $\mathcal R$ or is removed at some
stage $j$, i.e. lies in $B_{\mathbb T_p}(\theta_j,2H_j)$. Thus
$A\subset\mathcal R\cup\bigcup_jB_{\mathbb T_p}(\theta_j,2H_j)$ and countable
subadditivity gives
$\mathcal L^{1*}(A)\le R+\sum_j\mathcal L^{1}\bigl(B_{\mathbb T_p}(\theta_j,2H_j)\bigr)
\le R+\sum_j4H_j$, since a projective ball of radius $t$ has measure at most
$\min(\pi,2t)\le 4t$. $\square$

**(B2) Angular separation.** *For $j<n$ (both stages performed),*

$$\arcsin\frac{\delta_j}{\rho}+\arcsin\frac{\delta_n}{\rho}
\ <\ 2H_j\ \le\ \operatorname{dist}_{\mathbb T_p}(\theta_j,\theta_n).$$

*Proof.* $\theta_n\in S_n\subset S_{j+1}$, so
$\theta_n\notin B_{\mathbb T_p}(\theta_j,2H_j)$, giving the right-hand
inequality. For the left: $\sin H_j=\delta_j/(m\rho)>\delta_j/\rho$ because
$m<1$ and $\delta_j>0$, so $\arcsin(\delta_j/\rho)<H_j$. Also
$\delta_n\le\sigma_n\le\sigma_{j}<\delta_j/m$ (approximate maximality at stage
$j$ and $S_n\subset S_j$), hence $\delta_n/\rho<\delta_j/(m\rho)=\sin H_j$ and
$\arcsin(\delta_n/\rho)<H_j$. $\square$

Consequently, by Lemma 6.2, the shadow cones $S(\theta_j,\delta_j)$ are
pairwise disjoint, and so are the open triangles
$\operatorname{int}\Delta_{\theta_j}$. Note only the two displayed strict
inequalities are used; the monotonicity $H_n<H_j$ is **false** in general and
is never invoked.

**(B3) Residual separation.** *If $\theta\in\mathcal R$ then, for every stage
$j$, $\operatorname{dist}_{\mathbb T_p}(\theta_j,\theta)\ge2H_j>\arcsin(\delta_j/\rho)$;
hence $\mathcal R$'s fan misses every $S(\theta_j,\delta_j)$.*

*Proof.* $\theta\in\mathcal R\subset S_{j+1}$, so $\theta$ was not deleted at
stage $j$. $\square$

### 8.3 Residual heights vanish

**(B4).** *Every $\theta\in\mathcal R$ has $h(\theta)=0$, except possibly in
the case $B=\infty$, which is handled separately in §8.6.*

*Proof.* If the process stops at stage $j$ then $\sigma_j=0$ and all residual
heights vanish. If it runs forever and $B=\sum_j4H_j<\infty$, then $H_j\to0$,
hence $\delta_j=m\rho\sin H_j\to0$, hence
$\sigma_j<\delta_j/m\to0$; for $\theta\in\mathcal R\subset S_j$ we get
$h(\theta)\le\sigma_j$ for all $j$, so $h(\theta)=0$. $\square$

### 8.4 The residual annular fan

**Throughout §8.4 assume (B4)**, i.e. every $\theta\in\mathcal R$ has
$h(\theta)=0$; by §8.3 this holds whenever $B<\infty$. For such $\theta$ the
needle $N_\theta$ lies on a
line through $0$ and avoids $B(0,\rho)$; being connected and not containing
$0$, it lies on one closed ray from the origin. Choose for each
$\theta\in\mathcal R$ an oriented angle $\omega(\theta)\in[-\pi,\pi)$ with

$$N_\theta=\{t\,e(\omega(\theta)):t\in[t_\theta,t_\theta+1]\},
\qquad t_\theta\ge\rho ,$$

so that $e(\omega(\theta))$ is a unit vector of direction $\theta$. The lift
$\omega$ is a pointwise choice (axiom of choice); no measurability or
continuity of $\omega$ is assumed. By star-shapedness

$$F:=\bigcup_{\theta\in\mathcal R}\{t\,e(\omega(\theta)):0\le t\le\rho\}
\ \subset\ \operatorname{Tri}(E)\subset E .$$

Before measuring $F$ we record the adapter that carries a projective direction
set into the **real-angle** statement of Lemma 9.1. Write
$\pi_q:\mathbb R/2\pi\mathbb Z\to\mathbb T_p$ for the canonical quotient of
oriented angles onto unoriented directions, and write $\pi_q(\omega)$ also for
$\pi_q$ applied to the class of a real number $\omega$.

**Lemma 8.3 (2π cut adapter).**
*Let $\mathcal S\subset\mathbb T_p$ be arbitrary and let
$\omega:\mathcal S\to[-\pi,\pi)$ satisfy $\pi_q(\omega(\theta))=\theta$ for
every $\theta\in\mathcal S$. Put $\Omega=\omega(\mathcal S)\subset[-\pi,\pi)$.
Then*

$$\mathcal L^{1*}\bigl(\Omega\cap(-\pi,\pi)\bigr)
\ =\ \mathcal L^{1*}(\Omega)
\ \ge\ \mathcal L^{1*}(\mathcal S).$$

*Proof.* **Choice of cut.** Take the cut point $-\pi$. Since
$\Omega\subset[-\pi,\pi)$ we have $\Omega\cap(-\pi,\pi)=\Omega\setminus\{-\pi\}$.
Removing one point does not change one-dimensional outer measure:
monotonicity gives
$\mathcal L^{1*}(\Omega\setminus\{-\pi\})\le\mathcal L^{1*}(\Omega)$, while
finite subadditivity together with $\mathcal L^{1*}(\{-\pi\})=0$ gives

$$\mathcal L^{1*}(\Omega)
\ \le\ \mathcal L^{1*}(\Omega\setminus\{-\pi\})+\mathcal L^{1*}(\{-\pi\})
\ =\ \mathcal L^{1*}(\Omega\setminus\{-\pi\}).$$

Any other cut point would serve equally well; the choice is immaterial
precisely because a single point is null.

**Quotient step.** $\pi_q$ is $1$-Lipschitz, because
$\mathbb T_p=\mathbb R/\pi\mathbb Z$ is a further quotient of
$\mathbb R/2\pi\mathbb Z$ and passing to a quotient metric can only shrink
distances; and $1$-Lipschitz maps do not increase one-dimensional outer
measure. Since $\pi_q(\omega(\theta))=\theta$ for every $\theta\in\mathcal S$,
the image of $\Omega$ under the composite
$\mathbb R\to\mathbb R/2\pi\mathbb Z\to\mathbb T_p$ is exactly $\mathcal S$,
whence
$\mathcal L^{1*}(\Omega)\ge\mathcal L^{1*}(\mathcal S)$. No lift is claimed to
be an isometry, and $\omega$ need not be injective; only surjectivity onto
$\mathcal S$ after projection is used. $\square$

**(B5) Annular fan area.**
$\mathcal L^{2*}\bigl(F\setminus\bar B(0,r_0)\bigr)\ \ge\ C_{\mathrm{fan}}\,R$
*with* $C_{\mathrm{fan}}=(\rho^2-r_0^2)/2$.

*Proof.* Put $F'=F\setminus\bar B(0,r_0)$ and
$\Omega=\omega(\mathcal R)\subset[-\pi,\pi)$. For each $r\in(r_0,\rho]$ and
each $\theta\in\mathcal R$ the point $r\,e(\omega(\theta))$ lies in $F$
(because $0\le r\le\rho$) and outside $\bar B(0,r_0)$ (because $r>r_0$).
Hence the real-angle section of Lemma 9.1 satisfies
$\Sigma_r(F')\supset\Omega\cap(-\pi,\pi)$, and monotonicity together with
Lemma 8.3 applied to $\mathcal S=\mathcal R$ gives

$$\mathcal L^{1*}\bigl(\Sigma_r(F')\bigr)
\ \ge\ \mathcal L^{1*}\bigl(\Omega\cap(-\pi,\pi)\bigr)
\ \ge\ \mathcal L^{1*}(\mathcal R)=R .$$

Now apply Lemma 9.1 to $S=F'$ on $[r_1,\rho]$ with the constant section bound
$q\equiv R$, for each $r_1\in(r_0,\rho)$:

$$\mathcal L^{2*}(F')\ \ge\ \int_{r_1}^{\rho}rR\,dr=\frac{\rho^2-r_1^2}{2}R .$$

Letting $r_1\downarrow r_0$ gives the claim. (If $R=0$ the claim is trivial;
$R\le\pi<\infty$ always.) $\square$

### 8.5 The exterior ledger

By Proposition 5.3, for each selected stage $j$,

$$\mathcal L^{2*}\bigl(\operatorname{int}\Delta_{\theta_j}\setminus\bar B(0,r_0)\bigr)
=\mathcal L^{2*}\bigl(\Delta_{\theta_j}\setminus\bar B(0,r_0)\bigr)
\ \ge\ C_{\mathrm{ext}}H_j
=\frac{C_{\mathrm{ext}}}{4}\cdot 4H_j .
\tag{8.2}$$

Write $A^{\mathrm{ext}}=E\setminus\bar B(0,r_0)$ and
$P_j=\operatorname{int}\Delta_{\theta_j}\setminus\bar B(0,r_0)$. By Lemma 6.1
and $\Delta_{\theta_j}\subset E$ we have
$P_j\subset A^{\mathrm{ext}}\cap S(\theta_j,\delta_j)$, and by (B2) together
with Lemma 6.2 the cones $S(\theta_j,\delta_j)$ are open, measurable and
pairwise disjoint. Lemma 7.2 therefore gives, **unconditionally** — in
particular without using (B4) or the fan of §8.4 —

$$\frac{C_{\mathrm{ext}}}{4}\,B
=\sum_j C_{\mathrm{ext}}H_j
\ \le\ \sum_j\mathcal L^{2*}(P_j)
\ \le\ \mathcal L^{2*}\bigl(E\setminus\bar B(0,r_0)\bigr).
\tag{8.3a}$$

If in addition (B4) holds, so that the fan $F$ of §8.4 is defined, put
$M_\ast=\mathbb R^2\setminus\bigcup_jS(\theta_j,\delta_j)$, which is
measurable and disjoint from every cone, and
$P_\ast=F\setminus\bar B(0,r_0)\subset A^{\mathrm{ext}}\cap M_\ast$ — the
inclusion in $M_\ast$ being (B3), since every fan point has direction at
distance $\ge2H_j>\arcsin(\delta_j/\rho)$ from $\theta_j$, hence outside every
cone. Corollary 7.3 together with (8.2) and (B5) then gives

$$\frac{C_{\mathrm{ext}}}{4}\,B+C_{\mathrm{fan}}\,R
\ \le\ \sum_j\mathcal L^{2*}(P_j)+\mathcal L^{2*}(P_\ast)
\ \le\ \mathcal L^{2*}\bigl(E\setminus\bar B(0,r_0)\bigr).
\tag{8.3b}$$

### 8.6 The exterior branch bound

**Proposition 8.1 (exterior greedy budget).**
*Assume Hypotheses A, B, the height cap (8.1), and
$C_{\mathrm{ext}}>0$. Then for every $A\subset\mathcal A_{\mathrm{out}}$*

$$\mathcal L^{2*}\bigl(E\setminus\bar B(0,r_0)\bigr)
\ \ge\ C_{\mathrm{out}}\cdot\mathcal L^{1*}(A),
\qquad
C_{\mathrm{out}}=\min\Bigl\{\frac{C_{\mathrm{ext}}}{4},\,C_{\mathrm{fan}}\Bigr\}.$$

*Proof.* **Case $B=\infty$.** By (8.3a), which uses only the selected shadow
cones,
$\mathcal L^{2*}(E\setminus\bar B(0,r_0))\ge(C_{\mathrm{ext}}/4)\cdot\infty=\infty$
— here $C_{\mathrm{ext}}>0$ is used — and the inequality is trivial. Neither
(B4) nor §8.4 is invoked in this case.

**Case $B<\infty$** (which includes the finite-stop case, where the sum is
finite by definition). Then (B4) applies, so §8.4 and (8.3b) are legitimate,
and by (B1),

$$C_{\mathrm{out}}\,\mathcal L^{1*}(A)
\le C_{\mathrm{out}}R+C_{\mathrm{out}}B
\le C_{\mathrm{fan}}R+\frac{C_{\mathrm{ext}}}{4}B
\le\mathcal L^{2*}\bigl(E\setminus\bar B(0,r_0)\bigr). \qquad\square$$

**Remark 8.2.** Unlike the escaping branch of the published paper, the
present argument does **not** need $C_{\mathrm{out}}\le\rho^2/2$ or
$\rho>1/2$: the two coefficients are combined by an explicit minimum rather
than by a comparison. It also does not need $\rho\le1$.

---

## 9. The confined contribution

Three results are quoted from `paper/star_shaped_kakeya_bounds.tex`. They are
used verbatim and are **not** reproved here; only the reformulation noted
after Proposition 9.2 is applied to them.

**Lemma 9.1 (polar slicing for outer measure; paper Lemma 5.6, `lem:polar`).**
*Let $S\subset\mathbb R^2$ and $0<r_1<r_2$. Suppose that for every
$r\in[r_1,r_2]$ the **real-angle** section*

$$\Sigma_r(S):=\{\theta\in(-\pi,\pi):\ r\,e(\theta)\in S\}$$

*has $\mathcal L^{1*}\bigl(\Sigma_r(S)\bigr)\ge q(r)$, where $q$ is measurable
on $[r_1,r_2]$. Then*

$$\mathcal L^{2*}\bigl(S\cap\bar B(0,r_2)\bigr)\ \ge\ \int_{r_1}^{r_2}r\,q(r)\,dr.$$

*No measurability of $S$ or of its sections is assumed.*

The cut $(-\pi,\pi)$ is the standard polar fundamental domain used by the
paper's proof (it is the domain on which the polar-coordinate area formula is
applied). §8.4 uses the adapter of Lemma 8.3 to feed a projective direction
set into this real-angle statement.

**Proposition 9.2 (aggregate first-arc bound; paper Proposition 5.3
`prop:endpoint`, with Lemma 5.4 `lem:dilation` and the aggregation display
`eq:section`).** *Assume the height cap (8.1). For every $r\in[h_0,r_0]$ the
angular section of $\operatorname{Tri}(E)$ at radius $r$ has outer measure at
least $L_{\mathrm{in}}/g(r)$, with $g$ as in (2.1).*

The proof of Proposition 9.2 in the paper is stated with the mass $p\pi$
supplied by alternative (I) of the trichotomy; the argument is however
pointwise in $\alpha$ and uses only monotonicity of outer measure, so it
gives the section bound $\mathcal L^{1*}(\mathcal A_{\mathrm{in}})/g(r)$ for
the *actual* confined mass. This is the only reformulation applied to the
quoted material, and it is a weakening of nothing: taking
$L_{\mathrm{in}}\ge p\pi$ recovers the paper's statement.

**Proposition 9.3 (confined interior contribution).**
*Assume Hypotheses A, B and the height cap (8.1). Then*

$$\mathcal L^{2*}\bigl(E\cap\bar B(0,r_0)\bigr)\ \ge\ I\cdot L_{\mathrm{in}},
\qquad I=\int_{h_0}^{r_0}\frac{r}{g(r)}\,dr .$$

*Proof.* Apply Lemma 9.1 to $S=\operatorname{Tri}(E)$ with
$r_1=h_0<r_2=r_0$ and $q(r)=L_{\mathrm{in}}/g(r)$, which is legitimate by
Proposition 9.2 and is measurable in $r$ ($g$ is continuous). Then use
$\operatorname{Tri}(E)\subset E$ and monotonicity. $\square$

**Remark 9.4.** Only the *raw* radial integral appears. The published
confined branch multiplies by $k=1-f_0/(2r_0^2)$ and adds $f_0/4$ via the
strengthened Li Lemma 2.5, which converts local interior area into total area.
Here that conversion is deliberately **not** used: its exterior payments are
replaced by the sharper, geometrically separate exterior branch of §8, and
double counting is avoided because §8 charges only
$E\setminus\bar B(0,r_0)$ while §9 charges only $E\cap\bar B(0,r_0)$.

---

## 10. Assembly

**Hypothesis C (numerical gates).** The following four strict inequalities
between explicit reals hold:

$$\text{(C1)}\quad \frac{h_0}{2\pi}>T,
\qquad
\text{(C2)}\quad I>T,$$
$$\text{(C3)}\quad \frac{C_{\mathrm{ext}}}{4}>T,
\qquad
\text{(C4)}\quad C_{\mathrm{fan}}>T,$$

together with $C_{\mathrm{ext}}>0$ (implied by (C3) since $T>0$).

Hypothesis C is exactly what `certify.py` establishes with outward-rounded
Arb intervals; see §11.

**Theorem 10.1 (joint inner/outer lower bound, conditional on Hypothesis C).**
*Assume Hypotheses A, B, C. Then every star-shaped Kakeya set
$E\subset\mathbb R^2$ — with no measurability assumption — satisfies*

$$\mathcal L^{2*}(E)\ >\ \pi T=\frac{131\pi}{6250}=0.06584778\ldots$$

*Proof.* Translate the star centre to $0$; translation preserves outer
measure. Fix the chosen family $(N_\alpha)$ of §1.

**High branch.** If $h(\alpha)\ge h_0$ for some $\alpha$, then
$\mathcal L^{2*}(E)\ge\mathcal L^{2*}(\Delta_\alpha)=h(\alpha)/2\ge h_0/2
=\pi\cdot\frac{h_0}{2\pi}>\pi T$ by (C1).

**No-high branch.** Otherwise the height cap (8.1) holds. The closed ball
$\bar B(0,r_0)$ is measurable, so Lemma 7.1 gives, with no measurability of
$E$,

$$\mathcal L^{2*}(E)
=\mathcal L^{2*}\bigl(E\cap\bar B(0,r_0)\bigr)
+\mathcal L^{2*}\bigl(E\setminus\bar B(0,r_0)\bigr).$$

By Proposition 9.3 the first term is $\ge I\,L_{\mathrm{in}}$; by
Proposition 8.1 with $A=\mathcal A_{\mathrm{out}}$ the second term is
$\ge C_{\mathrm{out}}L_{\mathrm{out}}$ (here $C_{\mathrm{ext}}>0$ comes from
(C3)). Hence, with $c_\ast:=\min\{I,C_{\mathrm{out}}\}$ and using (1.1),

$$\mathcal L^{2*}(E)\ \ge\ I\,L_{\mathrm{in}}+C_{\mathrm{out}}L_{\mathrm{out}}
\ \ge\ c_\ast\,(L_{\mathrm{in}}+L_{\mathrm{out}})\ \ge\ c_\ast\,\pi .$$

By (C2), (C3), (C4), $c_\ast=\min\{I,C_{\mathrm{ext}}/4,C_{\mathrm{fan}}\}>T$,
so $\mathcal L^{2*}(E)>\pi T$. $\square$

**Corollary 10.2.** With
$\mathcal A_\ast=\inf\{\mathcal L^{2*}(E):E\text{ a star-shaped Kakeya set}\}$,

$$\mathcal A_\ast\ \ge\ \frac{131\pi}{6250}.$$

*Strictness discipline.* Theorem 10.1 is **strict** for each individual $E$;
the infimum inherits only the **non-strict** inequality, because an infimum of
quantities each $>\pi T$ can equal $\pi T$. This is the same convention as in
the published paper.

**Numerical situation of the four gates** (float scout values; the
authoritative values are the Arb intervals of §11):

| gate | quantity | value | $-T$ |
|---|---|---|---|
| C1 | $h_0/(2\pi)$ | $0.0209718468512$ | $+1.18\cdot10^{-5}$ |
| C2 | $I$ | $0.0209718240895$ | $+1.18\cdot10^{-5}$ |
| C3 | $C_{\mathrm{ext}}/4$ | $0.0527417216910$ | $+3.18\cdot10^{-2}$ |
| C4 | $C_{\mathrm{fan}}$ | $0.1035780162829$ | $+8.26\cdot10^{-2}$ |
| — | $T=131/6250$ | $0.02096$ | — |

The binding gate is C2 (the raw radial integral), with C1 essentially tied.

---

## 11. What the certificate proves, and what it does not

`certify.py` (this directory) establishes Hypothesis B and Hypothesis C using
`python-flint`/Arb interval arithmetic with outward rounding at 256 bits:

* every input is an exact `Fraction`; the fixed certificate path performs no
  binary-float conversion and is guarded by source inspection;
* every radical, denominator and domain sign is verified as a strict interval
  sign ($Q\ge0$, $Q<1$, $d>0$, $d<h_0/2$, $r_\lambda^2-d^2>0$,
  $1-2\sqrt{r_\lambda^2-d^2}>0$, $\rho>r_0$, $h_0<m\rho$, and both arcsine
  arguments $h_0/\rho$, $h_0/(m\rho)$ strictly inside $(0,1)$);
* $I$ is bounded **below** by an exact-rational partition of $[h_0,r_0]$ into
  $2^{16}$ cells whose per-cell integrand enclosure uses the Arb-native hull
  of the three branches of $g$, so the lower endpoint of the sum is a valid
  lower bound of the integral;
* the four gates C1–C4 are compared with $T$ using interval **lower**
  endpoints only.

The certificate does **not** prove any statement about star-shaped Kakeya
sets: it proves Hypothesis C for the fixed rational tuple. Theorem 10.1 as
argued *in this note* is the mathematical bridge, and that bridge is a paper
proof, not a machine-checked one. (Historical scope: the *conclusion* of
Theorem 10.1 is now independently a Lean theorem,
`universal_annular_lower_bound`, which does not use this certificate and
reproves the gates in exact rational arithmetic; see the status note in the
header.)

---

## 12. Explicit non-claims

1. No claim that $(h_0,r_\lambda,r_0)$ is optimal, canonical, or the result of
   a completed search of the legal domain. The scout in `scout.py` is a
   numerical spike; the tuple is a rationalisation of its basin.
2. No claim that $T=131/6250$ is the largest target this witness supports.
3. ~~No claim of a Lean theorem. §§4–8 are new and unformalised;
   Lemmas 9.1–9.2 are formalised for the *published* route only, and their
   reuse here still requires the reformulation noted after Proposition 9.2.~~
   **Superseded**: §§4–8 are now formalised, and the conclusion of Theorem 10.1
   is the Lean theorem `universal_annular_lower_bound`
   (`AnnularAssembly.lean:233`); the endpoint machinery of Lemmas 9.1–9.2 was
   reparameterised through a clean parameter interface so that the refinement
   instantiates it directly. What remains true is that this note itself is not
   machine checked, and that the Lean proof is independent of it.
4. ~~No claim that the exterior and interior contributions can be added for the
   *published* parameters, or that the published constant $100\pi/5599$ is
   superseded until Lean is complete.~~ **Superseded in part**: Lean is now
   complete for the tuple of §2, so $131\pi/6250$ is a Lean theorem and is the
   headline constant of the manuscript. The published $100\pi/5599$ remains a
   valid, unmodified and separately compiled Lean theorem
   (`universal_strong_lower_bound`); it is superseded numerically, not
   logically. Nothing is claimed about adding the two contributions at the
   *published* parameters.
5. The sharp width $W_\rho$ of Lemma 4.3 is proved but only its weakening
   $\arcsin(\delta/\rho)$ is used in Proposition 5.3; using $W_\rho$ itself
   would give a strictly better $C_{\mathrm{ext}}$ and is left unexploited on
   purpose, to keep the certified chain as short as possible.
6. $\mathcal A_{\mathrm{turn}}$ and the upper-bound part of the paper are
   untouched by this note.
7. This note is **not self-contained**: it is a proof *relative to* the quoted
   main-paper results listed in the Evidence status block and tagged
   `[paper]` in §13. If any of those is later found defective, the conclusion
   of Theorem 10.1 fails with it.

---

## 13. Dependency summary

Provenance tags: `[new]` proved in this note; `[classical]` standard real
analysis / measure theory; `[paper]` quoted from
`paper/star_shaped_kakeya_bounds.tex` and **not** reproved here.

```
Lemma 3.3* triangle reduction (area h/2)            [paper Lemma 3.3, lem:triangle]
Lemma 3.1  escaping needles avoid B(0,rho)          [new proof, statement as paper lem:outside]
Lemma 4.1  one-sided position (connectedness)       [new]
Lemma 4.2  direction set of Delta                   [new]
Lemma 4.3  exact maximal one-sided width W_rho      [new, sharp]
Prop  4.5  exterior area of one escaping triangle   [new]  <- 4.2, 4.3
Rem   4.6  sector step is an equality (sharpness)   [new]
Lemma 5.1  sin u / u decreasing                     [classical]
Lemma 5.2  arcsin(m sin u) <= m u                   [classical]
Prop  5.3  area_ext >= C_ext * H(delta)             [new]  <- 4.5, 5.1, 5.2
Lemma 6.1  shadow cone                              [new proof; cf. paper lem:shadow]
Lemma 6.2  separation => disjointness               [new proof; cf. paper lem:shadow]
Lemma 7.1  Caratheodory                             [classical]
Lemma 7.2  separated countable superadditivity      [classical]
Cor   7.3  exterior ledger                          [new packaging] <- 7.1, 7.2
Lemma 8.3  2*pi cut adapter                         [new]  -> feeds 9.1
(B1)-(B5)  greedy budget inequalities               [new]  <- 5.3, 6.2, 8.3, 9.1
Prop  8.1  exterior greedy budget                   [new]  <- 5.3, 6.2, 7.2, 7.3, 8.3, 9.1
Lemma 9.1  polar slicing for outer measure          [paper Lemma 5.6, lem:polar]
Prop  9.2  aggregate first-arc bound                [paper Prop 5.3 prop:endpoint,
                                                     + Lemma 5.4 lem:dilation,
                                                     + display eq:section]
Prop  9.3  confined interior contribution           [new packaging] <- 9.1, 9.2
Thm  10.1  joint lower bound                        [new]  <- 3.3*, 7.1, 8.1, 9.3, (C)
```

Paper Proposition 5.7 (`prop:li25`, strengthened Li Lemma 2.5) is quoted
nowhere in the chain above; see Remark 9.4 for why the new route does not use
it.
