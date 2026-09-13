# Full-cone capped far-arc kernels for every Borel cut

## Result and boundary of the claim

**Result.** Under the recovered height bound `|h|<=1/5`, the literal triangle
union admits an all-cut far-arc kernel on **every radius below the least far
endpoint radius**, including radii below the nearest point of the segment.
Its explicit bounded-radius version strictly improves the old terminal kernel
at every positive radius of that kernel's support. A separate joint-geometry
estimate improves the old low kernel pointwise, strictly on a nonempty radial
interval, without centering or equal-height assumptions.

**Still OPEN: area 1/10.** Even perfecting the full-cone constant in the
common-uniform far-base extension-ratio construction with factor `1+2*rho`
cannot pay the low class at rate `1/(10*pi)`.
Section 8 gives an exact ceiling for this proof route. No new numerical
universal area constant, price schedule, or 1/10 theorem is asserted.

The only imported mathematical source is `../../baseline/PROOF.md`, read in
full: its open-cover Borel recovery, interval-union lemma (1), and common-source
price accounting. Its constants are compared, not edited or rerun. The
arguments below are human proofs with six tiny exact controls, not formalized
proofs. Independent adversarial review remains a promotion gate.

## 1. Quantifiers, actual source, and joint endpoint domain

Fix a Borel set `D` of unoriented directions on `RP^1`, whose length is pi.
For every `q in D` let a unit segment depend Borel-measurably on q. This includes
the finite-valued midpoint selector recovered from an arbitrary original
selector by the baseline's open-cover argument. Put

\[
 T_q=\operatorname{conv}(0,A_q,B_q),\qquad
 W(V)=\bigcup_{q\in V}T_q
\]

for **every Borel subcut** `V subset D`. Its radius-r angular section is `S_r(V)`
on the actual ordinary circle of length `2*pi`; no reflection or antipodal copy
is added to W. These unions and sections are analytic, hence measurable.

Orient the chord toward a far endpoint, making a fixed Borel choice at ties.
In the resulting local orthonormal coordinates the endpoints are

\[
 (x-1,h),\quad (x,h),\qquad x=|s|+\tfrac12\ge\tfrac12.
\]

Writing `z=|h|`, their radii obey exactly

\[
 M^2=x^2+z^2,\quad N^2=(x-1)^2+z^2
       =M^2+1-2\sqrt{M^2-z^2},\quad M^2-z^2\ge\tfrac14. \tag{1}
\]

The minimum radius of a point **of the segment** is

\[
 a_{\min}=\begin{cases}z,&1/2\le x\le1,\\N,&x>1.\end{cases} \tag{2}
\]

In particular `M<1` implies `x<1`, so the perpendicular foot is on the segment.
Conversely `N` is not generally the closest segment radius. All bounds below
retain (1); any subsequent relaxation is stated explicitly.

For arbitrary star-shaped E, first pass to an open G containing E, recover the
Borel selector with all triangles inside G, and **rerun** the height dichotomy.
If a recovered triangle has `|h|>=1/5`, then `|G|>=1/10`. Otherwise the following
low-height results apply. No regularity of the original selector is used.

## 2. Exact circular sections, including radial filling

For `z>0`, measure the local angle phi from the oriented far chord direction,
on the actual side indicated by the sign of h. Define

\[
 b=\arctan(z/x),\qquad d=\operatorname{atan2}(z,x-1),\qquad
 \gamma=d-b\in(0,\pi).
\]

Here `0<b<pi/2` and `b<d<pi`. The triangle's cone is `[b,d]`. On a ray in this
cone the base segment is at radius `z/sin(phi)`; the triangle contains all
smaller radii on that ray. Hence its **entire** circular section is

\[
 S_r(T_q)=
 \begin{cases}
 [b,d],&0<r\le z,\\
 [b,d]\cap\bigl([0,a_r]\cup[\pi-a_r,\pi]\bigr),
       &r>z,\quad a_r=\arcsin(z/r).
 \end{cases} \tag{3}
\]

The intervals here are transported to their original physical angles. The
choice of local signed coordinates is not a symmetrization of the source.
Equation (3) covers disconnected lobes, tangency, and an exterior foot.

In particular, for **all** `r<=a_min` the whole cone `[b,d]` is present. When
`x>1` and `z<r<N`, one has `d<a_r`, so this assertion still follows from the
second line of (3). Absence of segment-circle intersection does not mean
absence of triangle-circle intersection.

For `0<r<M`, the following single physical far base is always present:

\[
 J_r(q)=
 \begin{cases}
 [b,d],&r\le z,\\
 [b,\min(d,a_r)],&z<r<M.
 \end{cases} \tag{4}
\]

Its length is gamma in the first case and `min(gamma,a_r-b)` in the second.
This is the crucial cap missing when a window formula is used outside its
support. It is not legitimate to replace this minimum by `a_r-b` when `r<N`
for an exterior-foot chord.

When `z=0`, the actual triangle consists of the positive radial interval
`[0,x]` and, only if `x<1`, the negative radial interval of length `1-x`.
At `r<M=x` select the **actual singleton far anchor** as J. This treats the
zero-height directions literally; they are not dropped as a null label set.

## 3. All-cut full-cone cap theorem

**Theorem 1 (uniform joint-domain cap).** Assume `M>=m>=1/2` on D. Suppose a
finite `B>=0` satisfies

\[
 \frac{b}{\gamma}\le B \qquad(q\in D,\ z>0). \tag{5}
\]

Then, for every Borel `V subset D` and every `0<r<m`,

\[
 |S_r(V)|\ge G_{m,B}(r)|V|,\qquad
 G_{m,B}(r)=\min\left\{\frac1{1+2B},\frac{m-r}{m+r}\right\}. \tag{6}
\]

Set G to zero outside `(0,m)` if an everywhere-defined radial kernel is needed.
The domain, constants and kernel are fixed before V is chosen.

*Proof.* Extend each actual interval (4) to its ideal far anchor by the one-sided
length b. If `r<=z`, the extension/base ratio is at most B. If `z<r`, monotonicity
of `arcsin(t)/t` gives

\[
 \frac b{a_r}=\frac{\arcsin(z/M)}{\arcsin(z/r)}\le\frac rM,
 \qquad \frac b{a_r-b}\le\frac r{M-r}\le\frac r{m-r}.
\]

By the **actual minimum** in (4), the ratio for J is at most
`max(B,r/(m-r))`. For `z=0` the singleton requires no extension.

Apply the baseline interval-union lemma **once to all these bases together**,
with `Lambda=1+max(B,r/(m-r))`. The extended union contains one Borel far lift
of every direction of V. Such a lift has ordinary-circle length exactly `|V|`:
it is a Borel choice between the two antipodal lifts, not both lifts. Thus

\[
 |V|\le(1+2\max(B,r/(m-r)))\left|\bigcup_{q\in V}J_r(q)\right|
       \le(1+2\max(B,r/(m-r)))|S_r(V)|.
\]

This is (6). Mixed signs of h and far-endpoint switches are already allowed by
the interval lemma's two-sided component enlargement. There is no summation
of per-label triangle mass or separate recharging of the cone and lobe cases.
\(\square\)

An exact, possibly implicit constant in (5) is the supremum of the literal
`atan(z/x)/(atan2(z,x-1)-atan(z/x))` on any chosen jointly feasible regime.
Theorems 2 and 3 supply explicit bounds; no optimization of that supremum is
needed or performed.

## 4. Explicit bounded-radius kernel, stronger than the old terminal bound

**Theorem 2.** Let `0<H<=1/2`, `m>=1/2`,
`R>=max(m,sqrt(1/4+H^2))`, and assume `m<=M<=R`, `|h|<=H` on D. Then (6) holds
with

\[
 B_{R,H}=\frac{R^2}{\sqrt{R^2-H^2}},\qquad
 K_{R,H}=\frac1{1+2B_{R,H}}. \tag{7}
\]

*Proof.* The literal cone angle is

\[
 \gamma=\int_{x-1}^{x}\frac z{t^2+z^2}\,dt.
\]

Since `x>=1/2`, every t in this interval satisfies `|t|<=x`. Therefore

\[
 \gamma\ge\frac z{x^2+z^2}=\frac z{M^2},\qquad
 b\le\frac zx,\qquad \frac b\gamma\le\frac{M^2}{x}
             =x+\frac{z^2}{x}. \tag{8}
\]

At fixed z, the last expression is increasing for `x>=1/2>=z`. The exact
feasible upper endpoint is `x=sqrt(R^2-z^2)`, not an independently assigned
near radius. Thus (8) is at most `R^2/sqrt(R^2-z^2)`, increasing in z, and is
at most (7). The assumption on R ensures the maximizing boundary at z=H is
feasible. These are explicit upper relaxations of the angular ratio, not a
claim that (8) is sharp. Apply Theorem 1. \(\square\)

**Strict comparison.** With `H=1/5`, for every permitted `m,R` with `m>1/2`
and every `0<r<m`,

\[
 \min\{K_{R,H},(m-r)/(m+r)\}
   >\frac{\min(1/2,m-r)}{\pi R}. \tag{9}
\]

The right side is the accepted terminal kernel (5). Indeed the simpler bound
`B_{R,H}<=R+2H^2` follows directly from (8), `x<=R`, `x>=1/2`. Hence

\[
 K_{R,H}\ge\frac1{1+2R+4/25}>\frac1{2\pi R},
\]

where the strict inequality follows from `R>=1/2`, `pi>3`:
`2*pi*R-(1+2R+4/25)>=pi-54/25>0`.
Also `m+r<2m<=2R<pi*R`, so
`(m-r)/(m+r)>(m-r)/(pi*R)`. Both entries of the minimum strictly exceed the old
kernel. This comparison is uniform, not a fixed-radius numerical observation.
It uses the low-height hypothesis, which the old terminal bound did not need.

**Frozen finite-high example.** For `m=99/100`, `R=8/5`, `H=1/5`, the new cap is

\[
 K_F=\frac{5\sqrt{63}}{5\sqrt{63}+128}>
       \frac{73}{323}=\frac{99/100-5/8}{99/100+5/8}. \tag{10}
\]

Since the other branch decreases in r, the new kernel equals
`(99/100-r)/(99/100+r)` throughout `[5/8,4/5]`, retaining the old P-window bound
there, but it is now valid on the **whole** interval `(0,99/100)` and for P and Z
together. Equation (9) gives strictly more than the old all-F terminal payment
at every active radius. This does not authorize adding the new all-F bound to
the old P/Z bounds on the same physical source without separate prices.

## 5. A sharper cone cap for every straddling low chord

The crude integral bound (8) is not used for the low improvement.

**Theorem 3.** Fix `H>0`. Suppose `1/2<=x<1`, `|h|<=H`, and `M>=1/2`. Define

\[
 b_0=\arctan(2H),\quad b_1=\arctan H,\qquad
 B_L=\max\left\{\frac{b_0}{\pi-2b_0},
                    \frac{b_1}{\pi/2-b_1}\right\},
\]
\[
 K_L=\frac1{1+2B_L}
   =\min\left\{1-\frac{2\arctan(2H)}\pi,
          \frac{\pi/2-\arctan H}{\pi/2+\arctan H}\right\}. \tag{11}
\]

For every Borel subcut V and `0<r<1/2`,

\[
 |S_r(V)|\ge g_{\rm new}(r)|V|,\qquad
 g_{\rm new}(r)=\min\{K_L,(1/2-r)/(1/2+r)\}. \tag{12}
\]

*Proof of the new cap.* For `z>0`, write
`c=atan(z/(1-x))`, so `gamma=pi-b-c`. Fix z and relax the feasible x-interval
to `[1/2,1]`, with `c(1)=pi/2` interpreted as the limit. Set `A=1+1/B_L`.
For `1/2<x<1`, the sign of the derivative of

\[
 F(x)=\arctan(z/(1-x))+A\arctan(z/x)
\]

is the sign of

\[
 x^2+z^2-A((1-x)^2+z^2).
\]

The latter has derivative `2x+2A(1-x)>0`. Therefore F decreases then increases,
or is monotone, and its **maximum is at an endpoint**, not at an unproved
sampled interior extremum. At x=1/2 and x=1 respectively, the definition of B_L
and `z<=H` give

\[
 F(1/2)=(A+1)\arctan(2z)\le\pi,\qquad
 F(1)=\pi/2+A\arctan z\le\pi.
\]

Thus `c+(1+1/B_L)b<=pi`, equivalent to `b/gamma<=B_L`. Theorem 1 with `m=1/2`
proves (12). This argument permits arbitrary x(q) and z(q); no centered or
constant-height selector is assumed. The limit x=1 is an explicitly enlarged
domain, not an extra physical chord or a discarded near endpoint. \(\square\)

## 6. Exact comparison with both branches of the frozen low theorem

Now take `H=1/5`, `M0=99/100`, and `m0=1-M0=1/100` as in the baseline. Then
`M<M0` implies the straddling hypothesis of Theorem 3. From `atan t<t` and
`pi>3`, the two entries in (11) satisfy respectively

\[
 1-2\arctan(2/5)/\pi>11/15,\qquad
 \frac{\pi/2-\arctan(1/5)}{\pi/2+\arctan(1/5)}>13/17>11/15.
\]

Consequently `K_L>11/15`.

In the baseline notation

\[
 \alpha=2\arcsin(50/99),\quad\beta=\arctan20,\quad
 c_H=\frac{2\alpha}{\alpha+2\beta},\quad
 k=\frac\alpha{\alpha+2\arcsin(2/5)}.
\]

Both old cone caps are strictly below `2/3`:

* `alpha<beta`, since `cos(alpha)=4801/9801>1/sqrt(401)=cos(beta)`;
  the positive squared rational guard is checked in control 4. Hence `c_H<2/3`.
* `alpha<pi/2<8/5` and `2*arcsin(2/5)>4/5`, so `k<2/3`.

On `0<r<m0`, the old two-anchor kernel is at most `c_H<2/3`, whereas the new
kernel is greater than `11/15`, because its rational branch is greater than
`49/51`. On `m0<=r<1/2`, the old kernel is `min(k,(1/2-r)/(1/2+r))` and the new
one replaces k by the strictly larger K_L. Thus the new kernel dominates the
**whole frozen low kernel**, strictly for

\[
 0<r<c_{\rm old}:=\frac{1-k}{2(1+k)},
\]

and agrees with it for `c_old<=r<1/2`. Here `c_old>1/10>m0` follows from `k<2/3`.
Both are set to zero for `r>=1/2`. The improvement is in the union theorem,
not a reparametrization or a sum of individual low-chord masses.

## 7. Radial integration and source-once composition

For any one of these fixed jointly feasible direction classes D, every
nonnegative Borel radial price p satisfies, in the extended nonnegative sense,

\[
 \left(\int_0^\infty p(r)\min(r,1)G_D(r)\,dr\right)|V|
 \le\int_{W(V)}p(|x|)\,d\nu(x),\qquad
 d\nu=\min(1,1/|x|)\,dx, \tag{13}
\]

for every Borel V contained in D. This follows from the all-cut section theorem
and polar integration, not by integrating labelwise lower bounds.

For several classes/subclasses use prices fixed before the cut, whose pointwise
sum is at most one, exactly as in baseline Section 6. Then the sum of the right
sides is at most `nu(W)<=|G|`, even though the subunions overlap. In particular:

* cone and partial-lobe cases have already been combined inside **one** interval
  lemma; their payments are not added;
* an all-F payment is issued once to F, not separately at full price to P and Z;
* two valid estimates of one physical source may be maximized, not added,
  unless radial prices or an actual disjoint source partition license addition.

For a nonmeasurable original E, the recovery and height dichotomy of Section 1
must precede these arguments, and only then may one infimize over open G.
Nothing here modifies the accepted outer-measure interface.

## 8. Exact obstruction: this one-far-lobe route cannot close 1/10

The new low theorem is genuinely stronger, but for any price `0<=p<=1` its
per-radian coefficient is bounded above by

\[
 \int_0^{1/2}r\,\frac{1/2-r}{1/2+r}\,dr
       =\frac38-\frac12\log2. \tag{14}
\]

This remains an upper ceiling if K_L is improved all the way to 1. The positive
series `log2=2 sum_{j>=0}(1/3)^(2j+1)/(2j+1)` gives `log2>56/81`; with
`pi<22/7`, the corresponding full-direction area coefficient obeys

\[
 \pi\left(\frac38-\frac12\log2\right)
 <\frac{22}7\left(\frac38-\frac{28}{81}\right)
 =\frac{209}{2268}<\frac1{10}. \tag{15}
\]

This is a **payment-method ceiling**, not an upper bound on the actual area of
low star-Kakeya unions, and not a counterexample to a possible 1/10 theorem.

There is a literal joint-domain reason the rational branch cannot simply be
raised inside this same extension argument. Take feasible centered chords
`x=1/2`, `z downarrow 0`, with `M=sqrt(1/4+z^2)<M0`. At any fixed `0<r<1/2`,

\[
 \frac b{|J_r|}
 =\frac{\arctan(2z)}{\arcsin(z/r)-\arctan(2z)}
 \longrightarrow\frac r{1/2-r}. \tag{16}
\]

Thus a uniform extension/base bound for **only this far lobe and anchor** must
allow at least this ratio. The baseline interval-union factor `1+2*ratio` then
cannot give a coefficient exceeding `(1/2-r)/(1/2+r)`. The degeneration is
inside the actual endpoint domain, not a box-relaxation artifact. The h=0
singleton itself has no drift, but the positive-height limit is admissible.
Equation (16) does not claim the interval-union inequality is saturated by an
actual selector family; it isolates the exact ceiling of this particular
proof construction. It does not exclude asymmetric, sign-dependent, or
class-refined far-only arguments, and the upper ceiling is not claimed to be
an attained optimum of the unrelaxed construction.

**Missing universal bridge.** A 1/10 proof still needs an all-cut low-source
estimate stronger than this one-far-lobe ceiling (for example, a proved joint
use of both physical endpoint lobes), or a global geometric theorem linking
low and high direction classes that rules out the unpaid low demand. Merely
optimizing radial prices, sharpening the full-cone cap, using the improved
high kernel, or asserting triangle contributions add cannot bridge (15).
No such missing theorem is assumed here.

## 9. Verification and status ledger

| Claim | Status / evidence |
|---|---|
| Joint endpoints, closest-radius distinction, full circular sections | PROVED, Sections 1–2; controls 1–3 |
| All-Borel-cut cap theorem, mixed signs and zero-height included | PROVED analytically, Section 3 |
| Strict improvement over old terminal kernel throughout support | PROVED analytically, Section 4 |
| Retention of old finite-high window with extension below it | PROVED, (10); control 5 |
| Strict pointwise improvement of frozen low kernel | PROVED analytically, Sections 5–6; control 4 |
| Source-once price integration | PROVED using accepted recovery/polar interface, Section 7 |
| One-far-lobe payment ceiling below 1/10 | PROVED analytically, Section 8; control 6 |
| Universal area 1/10 / new optimized universal constant | OPEN / not claimed |
| Independent adversarial proof review | Pending parent review |

`ADMISSION-LOCAL.md` preregisters six fixed rational controls and the inherited
one-subprocess arithmetic budget. `check.py` checks their exact guards plus
four symbolic identities. It does not certify the geometric or measure-theoretic
proof. `CHECK-RESULT.txt` records the one real execution. No searches, numerical
quadratures, schedule experiments, historical imports, or other lane edits are
part of this result.
