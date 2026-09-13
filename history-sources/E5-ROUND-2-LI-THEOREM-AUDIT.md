# Round 2 audit: Li Lemma 2.5 and a corrected parametric Theorem 3.5

Provider: `[Codex]`

Date: 2026-07-31

## Hard verdict

- Li Lemma 2.5 applies to the present Case I after the slice object is written
  as \(E_{\rm all}=\bigcup_{\alpha\in[0,\pi)}\Delta_\alpha\): `confirmed`.
- The factor-\(3\)-free circle estimate applies to this same
  \(E_{\rm all}\): `confirmed`.
- The claim that the present Case II is a direct instance of Li Theorem 3.5:
  `refuted-as-a-source-scope-claim`.
- A corrected parametric replacement for Theorem 3.5, valid for
  \(\rho>1/2\): `proved-draft` after an independent derivation and a
  root-agent line-by-line audit.
- The universal \(\pi/56\) paper theorem: `proved-draft`.
- The universal \(\pi/56\) Lean theorem: `open`.

The source-scope refutation is not a counterexample to Case II.  The current
parameters have \(\rho=R_1-1>1/2\), whereas Li Section 3 and Lemma 2.4 fix the
cutoff radius in \([0,1/2]\).  The projective-angle proof below removes this
restriction and also repairs the infinite-selection bookkeeping.

No theorem-library entry is permitted before the full Lean target and a
final fresh audit close.

## Primary-source anchors

- Li's outer-measure conventions and triangle definition:
  `../star-shaped-kakeya-upper-bound/sources/li-2026.txt`, lines 43--83.
- Lemma 2.4: lines 177--188.
- Theorem 2.1's greedy selection and its displayed (2.8): lines 190--343.
- Lemma 2.5: lines 349--394.
- Section 3's fixed \(r\in[0,1/2]\) and fixed height cap: lines 419--425.
- Lemma 3.2 and the Case I/II formulas: lines 669--760.
- Lemma 3.3 and Theorem 3.5: lines 763--839.
- Radial-fan and polar-slicing Lemmas A.1--A.2: lines 951--1007.

The audited local PDF has SHA-256
`294b1f852bea222b4331d78fbe2a55617367f40e3b9e9da4737ba284448c87c8`.

## 1. Literal objects and parameters

Let \(E\subset\mathbb R^2\) be an arbitrary, possibly nonmeasurable,
star-shaped Kakeya set with star centre \(O=0\).  For every unoriented
direction \(\alpha\in\mathbb T_\pi\), choose a unit needle
\(l_\alpha\subset E\) and put

\[
\Delta_\alpha=\operatorname{conv}(0,l_\alpha),
\qquad
\delta_\alpha=\operatorname{height}(\Delta_\alpha),
\qquad
E_{\rm all}=\bigcup_{\alpha\in[0,\pi)}\Delta_\alpha.
\]

Then \(E_{\rm all}\subset E\).  The non-iterative parameters are

\[
a=\frac{449}{4000},
\qquad
r_\lambda=\frac{13}{56},
\qquad
r_0=\frac{49}{100},
\qquad
p=\frac{333}{400},
\qquad
\lambda=\frac{7220}{10577},
\]

with the exact identity

\[
r_\lambda=\lambda a+(1-\lambda)r_0.
\]

Define

\[
d=
\frac{
a\left(1-\sqrt{4r_\lambda^2+4a^2r_\lambda^2-a^2}\right)
}{
2(1+a^2)
},
\]

\[
R_1=
\frac{\sqrt{1+4d^2}}
{1-2\sqrt{r_\lambda^2-d^2}},
\qquad
\rho=R_1-1,
\]

\[
f(r)=\frac12r(2r-1)^2,
\]

\[
g(r)=
\max\left\{
\frac{1+2r}{1-2r},
\frac{1+2r_\lambda}{1-2r_\lambda},
\frac{\pi}{\pi/2-\arctan(2r)}
\right\},
\]

and

\[
k=1-\frac{f(r_0)}{2r_0^2}
=\frac{4899}{4900}.
\]

The direction sets are

\[
A_{\rm in}
=
\{\alpha:\Delta_\alpha\subset B_{R_1}\},
\qquad
A_{\rm out}
=
[0,\pi)\setminus A_{\rm in}.
\]

The three exhaustive branches are:

1. some \(\delta_\alpha\geq a\);
2. all \(\delta_\alpha<a\) and
   \(\mathcal L_1^*(A_{\rm in})\geq p\pi\);
3. all \(\delta_\alpha<a\) and
   \(\mathcal L_1^*(A_{\rm in})<p\pi\).

In the third branch, outer subadditivity gives

\[
\mathcal L_1^*(A_{\rm out})\geq(1-p)\pi.
\]

No measurability of either direction set is assumed.

## 2. Lemma 2.5 and the corrected Case I object

Li Lemma 2.5 is stated for \(A\subset[0,\pi)\), \(r\geq0.15\), and
\(E_A=\bigcup_{\alpha\in A}\Delta_\alpha\).  The current use has
\(A=[0,\pi)\) and \(r=r_0=49/100\).  The height branch has reduced to
\(\delta_\alpha<a<r_0\).

The factor-\(3\)-free circle proof must therefore conclude

\[
\mathcal H_1^*(E_{\rm all}\cap S_r)
\geqslant
\frac{p\pi r}{g(r)}
\]

for \(a\leq r\leq r_0\).  Writing this only for the larger set \(E\) would
not suffice to invoke Lemma 2.5.  The proof is available for
\(E_{\rm all}\), because every arc in the direction-covering argument is a
subset of its triangle \(\Delta_\alpha\).

Li Lemma A.2 handles arbitrary sets by open measurable supersets.  Hence

\[
\mathcal L_2^*(E_{\rm all}\cap B_{r_0})
\geqslant
p\pi\int_a^{r_0}\frac r{g(r)}\,dr.
\]

Lemma 2.5 gives

\[
\frac{\mathcal L_2^*(E)}{\pi}
\geqslant
pk\int_a^{r_0}\frac r{g(r)}\,dr+\frac{f(r_0)}4.
\]

This confirms the coefficient placement in Case I: \(p\) multiplies only the
integral term, while the full-direction baseline is \(f(r_0)/4\) after
normalization by \(\pi\).

## 3. Exact and Lean Case I layers

The finite exact certificate based on rational branch enclosures gives

\[
p\,k\,I_{\rm lb}+\frac{f(r_0)}4-\frac1{56}
=
\frac{
116569153710187543639191405603945643017
}{
72983798677231265966266373597152000000000000
}>0.
\]

Its seven-term mutation is negative, so the check is sensitive to the
logarithmic remainder.

`StarKakeyaLower.AnalyticKernel` additionally proves from
`Real.hasSum_log_one_add` that, for

\[
z=\frac{283}{1917},
\]

\[
\log\left(1+\frac{283}{817}\right)
\leqslant
2z+\frac{2z^3}{3}+\frac{2z^5}{5}
+\frac{2z^7}{1-z^2}.
\]

The corresponding exact integral lower bound is

\[
\frac{
163512203344334226603335030071
}{
7631310947411192372575200000000
},
\]

and the normalized Case I margin is

\[
\frac{
9903508366951835577422590421
}{
7802487979617077230176000000000000
}>0.
\]

The Lean declarations `alt_log_geom_upper`,
`alt_iLower_geom_le_exact`, `alt_caseI_geom_margin_exact`, and
`alt_caseI_exactPrimitive_strict` compile without `sorry`, `admit`, or a
custom axiom.  This pays the logarithmic remainder.  The branch-dominance and
integral-identification interfaces remain separate Lean obligations.

## 4. Why the direct Theorem 3.5 citation fails

Li Section 3 fixes \(r\in[0,1/2]\).  Li Lemma 2.4, used for exterior
disjointness, is likewise stated only for \(r\in[0,1/2]\).  Theorem 3.5
refers back to the proof of Theorem 2.1 and uses both this exterior
disjointness and Lemma 3.3's interior disjointness.

The current candidate lies strictly outside that domain.  Put

\[
Q=4r_\lambda^2(1+a^2)-a^2.
\]

Exact arithmetic gives

\[
Q=\frac{516003077}{2508800000}\in(0,1).
\]

Thus \(0<d<a/2\).  Moreover,

\[
r_\lambda^2-\left(\frac a2\right)^2-\frac1{36}
=
\frac{648093959}{28224000000}>0.
\]

Therefore

\[
\sqrt{r_\lambda^2-d^2}>\frac16,
\]

so the denominator of \(R_1\) is positive and smaller than \(2/3\), while
its numerator is at least \(1\).  Consequently

\[
R_1>\frac32,
\qquad
\rho=R_1-1>\frac12.
\]

There is a second source defect: step (3) in Li's proof of Theorem 3.5
retains \(4b/f(r)\), while step (4) says to replace \(f(r)\) by \(c(r)\)
throughout.  The height cap is inherited from the section's fixed
\(a=\pi/49\), not quantified as an arbitrary parameter in the theorem
statement.  The current Case II therefore cannot be labeled as a direct
instance of the printed theorem.

## 5. Corrected parametric Case II theorem

### Theorem

Let \(A\subset\mathbb T_\pi\) be arbitrary.  For every \(\alpha\in A\), let
\(l_\alpha\subset\mathbb R^2\setminus B_\rho\) be a closed unit segment of
unoriented direction \(\alpha\).  Assume \(\rho>1/2\), and let

\[
\delta_\alpha
=
\operatorname{dist}(0,\operatorname{aff}l_\alpha)
<a<\rho,
\]

and let

\[
\Delta_\alpha=\operatorname{conv}(\{0\}\cup l_\alpha).
\]

Then

\[
\mathcal L_2^*
\left(
\bigcup_{\alpha\in A}\Delta_\alpha
\right)
\geqslant
\frac{\mathcal L_1^*(A)}4\,c_a(\rho),
\qquad
c_a(\rho)=\frac{a}{2\arcsin(a/\rho)}.
\]

This includes arbitrary nonmeasurable \(A\) and triangle unions.

### Full-triangle disjointness

Let \(d_\pi\) be geodesic distance on \(\mathbb T_\pi\).  Suppose
\(P\in\mathring\Delta_1\cap\mathring\Delta_2\).  The ray \(OP\) meets the
relative interior of each base \(l_i\) at \(K_i=t_iP\), where \(t_i>1\).
Write \(\beta\) for the projective direction of this ray.

Because \(K_i\) lies in the relative interior of a segment contained in
\(\mathbb R^2\setminus B_\rho\), and because \(\delta_i<\rho\), one has
\(|K_i|>\rho\).  Equality would make \(K_i\) a local distance minimum on its
supporting line and force \(\delta_i=\rho\).  Therefore

\[
\sin d_\pi(\alpha_i,\beta)
=
\frac{\delta_i}{|K_i|}
<
\frac{\delta_i}{\rho}.
\]

The triangle inequality on \(\mathbb T_\pi\) gives

\[
d_\pi(\alpha_1,\alpha_2)
<
\arcsin(\delta_1/\rho)+\arcsin(\delta_2/\rho).
\]

Consequently,

\[
d_\pi(\alpha_1,\alpha_2)
\geqslant
\arcsin(\delta_1/\rho)+\arcsin(\delta_2/\rho)
\]

implies

\[
\mathring\Delta_1\cap\mathring\Delta_2=\varnothing.
\]

This proves the needed result for complete triangles directly; it does not
extend Li Lemma 2.4 by citation.

### Weighted greedy selection

Fix

\[
0<\varepsilon<1-\frac a\rho,
\qquad
m=1-\varepsilon,
\qquad
\kappa_\varepsilon=\frac{2\arcsin m}{\pi}.
\]

For \(\delta_\alpha>0\), define

\[
H_\alpha
=
\arcsin\left(\frac{\delta_\alpha}{m\rho}\right).
\]

The function \(x/\arcsin(x/\rho)\) is decreasing on \((0,\rho)\), so

\[
\frac{\delta_\alpha}{2}
\geqslant
c_a(\rho)\arcsin(\delta_\alpha/\rho).
\]

The function \(u\mapsto\arcsin(m\sin u)\) is concave on
\([0,\pi/2]\).  Comparing it with its endpoint chord gives

\[
\arcsin(\delta_\alpha/\rho)
=
\arcsin(m\sin H_\alpha)
\geqslant
\kappa_\varepsilon H_\alpha.
\]

Hence

\[
|\Delta_\alpha|
=
\frac{\delta_\alpha}{2}
\geqslant
c_a(\rho)\kappa_\varepsilon H_\alpha.
\]

Let \(I_\alpha\) be the saturated circle interval in \(\mathbb T_\pi\)
centered at \(\alpha\) with radius \(2H_\alpha\).  Its length is at most
\(4H_\alpha\).  Starting from the remaining set \(R\), whenever
\(\sup_R\delta>0\), choose \(\alpha_n\in R\) with

\[
\delta_n>m\sup_{\alpha\in R}\delta_\alpha
\]

and delete \(I_n\).  If \(j<n\), then

\[
d_\pi(\alpha_j,\alpha_n)
\geqslant
2H_j
>
\arcsin(\delta_j/\rho)+\arcsin(\delta_n/\rho).
\]

The selected full triangles therefore have pairwise disjoint interiors.

Put

\[
B_\varepsilon=\sum_n4H_n,
\qquad
b_\varepsilon=
\frac{c_a(\rho)\kappa_\varepsilon}{4}B_\varepsilon.
\]

The measurable union \(G=\bigcup_n\mathring\Delta_n\) satisfies

\[
|G|
=
\sum_n|\Delta_n|
\geqslant
b_\varepsilon.
\]

If \(B_\varepsilon=\infty\), the theorem follows immediately.  Otherwise
\(H_n\to0\), and hence \(\delta_n\to0\).  The greedy rule forces every
residual direction in

\[
A_0=A\setminus\bigcup_nI_n
\]

to have \(\delta_\alpha=0\).  Outer subadditivity gives

\[
\mathcal L_1^*(A_0)
\geqslant
\mathcal L_1^*(A)-B_\varepsilon.
\]

This definition of \(B_\varepsilon\) corrects a factor in Li's displayed
(2.8): the paper defines \(b=(1-\varepsilon)\sum_n|I_n|\), which does not
itself bound \(\left|\bigcup_nI_n\right|\).

### Residual radial fan and minimax closure

When \(\delta_\alpha=0\) and \(l_\alpha\subset B_\rho^c\),
\(\Delta_\alpha\) contains a radial segment from \(0\) to radius \(\rho\).
Choose its oriented angle \(\theta_\alpha\in\mathbb T_{2\pi}\), and let
\(\Theta=\{\theta_\alpha:\alpha\in A_0\}\).  The quotient

\[
q:\mathbb T_{2\pi}\longrightarrow\mathbb T_\pi
\]

is \(1\)-Lipschitz and maps \(\Theta\) onto \(A_0\).  Thus

\[
m_{2\pi}^*(\Theta)\geqslant m_\pi^*(A_0).
\]

Li Lemma A.1 gives the residual fan \(F\) the outer-measure bound

\[
\mathcal L_2^*(F)
\geqslant
\frac{\rho^2}{2}
\left(
\mathcal L_1^*(A)-B_\varepsilon
\right).
\]

If a residual radial ray met \(\mathring\Delta_n\), its angle from the base
direction would be strictly smaller than
\(\arcsin(\delta_n/\rho)<H_n\), contradicting exclusion from the
radius-\(2H_n\) interval \(I_n\).  Hence \(F\cap G=\varnothing\).

Let

\[
M=
\mathcal L_2^*
\left(
\bigcup_{\alpha\in A}\Delta_\alpha
\right),
\qquad
L=\mathcal L_1^*(A),
\qquad
s=\frac{\rho^2}{2}.
\]

Because \(G\) is measurable, Carathéodory additivity gives

\[
M\geqslant b_\varepsilon
\]

and

\[
M
\geqslant
b_\varepsilon
+s\left(
L-\frac{4b_\varepsilon}
{c_a(\rho)\kappa_\varepsilon}
\right).
\]

Set

\[
\mu_\varepsilon
=
1-\frac{2\rho^2}
{c_a(\rho)\kappa_\varepsilon}.
\]

Since

\[
\arcsin(a/\rho)>\frac a\rho,
\]

one has

\[
c_a(\rho)<\frac\rho2.
\]

For \(\rho>1/2\), this implies \(\mu_\varepsilon<0\).  As
\(b_\varepsilon\leq M\),

\[
M
\geqslant
sL+\mu_\varepsilon b_\varepsilon
\geqslant
sL+\mu_\varepsilon M.
\]

Exact coefficient reduction yields

\[
M
\geqslant
\frac{c_a(\rho)\kappa_\varepsilon}{4}L.
\]

Letting \(\varepsilon\downarrow0\), one has
\(\kappa_\varepsilon\uparrow1\), proving the theorem.

## 6. Application to the candidate

If \(\Delta_\alpha\not\subset B_{R_1}\), some \(x\in l_\alpha\) has
\(|x|\geq R_1\).  For every \(y\in l_\alpha\),

\[
|y|\geq|x|-|x-y|\geq R_1-1=\rho.
\]

Thus \(l_\alpha\subset B_\rho^c\), and the corrected theorem gives

\[
\frac{\mathcal L_2^*(E)}{\pi}
\geqslant
\frac{1-p}{4}\frac{a}{2\arcsin(a/\rho)}.
\]

The strict comparison with \(1/56\) is equivalent to

\[
\arcsin(a/\rho)<7(1-p)a.
\]

The existing radical and inverse-trigonometric certificate proves this
through the exact positive margin

\[
\frac{
8595227380165644121
}{
59375508286970145600000
}>0.
\]

Therefore Case II is closed at paper level.

## 7. Source-domain parameter scout

As a diagnostic, the candidate family was also searched under
\(\rho\leq1/2\), where Li's printed radius domain would apply without the
new theorem.  Eight differential-evolution runs followed by SLSQP refinement
converged near

\[
\begin{aligned}
a&\approx0.112199837664,\\
r_\lambda&\approx0.169920968740,\\
r_0&\approx0.44722,\\
\rho&\approx0.499999999764,\\
p&\approx0.738911356486.
\end{aligned}
\]

The best observed minimax value was

\[
0.01617908432913
<
\frac1{56}
\approx0.01785714285714.
\]

The integral was cross-checked independently to approximately \(10^{-14}\),
and all runs pressed against \(a\downarrow\pi/28\) and
\(\rho\uparrow1/2\).

This is `numerical` scouting only.  It is neither a proof that the constrained
family cannot reach \(1/56\) nor evidence for the universal theorem.

## 8. Current completion boundary

The paper-level Case II gap is closed by the parametric theorem above.
Together with the independently audited circle theorem, Li endpoint
containment, scoped Lemma 2.5 application, exact Case I/II certificates, and
height branch, this gives a `proved-draft` universal \(\pi/56\) proof.

The campaign is not complete because the user-required Lean theorem remains
open.  The present Lean package has exact arithmetic and the Case I log
series.  It still needs the circle outer-measure theorem, Li endpoint
geometry, the parametric Case II selection/fan argument, the remaining
inverse-trigonometric and branch bridges, and the final universal assembly.
