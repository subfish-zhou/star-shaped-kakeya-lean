# No-go theorem for pointwise antipodal radial floors

Date: 2026-08-03

## Theorem

There is no universal constant \(c>0\) such that every star-shaped Kakeya set,
every star centre, every selected unit-needle family, and every oriented angle
\(\phi\) satisfy

\[
\rho(\phi)^2+\rho(\phi+\pi)^2\ge c.
\]

The claim remains false if "every angle" is replaced by almost every angle,
essential infimum, any fixed lower-quantile/prevalence requirement with
\(q\in(0,1)\), or a uniform local average on
windows shorter than the projective circle.

## 1. Literal far common-centre family

Fix \(R>1/2\), put \(P_R=(R,0)\), and for each projective direction
\(\theta\in\mathbb R/\pi\mathbb Z\) select the unit segment

\[
N_\theta=P_R+[-1/2,1/2]e(\theta).
\]

Every projective direction occurs.  The union of the needles is exactly the
closed disk

\[
D_R=\overline B(P_R,1/2),
\]

because each disk point can be written as \(P_R+s e(\theta)\) with
\(|s|\le1/2\).  Its radial hull

\[
E_R=\bigcup_{x\in D_R}[0,x]
=\operatorname{conv}(\{0\}\cup D_R)
\]

is compact, convex, star-shaped about the origin, and contains every selected
needle.  Thus this is a literal star-shaped Kakeya set, not a formal endpoint
configuration.

## 2. Exact radial support

Define

\[
\alpha_R=\arcsin\frac1{2R}\in(0,\pi/2).
\]

Represent an oriented angle by \(\phi\in(-\pi,\pi]\).  A ray from the origin
meets \(D_R\) exactly when \(|\phi|\le\alpha_R\).  On this cone the far radial
intersection is

\[
\rho_R(\phi)
=R\cos\phi+
\sqrt{\frac14-R^2\sin^2\phi},
\]

and outside the cone \(\rho_R(\phi)=0\).

At the antipodal pair \(\phi=\pi/2\),
\(\phi+\pi=3\pi/2\equiv-\pi/2\pmod{2\pi}\), both rays lie outside
the support cone.  Hence

\[
\rho_R(\pi/2)=\rho_R(3\pi/2)=0.
\]

More strongly, the projective pair function

\[
F_R(\phi)=\rho_R(\phi)^2+\rho_R(\phi+\pi)^2
\]

vanishes on the entire open projective interval

\[
(\alpha_R,\pi-\alpha_R),
\]

of length \(\pi-2\alpha_R>0\).  Therefore the best universal pointwise or
essential-inf constant is exactly zero.

## 3. Stronger failed repairs

The oriented support of \(\rho_R\) has total angular length \(2\alpha_R\), while
that of the projective pair function has length \(2\alpha_R\) on the projective
circle (equivalently \(4\alpha_R\) before antipodal identification).  As
\(R\to\infty\), this tends to zero.

Consequently the same family refutes:

- an almost-everywhere positive floor;
- a positive essential infimum;
- any fixed lower-quantile/prevalence requirement with \(q\in(0,1)\);
- any uniform moving-average floor on angular windows of fixed length
  \(\ell<\pi\), since a sufficiently large \(R\) leaves a zero interval longer
  than \(\ell\).

## 4. What survives is only the global capacity identity

For this compact Borel family, ordinary integrals are legitimate and

\[
\int_0^\pi F_R(\phi)\,d\phi
=
\int_{S^1}\rho_R(\phi)^2\,d\phi
=2\operatorname{Cap}_2(E_R)
=2|E_R|.
\]

Thus a full-projective-circle linear average lower bound for \(F\) is exactly a
radial-capacity/area lower bound in different notation.  For an arbitrary
selector the corresponding statement must use the upper integral and the
selector's radial-hull capacity; the present ordinary integral equals
\(|E_R|\) because this example is compact and Borel.  In either formulation it
is not a new antipodal mechanism.

For reference, direct tangent geometry gives

\[
|E_R|
=\frac\pi8+\frac{\alpha_R}{4}
 +\frac12\sqrt{R^2-\frac14}.
\]

This grows linearly with \(R\): the example kills local and pointwise floors by
concentrating its radial mass in a narrow cone, not by making total area small.

## Evidence boundary

- The set construction, radial formula, positive-measure zero interval, and
  global-average identity are paper-level exact calculations.
- This no-go refutes pointwise, essential-inf, quantile, and fixed local-average
  antipodal routes.  It does not refute unrelated global nonlinear functionals.
- The valid universal lower bound remains
  \[
  \mathcal L^{2*}(E)\ge C_{\rm FS}\ge141/2000.
  \]
