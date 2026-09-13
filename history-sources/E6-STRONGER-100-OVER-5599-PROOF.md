# A strict \(100\pi/5599\) lower bound

Provider: `[Codex]`

Date: 2026-07-31

Status: `proved-draft` on paper; the universal Lean formalization is
**closed** — see `StarKakeyaLower.universal_strong_lower_bound`.

## Theorem

Every star-shaped Kakeya set \(E\subset\mathbb R^2\), without a
measurability assumption, satisfies

\[
\mathcal L_2^*(E)>\frac{100\pi}{5599}.
\]

In particular,

\[
\mathcal L_2^*(E)>\frac{\pi}{56},
\]

because

\[
\frac{100}{5599}-\frac1{56}=\frac1{313544}>0.
\]

## 1. Fixed-parameter trichotomy used in this proof

Choose one unit needle in every unoriented direction and join each needle to
the star centre.  The circle-dilation theorem, the correctly typed endpoint
containment on
\(\mathbb T_{2\pi}\to\mathbb T_\pi\), Li's Lemma 2.5, and the corrected
parametric Case II theorem proved in `PI56-INDEPENDENT-PROOF.md` and
`ROUND-2-LI-THEOREM-AUDIT.md` give the following **fixed-instance contract**.
This proof invokes no trichotomy for arbitrary parameters.

Use exactly

\[
a=\frac{1123}{10000},\quad
r_\lambda=\frac{581}{2500},\quad
r_0=\frac{2453}{5000},\quad
p=\frac{83301}{100000},\quad
\lambda=\frac{2582}{3783}.
\]

Define \(d,R_1,\rho\) by the formulas in Section 4.  The exact checks in
Sections 2 and 4 establish every numerical domain fact used by the reduction:

\[
\frac3{20}\leq r_0<\frac12,
\quad 0<a<r_\lambda<r_0,
\quad 0<p,\lambda<1,
\quad \lambda a+(1-\lambda)r_0=r_\lambda,
\]

\[
Q:=4r_\lambda^2(1+a^2)-a^2,
\quad 0\leq Q<1,
\quad 0<d<\frac a2,
\quad 0\leq r_\lambda^2-d^2,
\quad 1-2\sqrt{r_\lambda^2-d^2}>0,
\quad \rho>\max\left\{\frac12,a\right\},
\quad \frac1\rho<R_1.
\]

For this instance only, put

\[
H=\frac{a}{2\pi},
\]

\[
A=p\left(1-\frac{f(r_0)}{2r_0^2}\right)
\int_a^{r_0}\frac{r}{g(r)}\,dr+\frac{f(r_0)}4,
\]

\[
B=\frac{1-p}{4}
\frac{a}{2\arcsin(a/\rho)}.
\]

Here the first displayed product in \(A\) means

\[
A=
p\left(1-\frac{f(r_0)}{2r_0^2}\right)
\left(\int_a^{r_0}\frac{r}{g(r)}\,dr\right)
+\frac{f(r_0)}4.
\]

Thus the notation is unambiguous: the factor multiplying the integral is
\(p(1-f(r_0)/(2r_0^2))\).  The fixed-instance contract says that at least one
of the following three inequalities holds:

\[
\frac{\mathcal L_2^*(E)}{\pi}\geq H,\qquad
\frac{\mathcal L_2^*(E)}{\pi}\geq A,\qquad\text{or}\qquad
\frac{\mathcal L_2^*(E)}{\pi}\geq B.
\]

The alternatives are respectively: a triangle of height at least \(a\);
at least \(p\pi\) confined directions, to which the factor-\(3\)-free
cross-section bound and Lemma 2.5 apply; or at least \((1-p)\pi\) exterior
directions, to which the corrected full-triangle Case II theorem applies.
The endpoint-containment and outer-measure statements are cited paper lemmas.
They are deliberately not fields of the Lean arithmetic domain certificate
`StrongParameterDomain`; they are proved in their own Lean modules and combined
by `universal_strong_lower_bound`.

## 2. Exact parameters

Take

\[
a=\frac{1123}{10000},\qquad
r_\lambda=\frac{581}{2500},\qquad
r_0=\frac{2453}{5000},\qquad
p=\frac{83301}{100000},
\]

and

\[
\lambda=\frac{2582}{3783}.
\]

Exact reduction gives

\[
\lambda a+(1-\lambda)r_0=r_\lambda,
\qquad
0<a<r_\lambda<r_0<\frac12,
\qquad
0<\lambda,p<1.
\]

Moreover,

\[
k:=1-\frac{f(r_0)}{2r_0^2}
=\frac{12262791}{12265000}.
\]

## 3. Piecewise control of \(g\)

Write

\[
b_1(r)=\frac{1+2r}{1-2r},\qquad
b_2=\frac{1+2r_\lambda}{1-2r_\lambda}
=\frac{1831}{669},
\]

\[
b_3(r)=\frac{\pi}{\pi/2-\arctan(2r)}.
\]

Set

\[
L=\frac{2249}{10000},\qquad
U=\frac{2354}{10000}.
\]

The exact alternating-series bounds for \(\arctan\), together with the
rational enclosure

\[
\frac{314159265358979323846}{10^{20}}
<\pi<
\frac{314159265358979323847}{10^{20}},
\]

give

\[
b_3(L)<b_2,\qquad b_3(U)<b_1(U).
\]

Since \(b_1\) and \(b_3\) are increasing,

\[
g(r)=\max\{b_1(r),b_2,b_3(r)\}
\leq
\begin{cases}
b_2,&a\leq r\leq L,\\
b_1(U),&L\leq r\leq U.
\end{cases}
\]

For \(x=2r\), the remaining comparison \(b_1(r)\geq b_3(r)\) is equivalent
to

\[
F(x):=\frac{\pi(3x-1)}2-(1+x)\arctan x\geq0.
\]

On the relevant interval \(0\leq x<1\),

\[
F'(x)
=\frac{3\pi}{2}-\arctan x-\frac{1+x}{1+x^2}
>\frac{5\pi}{4}-\frac32>0.
\]

The exact endpoint certificate gives \(F(2U)>0\).  Hence

\[
g(r)=b_1(r)\qquad(U\leq r\leq r_0).
\]

It follows that

\[
I:=\int_a^{r_0}\frac r{g(r)}\,dr
\geq I_L+I_M+I_R,
\]

where

\[
I_L=\frac{L^2-a^2}{2b_2},\qquad
I_M=\frac{U^2-L^2}{2b_1(U)},
\]

and

\[
I_R=
\left[-\frac{r^2}{2}+r-\frac12\log(1+2r)\right]_{U}^{r_0}.
\]

For

\[
z=\frac{638}{4315},
\]

the positive series for
\(\log((1+z)/(1-z))\) gives

\[
\log\frac{1+z}{1-z}
\leq
2z+\frac{2z^3}{3}+\frac{2z^5}{5}
+\frac{2z^7}{1-z^2}.
\]

Substitution yields the exact lower bound

\[
I\geq
\frac{22793357350571006116275623711763}
{1064174925446566790615478200000000}.
\]

Consequently,

\[
A-\frac{100}{5599}\geq
\frac{139158989937085958631189100903645702101397}
{664352167944649011863150962260700000000000000000}
>0.
\]

Replacing the positive-series tail by the deliberately weaker seven-term
alternating expression changes this margin to

\[
-\frac{102307073124674754126774830746397279660372227033}
{14543104472264293417969377841271107700000000000000000}<0.
\]

Thus the Case I certificate has a nontrivial negative control.

## 4. Exterior-direction case

Define \(d,R_1,\rho\) from \(a,r_\lambda\) as in the general reduction:

\[
d=
\frac{a\left(1-\sqrt{4r_\lambda^2(1+a^2)-a^2}\right)}
{2(1+a^2)},
\]

\[
R_1=
\frac{\sqrt{1+4d^2}}
{1-2\sqrt{r_\lambda^2-d^2}},
\qquad
\rho=R_1-1.
\]

Signed rational square comparisons give

\[
\frac{302738}{10^7}<d<\frac{302739}{10^7},
\qquad
R_1>\frac{185813}{100000}.
\]

In particular,

\[
\rho>\frac12,\qquad \rho>a.
\]

Monotonicity of \(\arcsin\) gives

\[
\arcsin(a/\rho)
<
\arcsin\left(\frac{11230}{85813}\right).
\]

The identity

\[
(\arcsin x-x)'
=
\frac{x^2}
{\sqrt{1-x^2}\left(1+\sqrt{1-x^2}\right)}
\]

and the exact square bound

\[
\left(\frac{9914}{10000}\right)^2
<
1-\left(\frac{11230}{85813}\right)^2
\]

give the rational upper estimate used below.  Exact reduction then yields

\[
\frac{(1-p)a}{8(100/5599)}
-\arcsin(a/\rho)
>
\frac{227923075074420651443585972857}
{74854501574905182351967200000000000}
>0.
\]

Therefore

\[
B=\frac{(1-p)a}{8\arcsin(a/\rho)}
>\frac{100}{5599}.
\]

## 5. Height case and conclusion

The same rational upper bound on \(\pi\) gives

\[
H-\frac{100}{5599}
>
\frac{22458464102067615300}
{1758977726744925234219353}
>0.
\]

All three branches of the trichotomy are therefore strictly larger than
\(100/5599\).  Multiplying by \(\pi\) proves the theorem.

## 6. Reproducibility and formalization boundary

The exact arithmetic is independently reproduced by
`50-computation/verify_pi56_stronger_candidate.py`, whose symbolic review,
sign guards, displayed-fraction anchors, and mutation gates pass.  The
independent Arb fixed witness in
`50-computation/interval_pi56_raw_family.py` gives a separate, slightly weaker
coefficient lower bound

\[
0.017866278155401827>\frac{100}{5599}.
\]

The Lean module `StarKakeyaLower/StrongerKernel.lean` formalizes the exact
parameters, the strict comparison \(100/5599>1/56\), both rational margins,
the height margin, and the failing mutation without placeholders or custom
axioms.  The quotient-circle geometry, projective separation, outer-measure
selection, and the universal theorem assembly are formalized as well, in
`QuotientCircle`, `PolarProjectiveOuter`, `CaseIAssemblyConditional`,
`UniversalEndpointClosure` and `UniversalAssembly`; the top-level result is

```lean
theorem StarKakeyaLower.universal_strong_lower_bound :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (Real.pi * 100 / 5599) < volume.toOuterMeasure E
```

with axiom footprint `propext, Classical.choice, Quot.sound`.
