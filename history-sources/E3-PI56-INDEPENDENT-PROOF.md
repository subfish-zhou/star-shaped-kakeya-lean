# An independent \(\pi/56\) lower-bound proof for star-shaped Kakeya sets

Provider: `[Codex]`

Status: `proved-draft` on paper; Lean formalization is incomplete.

Date: 2026-07-31

## Theorem

Let \(E\subset\mathbb R^2\) be a star-shaped Kakeya set: there is a point
\(O\in E\) such that \([O,x]\subset E\) for every \(x\in E\), and \(E\)
contains a unit segment in every unoriented direction.  Then

\[
\mathcal L_2^*(E)\geqslant\frac{\pi}{56}.
\]

Here \(\mathcal L_2^*\) is Lebesgue outer measure.  No measurability of \(E\)
is assumed.

The proof does not use Li Remark 4.1.

## 1. Setup

Translate the star centre to \(O=0\).  For every
\(\alpha\in\mathbb T_\pi=\mathbb R/\pi\mathbb Z\), choose a closed unit
segment \(l_\alpha\subset E\) of direction \(\alpha\), and put

\[
\Delta_\alpha=\operatorname{conv}(\{0\}\cup l_\alpha),
\qquad
\delta_\alpha=\operatorname{dist}(0,\operatorname{aff}l_\alpha).
\]

Star-shapedness gives

\[
\Delta_\alpha\subset E.
\]

Define

\[
E_{\rm all}
=
\bigcup_{\alpha\in[0,\pi)}\Delta_\alpha
\subset E.
\]

The fixed parameters are

\[
a=\frac{449}{4000},
\qquad
r_\lambda=\frac{13}{56},
\qquad
r_0=\frac{49}{100},
\qquad
p=\frac{333}{400},
\qquad
\lambda=\frac{7220}{10577}.
\]

Exact reduction gives

\[
r_\lambda=\lambda a+(1-\lambda)r_0.
\]

Put

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
\qquad
k=1-\frac{f(r_0)}{2r_0^2}
=\frac{4899}{4900},
\]

and

\[
g(r)=
\max\left\{
\frac{1+2r}{1-2r},
\frac{1+2r_\lambda}{1-2r_\lambda},
\frac{\pi}{\pi/2-\arctan(2r)}
\right\}.
\]

## 2. Same-centre dilation on a circle

Let \(\mathbb T_L=\mathbb R/L\mathbb Z\).  If \(I\) is a circle interval and
\(c\geq1\), let \(cI\) be its same-centre dilation, saturated to
\(\mathbb T_L\) when the nominal length reaches \(L\).

### Lemma 2.1

If \(I\subset C\), then

\[
cI\subset cC.
\]

### Proof

If \(cC=\mathbb T_L\), the assertion is immediate.  Otherwise lift \(C\) to
a real interval of length \(s<L\) and lift \(I\) inside it.  If the lengths
and centres are \(\ell,m\) and \(s,M\), inclusion gives

\[
|m-M|\leqslant\frac{s-\ell}{2}.
\]

For \(x\in cI\),

\[
|x-M|
\leqslant
\frac{c\ell}{2}+\frac{s-\ell}{2}
\leqslant
\frac{cs}{2}.
\]

Thus \(x\in cC\).  If \(cI\) is saturated, then \(cC\) is saturated because
\(\ell\leq s\).  This also covers intervals crossing the chosen cut.

### Lemma 2.2

For an arbitrary, possibly uncountable, family of circle intervals
\(\{I_j\}_{j\in J}\),

\[
m_L^*\left(\bigcup_{j\in J}cI_j\right)
\leqslant
c\,m_L^*\left(\bigcup_{j\in J}I_j\right).
\]

### Proof

Put \(U=\bigcup_jI_j\).  If \(m_L^*(U)=L\), the conclusion is immediate.
Otherwise choose an open \(V\supset U\) with

\[
m_L(V)<m_L^*(U)+\varepsilon<L.
\]

The proper open set \(V\) is a disjoint union of at most countably many open
circle intervals \(C_n\).  Every connected \(I_j\) lies in one \(C_n\), so
Lemma 2.1 gives

\[
\bigcup_jcI_j\subset\bigcup_ncC_n.
\]

Consequently,

\[
m_L^*\left(\bigcup_jcI_j\right)
\leqslant
\sum_n|cC_n|
\leqslant
c\sum_n|C_n|
=
c\,m_L(V).
\]

Let \(\varepsilon\downarrow0\).

## 3. The correctly typed Li endpoint containment

Needle directions live in \(\mathbb T_\pi\), while polar angles on a circle
live in \(\mathbb T_{2\pi}\).  Let

\[
q:\mathbb T_{2\pi}\longrightarrow\mathbb T_\pi
\]

be reduction modulo \(\pi\).

Fix a triangle-circle arc \(\Gamma\subset S_r\), and rotate its polar-angle
interval to \([0,t]\).  Li's geometry gives \(0\leq t\leq\pi/2\).

In the first small-angle configuration, write

\[
s=\arcsin(\delta_0/r).
\]

The two endpoint directions satisfy

\[
\alpha_1=s,
\qquad
\alpha_1-\alpha_2=2s-t.
\]

Therefore

\[
\alpha_2=t-s,
\]

and the direction set is contained in

\[
[t-s,s],
\]

which is centred at \(t/2\).

In the bounded exterior-needle configuration, the endpoint calculation gives

\[
[t-S,S],
\qquad
S=\arcsin(R_1\sin t),
\]

again centred at \(t/2\).  Li's ratio estimates bound the lengths of these
containing intervals by \(g(r)t\).

If

\[
t\geqslant\frac{\pi}{2}-\arctan(2r),
\]

the third branch of \(g\) gives \(g(r)t\geq\pi\), so the same-centre
dilation saturates the direction circle.  Thus the actual statement used
later is

\[
J_\Gamma
\subset
D_{g(r)}^\pi(q(\theta_\Gamma)).
\]

This is stronger than the length-only statement printed as Li Lemma 3.2.

## 4. Factor-\(3\)-free cross-sections

Let

\[
A_{\rm in}
=
\{\alpha:\Delta_\alpha\subset B_{R_1}\}.
\]

Assume

\[
\mathcal L_1^*(A_{\rm in})\geqslant p\pi.
\]

For fixed \(r\in[a,r_0]\), let \(P_r\subset\mathbb T_{2\pi}\) be the union
of the polar-angle arcs in

\[
E_{\rm all}\cap S_r.
\]

For each \(\alpha\in A_{\rm in}\), the direction \(\alpha\) belongs to the
corresponding \(J_{\Gamma_{\alpha,1}}\).  The endpoint containment and
Lemma 2.2 give

\[
\begin{aligned}
p\pi
&\leqslant
m_\pi^*\left(
\bigcup_{\alpha\in A_{\rm in}}
J_{\Gamma_{\alpha,1}}
\right)\\
&\leqslant
g(r)\,m_\pi^*(q(P_r))\\
&\leqslant
g(r)\,m_{2\pi}^*(P_r).
\end{aligned}
\]

The final inequality follows because quotient projection does not increase
outer measure.  Radial parametrization is a similarity: angular distances are
multiplied by \(r\) (it is an isometry only after the angular metric is scaled
by \(r\)).  Hence

\[
\mathcal H_1^*(E_{\rm all}\cap S_r)
=
r\,m_{2\pi}^*(P_r).
\]

Therefore

\[
\mathcal H_1^*(E_{\rm all}\cap S_r)
\geqslant
\frac{p\pi r}{g(r)}.
\]

No Vitali selection is used.

## 5. Inner-outer aggregation

The following is the form of Li Lemma 2.5 needed here, with the stopping rule
at zero residual supremum made explicit.

### Lemma 5.1

Let \(A\subset[0,\pi)\), let

\[
E_A=\bigcup_{\alpha\in A}\Delta_\alpha,
\]

and suppose

\[
0.15\leq r\leq\frac12,
\qquad
0\leq h<r,
\qquad
0\leq\delta_\alpha\leq h\quad(\alpha\in A).
\]

If \(s_0\geq0\) and

\[
\mathcal L_2^*(E_A\cap B_r)\geqslant s_0,
\]

then

\[
\mathcal L_2^*(E_A)
\geqslant
\frac{\mathcal L_1^*(A)}4f(r)
+\left(
1-\frac{f(r)}{2r^2}
\right)s_0.
\]

### Proof

Write \(L=\mathcal L_1^*(A)\).  Fix
\(0<\varepsilon<1-h/r\), put \(m=1-\varepsilon\), and, when
\(\delta_\alpha>0\), let \(I_\alpha\) be the interval in
\(\mathbb T_\pi\) centred at \(\alpha\) with radius

\[
2\arcsin\frac{\delta_\alpha}{mr};
\]

put \(I_\alpha=\varnothing\) when \(\delta_\alpha=0\).  Thus

\[
|I_\alpha|=4\arcsin\frac{\delta_\alpha}{mr}.
\]

Starting with \(R_0=A\), apply the following rule.  If \(R_n=\varnothing\),
stop with a cover.  If \(R_n\ne\varnothing\) but
\(\sup_{R_n}\delta=0\), stop and retain \(R_n\) as a zero-height residual
set.  Otherwise choose \(\alpha_n\in R_n\) so that

\[
\delta_n>m\sup_{\alpha\in R_n}\delta_\alpha,
\qquad
R_{n+1}=R_n\setminus I_{\alpha_n}.
\]

The second stopping alternative is essential: when the residual supremum is
zero, the displayed strict greedy inequality has no solution, even though the
remaining set need not be empty.

For \(j<n\), \(\alpha_n\notin I_{\alpha_j}\) and the greedy inequality give

\[
d_\pi(\alpha_j,\alpha_n)
>
\arcsin(\delta_j/r)+\arcsin(\delta_n/r).
\]

Hence the exterior pieces
\(\Delta_{\alpha_n}^{\rm ext}=\mathring\Delta_{\alpha_n}\cap B_r^c\)
are pairwise disjoint (discarding their null boundary pieces if necessary).
Each is Borel measurable.  The elementary exterior-triangle estimate and

\[
\frac{\arcsin(mx)}{\arcsin x}
\geq\frac{2\arcsin m}{\pi}
\qquad(0\leq x\leq1)
\]

give, with

\[
C_\varepsilon=\frac{2\arcsin m}{\pi m},
\qquad
q_\varepsilon=\frac{C_\varepsilon f(r)}4,
\qquad
B=\sum_n|I_{\alpha_n}|,
\]

the bound

\[
\mathcal L_2\!\left(\bigcup_n\Delta_{\alpha_n}^{\rm ext}\right)
\geq q_\varepsilon B. \tag{5.1}
\]

If \(B=\infty\), (5.1) makes the conclusion immediate.  Assume henceforth
that \(B<\infty\).  If the process stops with an empty residual, the selected
intervals cover \(A\), so \(B\geq L\), and

\[
\mathcal L_2^*(E_A)\geq s_0+q_\varepsilon L. \tag{5.2}
\]

This is stronger than the estimate used below.

It remains to treat a zero-supremum stop or an infinite selection.  In the
finite zero-supremum case, nonnegativity of heights immediately gives
\(\delta_\alpha=0\) on the residual set.  In the infinite case, convergence
of \(B\) implies

\[
\arcsin\frac{\delta_n}{mr}\longrightarrow0,
\qquad\text{hence}\qquad \delta_n\longrightarrow0.
\]

Let

\[
A_0=A\setminus\bigcup_n I_{\alpha_n}.
\]

For every \(\alpha\in A_0\) and every \(n\), one has
\(\alpha\in R_n\), and therefore the greedy rule gives

\[
0\leq m\delta_\alpha
\leq m\sup_{R_n}\delta
<\delta_n.
\]

Letting \(n\to\infty\) proves \(\delta_\alpha=0\).  This is the complete
``residual supremum is zero'' argument; it does not silently assume that the
greedy choice exists at supremum zero.  Outer subadditivity gives

\[
\mathcal L_1^*(A_0)\geq L-B. \tag{5.3}
\]

A zero-height base segment passes through the origin, so its triangle contains
a radial segment of length \(r\).  Li Lemma A.1 and (5.3) give a residual fan
\(F\subset E_A\cap B_r\) with

\[
\mathcal L_2^*(F)\geq\frac{r^2}{2}(L-B). \tag{5.4}
\]

Put \(U=\bigcup_n\Delta_{\alpha_n}^{\rm ext}\).  This is a countable union of
Borel sets, hence is measurable, and \(U\subset E_A\setminus B_r\).  Applying
the Carathéodory identity to the measurable separator \(U\), not to \(E_A\),
gives

\[
\mathcal L_2^*(E_A)
=\mathcal L_2(U)+\mathcal L_2^*(E_A\setminus U).
\]

Because \(E_A\cap B_r\subset E_A\setminus U\), (5.1) and the hypothesis give

\[
M:=\mathcal L_2^*(E_A)\geq s_0+q_\varepsilon B. \tag{5.5}
\]

Because also \(F\subset E_A\cap B_r\subset E_A\setminus U\), (5.1) and
(5.4) give

\[
M\geq q_\varepsilon B+\frac{r^2}{2}(L-B). \tag{5.6}
\]

The same two inequalities hold after a finite zero-supremum stop, with finite
sums.  Since \(0\leq q_\varepsilon\leq r^2/2\), splitting according as
\(B\geq L-2s_0/r^2\) or \(B\leq L-2s_0/r^2\) and using (5.5) or (5.6),
respectively, gives

\[
M\geq q_\varepsilon L+
\left(1-\frac{2q_\varepsilon}{r^2}\right)s_0. \tag{5.7}
\]

(The case \(L-2s_0/r^2<0\) is covered directly by (5.5).)  Finally
\(C_\varepsilon\to1\) as \(\varepsilon\downarrow0\).  Taking the supremum of
(5.7) over such \(\varepsilon\) proves

\[
M\geq\frac{Lf(r)}4+
\left(1-\frac{f(r)}{2r^2}\right)s_0.
\]

This proof uses only measurable selected exterior pieces in the additive
step; no measurability of \(A\) or \(E_A\) is assumed.

Apply polar outer-measure slicing to the cross-section estimate in Section 4:

\[
\mathcal L_2^*(E_{\rm all}\cap B_{r_0})
\geqslant
p\pi\int_a^{r_0}\frac r{g(r)}\,dr.
\]

Lemma 5.1 with \(A=[0,\pi)\) gives

\[
\frac{\mathcal L_2^*(E)}{\pi}
\geqslant
pkI+\frac{f(r_0)}4,
\qquad
I=\int_a^{r_0}\frac r{g(r)}\,dr.
\]

The use of \(E_{\rm all}\), rather than merely the larger set \(E\), is
essential here.

## 6. A parametric exterior-needle theorem

### Lemma 6.1

Let \(A\subset\mathbb T_\pi\) be arbitrary.  For every \(\alpha\in A\), let
\(l_\alpha\subset\mathbb R^2\setminus B_\rho\) be a closed unit segment of
direction \(\alpha\).  Suppose \(\rho>1/2\) and

\[
\delta_\alpha
=
\operatorname{dist}(0,\operatorname{aff}l_\alpha)
<a<\rho,
\]

and put

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
\frac{\mathcal L_1^*(A)}4
\frac{a}{2\arcsin(a/\rho)}.
\]

### Proof

Write

\[
c=\frac{a}{2\arcsin(a/\rho)}.
\]

First, complete triangles at sufficiently separated directions have
disjoint interiors.  Indeed, if

\[
P\in\mathring\Delta_1\cap\mathring\Delta_2,
\]

the ray \(OP\) meets the relative interior of each base \(l_i\) at
\(K_i=t_iP\), \(t_i>1\).  If \(\beta\) is the projective direction of this
ray, then \(|K_i|>\rho\): equality would make \(K_i\) a local distance
minimum on its supporting line and force \(\delta_i=\rho\).  Hence

\[
\sin d_\pi(\alpha_i,\beta)
=
\frac{\delta_i}{|K_i|}
<
\frac{\delta_i}{\rho}.
\]

Therefore

\[
d_\pi(\alpha_1,\alpha_2)
<
\arcsin(\delta_1/\rho)+\arcsin(\delta_2/\rho).
\]

Fix

\[
0<\varepsilon<1-\frac a\rho,
\qquad
m=1-\varepsilon,
\qquad
\kappa_\varepsilon=\frac{2\arcsin m}{\pi}.
\]

For a positive height define

\[
H_\alpha
=
\arcsin\left(\frac{\delta_\alpha}{m\rho}\right).
\]

The ratio \(x/\arcsin(x/\rho)\) decreases on \((0,\rho)\).  Also the
function \(u\mapsto\arcsin(m\sin u)\) is concave on \([0,\pi/2]\), so its
endpoint chord gives

\[
\frac{\delta_\alpha}{2}
\geqslant
c\arcsin(\delta_\alpha/\rho)
\geqslant
c\kappa_\varepsilon H_\alpha.
\]

Let \(I_\alpha\subset\mathbb T_\pi\) be the saturated interval centred at
\(\alpha\) with radius \(2H_\alpha\).  Its length is at most
\(4H_\alpha\).  Greedily choose from the remaining direction set an
\(\alpha_n\) such that

\[
\delta_n>m\sup\delta
\]

and delete \(I_n\).  If \(j<n\), then

\[
d_\pi(\alpha_j,\alpha_n)
\geqslant
2H_j
>
\arcsin(\delta_j/\rho)+\arcsin(\delta_n/\rho).
\]

The selected complete triangles have pairwise disjoint interiors.

Put

\[
B_\varepsilon=\sum_n4H_n,
\qquad
b_\varepsilon=\frac{c\kappa_\varepsilon}{4}B_\varepsilon.
\]

If \(B_\varepsilon=\infty\), the selected disjoint triangles have infinite
total area.  Otherwise \(H_n\to0\), hence \(\delta_n\to0\), and the greedy
rule forces every residual direction in

\[
A_0=A\setminus\bigcup_nI_n
\]

to have height zero.  Outer subadditivity gives

\[
\mathcal L_1^*(A_0)
\geqslant
\mathcal L_1^*(A)-B_\varepsilon.
\]

Each residual height-zero triangle contains a radial segment from \(0\) to
radius \(\rho\).  Choosing the corresponding oriented angles
\(\Theta\subset\mathbb T_{2\pi}\), the quotient map sends \(\Theta\) onto
\(A_0\), so

\[
m_{2\pi}^*(\Theta)\geqslant m_\pi^*(A_0).
\]

The residual radial fan \(F\) therefore satisfies

\[
\mathcal L_2^*(F)
\geqslant
\frac{\rho^2}{2}
\left(
\mathcal L_1^*(A)-B_\varepsilon
\right).
\]

The residual rays avoid the interiors of all selected triangles: an
intersection with the \(n\)-th triangle would force angular distance below
\(\arcsin(\delta_n/\rho)<H_n\), whereas the ray direction lies outside
\(I_n\).

Let \(M\) be the outer measure of the full triangle union and
\(L=\mathcal L_1^*(A)\).  The selected interior union is measurable and
disjoint from \(F\), so

\[
M\geqslant b_\varepsilon
\]

and

\[
M
\geqslant
b_\varepsilon
+\frac{\rho^2}{2}
\left(
L-\frac{4b_\varepsilon}{c\kappa_\varepsilon}
\right).
\]

Define

\[
\mu_\varepsilon
=
1-\frac{2\rho^2}{c\kappa_\varepsilon}.
\]

Since \(\arcsin(a/\rho)>a/\rho\),

\[
c<\frac\rho2.
\]

In the application below \(\rho>1/2\), so
\(\mu_\varepsilon<0\).  Using \(b_\varepsilon\leq M\),

\[
M
\geqslant
\frac{\rho^2}{2}L+\mu_\varepsilon b_\varepsilon
\geqslant
\frac{\rho^2}{2}L+\mu_\varepsilon M.
\]

Exact coefficient elimination gives

\[
M\geqslant\frac{c\kappa_\varepsilon}{4}L.
\]

Let \(\varepsilon\downarrow0\).  Then
\(\kappa_\varepsilon\uparrow1\), proving the lemma.

## 7. Exact Case I certificate

Put

\[
L=\frac{2241}{10000},
\qquad
U=\frac{2353}{10000},
\qquad
G_0=\frac{41}{15},
\qquad
G_1=\frac{1+2U}{1-2U}.
\]

For \(x\in[0,1)\), let \(y=(1-x)/(1+x)\).  The identity

\[
\arctan x=\frac\pi4-\arctan y
\]

and the alternating series for \(\arctan y\) give exact rational upper
bounds for \(\arctan x\).

At \(r=L\), the exact positive residual for

\[
G_0\left(\frac\pi2-\arctan(2L)\right)-\pi
\]

is

\[
\frac{
100284965253947086936934600310433341007409821951525568978989949
}{
477230837113020912408896462144833071541942851120000000000000000000
}>0.
\]

At \(r=U\), put

\[
F(x)=\frac{\pi(3x-1)}2-(1+x)\arctan x.
\]

The exact lower residual for \(F(2U)\) is

\[
\frac{
504250282431683226482768084357747171935584541198233407836001
}{
71148603557791633928864157411547679895546000000000000000000000000
}>0.
\]

Moreover,

\[
F'(x)
=
\frac{3\pi}{2}-\arctan x-\frac{1+x}{1+x^2}
>2
\]

for \(0\leq x<1\), using \(\pi>3\), \(\arctan x<1\), and

\[
\frac{1+x}{1+x^2}\leqslant\frac32.
\]

Monotonicity of the three branches therefore gives the certified lower bound

\[
\begin{aligned}
I
\geqslant{}&
\frac{L^2-a^2}{2G_0}
+\frac{U^2-L^2}{2G_1}\\
&+\left[
-\frac{r^2}{2}+r-\frac12\log(1+2r)
\right]_{r=U}^{r=r_0}.
\end{aligned}
\]

The logarithmic ratio is

\[
\frac{1+2r_0}{1+2U}=1+\frac{283}{817}.
\]

With

\[
z=\frac{283}{1917},
\]

the positive log series gives

\[
\log\left(1+\frac{283}{817}\right)
\leqslant
2z+\frac{2z^3}{3}+\frac{2z^5}{5}
+\frac{2z^7}{1-z^2}.
\]

The resulting exact integral lower bound is

\[
I\geqslant
\frac{
163512203344334226603335030071
}{
7631310947411192372575200000000
}.
\]

Exact reduction now gives

\[
pkI+\frac{f(r_0)}4-\frac1{56}
\geqslant
\frac{
9903508366951835577422590421
}{
7802487979617077230176000000000000
}>0.
\]

## 8. Exact Case II certificate

Let

\[
Q=4r_\lambda^2(1+a^2)-a^2.
\]

Exact arithmetic gives

\[
Q=\frac{516003077}{2508800000}\in(0,1)
\]

and

\[
r_\lambda^2-\left(\frac a2\right)^2-\frac1{36}
=
\frac{648093959}{28224000000}>0.
\]

Thus \(0<d<a/2\) and

\[
\rho=R_1-1>\frac12.
\]

The sharper rational enclosures are

\[
\frac{302897}{10^7}<d<\frac{302898}{10^7},
\qquad
R_1>\frac{18563}{10000},
\]

which imply

\[
\frac a\rho<\frac{2245}{17126}.
\]

The relevant exact square residual is

\[
1-\left(\frac{2245}{17126}\right)^2
-\left(\frac{99}{100}\right)^2
=
\frac{1991606331}{733249690000}>0.
\]

Using

\[
\arcsin x
=
\int_0^x\frac{dt}{\sqrt{1-t^2}}
\]

and

\[
\frac1{\sqrt{1-t^2}}-1
=
\frac{t^2}
{\sqrt{1-t^2}(1+\sqrt{1-t^2})},
\]

one obtains

\[
\arcsin\left(\frac{2245}{17126}\right)
<
\frac{2245}{17126}
+\frac{(2245/17126)^3}
{3(99/100)(199/100)}.
\]

The exact remaining margin below

\[
7(1-p)a=\frac{210581}{1600000}
\]

is

\[
\frac{
8595227380165644121
}{
59375508286970145600000
}>0.
\]

Therefore

\[
\arcsin(a/\rho)<7(1-p)a.
\]

If

\[
A_{\rm out}
=
\{\alpha:\Delta_\alpha\not\subset B_{R_1}\},
\]

then every \(l_\alpha\) with \(\alpha\in A_{\rm out}\) lies outside
\(B_\rho\): one point has radius at least \(R_1\), and every other point of
the unit segment has radius at least \(R_1-1\).

When

\[
\mathcal L_1^*(A_{\rm in})<p\pi,
\]

outer subadditivity gives

\[
\mathcal L_1^*(A_{\rm out})\geqslant(1-p)\pi.
\]

Lemma 6.1 yields

\[
\frac{\mathcal L_2^*(E)}{\pi}
\geqslant
\frac{1-p}{4}
\frac{a}{2\arcsin(a/\rho)}
>
\frac1{56}.
\]

## 9. The height branch and final assembly

If some \(\delta_\alpha\geq a\), then

\[
\mathcal L_2^*(E)
\geqslant
|\Delta_\alpha|
\geqslant
\frac a2.
\]

The exact rational comparison

\[
28a-\frac{22}{7}=\frac1{7000}>0
\]

together with \(\pi<22/7\) gives

\[
\frac a2>\frac{\pi}{56}.
\]

Assume now that every height is below \(a\).  Either

\[
\mathcal L_1^*(A_{\rm in})\geqslant p\pi,
\]

in which case Sections 4, 5, and 7 give the target, or the strict opposite
holds, in which case Sections 6 and 8 give the target.  These cases are
exhaustive, so

\[
\mathcal L_2^*(E)\geqslant\frac{\pi}{56}.
\]

## 10. Verification boundary

The exact arithmetic and minimax reductions are reproduced by:

- `50-computation/verify_pi56_noniterative_kernel.py`;
- `50-computation/verify_pi56_parametric_caseii_kernel.py`.

The logarithmic inequality and its exact Case I margin are also compiled in
`StarKakeyaLower.AnalyticKernel`.

The paper proof has undergone an independent fresh-context audit.  It is not
yet a completed Lean theorem, peer-reviewed publication, or theorem-library
entry.
