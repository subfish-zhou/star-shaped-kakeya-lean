# Round 1 audit: removing the factor \(3\) and a non-iterative \(\pi/56\) certificate

Provider: `[Codex]`

## Round-two correction

`ROUND-2-LI-THEOREM-AUDIT.md` supersedes the Case II source-scope verdict and
the list of remaining bridges below.  Direct citation of Li Theorem 3.5 at
the current \(\rho>1/2\) is invalid, but a new projective-angle,
weighted-selection, and radial-fan proof supplies the required parametric
theorem.  The universal paper proof is now `proved-draft`; the required Lean
universal theorem remains open.

## Verdict at this checkpoint

- Universal \(\pi/56\) verdict: `conditional`.
- Exact arithmetic verdict: `symbolic-proof`.
- Circle-dilation lemma: complete proof below and fresh-context adversarial
  audit confirmed.
- Li same-centre geometry and the mod-\(\pi\) projection: complete coordinate
  reconstruction below and fresh-context adversarial audit confirmed.
- Li Remark 4.1 iteration: not accepted.  The stated rescaling step has a
  direction-scope gap.
- Dependence on Remark 4.1: eliminated by the non-iterative candidate in
  Section 6 below.
- Lean: the fixed-rational kernels and positive-series logarithm theorem have
  been written; the remaining analytic and measure layers remain open.

No final theorem is registered at this checkpoint.

The independent audit was read-only and used no script or numerical evidence.
It checked the local Li v2 PDF with SHA-256
`294b1f852bea222b4331d78fbe2a55617367f40e3b9e9da4737ba284448c87c8`.
It confirmed wrap-around, saturation, arbitrary family cardinality, both
endpoint configurations, the large-angle branch, degenerate arcs, the
quotient map, and the full outer-measure chain.  It also supplied four
negative controls: the result fails if one drops same-centre containment,
keeps only a length inequality, allows \(c<1\), or incorrectly asks a
length-\(\pi\) dilation to saturate \(\mathbb T_{2\pi}\).

## 1. Circle dilation for an arbitrary interval family

Let \(\mathbb T_L=\mathbb R/L\mathbb Z\).  A circle interval \(I\) has length
\(\ell(I)\in[0,L]\) and a centre.  For \(c\geqslant1\), its same-centre
dilation \(cI\) has length \(\min(c\ell(I),L)\).

### Containment lemma

If \(I\subset C\), then

\[
cI\subset cC.
\]

When \(cC=\mathbb T_L\), this is immediate.  Otherwise choose the unique lift
of the proper interval \(C\) to a real interval of length \(s<L\), and lift
\(I\) inside it.  Let their lengths be \(\ell\leqslant s\) and their centres
be \(m,M\).  Inclusion gives

\[
|m-M|\leqslant\frac{s-\ell}{2}.
\]

For a point in the lifted \(cI\),

\[
|x-M|
\leqslant
\frac{c\ell}{2}+\frac{s-\ell}{2}
\leqslant
\frac{cs}{2},
\]

because \(c\geqslant1\).  This proves the containment, including wrapped
intervals after quotienting by \(L\).  If \(cI\) is already saturated, then
\(cC\) is also saturated because \(s\geqslant\ell\).

### Outer-measure theorem

For an arbitrary, possibly uncountable, interval family \(\{I_j\}_{j\in J}\),

\[
m_L^*\left(\bigcup_{j\in J}cI_j\right)
\leqslant
c\,m_L^*\left(\bigcup_{j\in J}I_j\right).
\]

Write \(U=\bigcup_j I_j\).  If \(m_L^*(U)=L\), the result is trivial.  Otherwise
take an open \(V\supset U\) with

\[
m_L(V)<m_L^*(U)+\varepsilon<L.
\]

The proper open set \(V\) is the disjoint union of at most countably many open
circle intervals \(C_k\).  Each connected \(I_j\) is contained in one
component \(C_k\), hence \(cI_j\subset cC_k\).  Therefore

\[
m_L^*\left(\bigcup_jcI_j\right)
\leqslant
\sum_k m_L(cC_k)
\leqslant
c\sum_km_L(C_k)
=c\,m_L(V).
\]

Letting \(\varepsilon\downarrow0\) proves the theorem.  Uncountability of the
original family disappears only after outer regularity; no countable
subfamily is assumed.

## 2. The hidden same-centre statement in Li Section 3

Needle directions live in
\(\mathbb T_\pi=\mathbb R/\pi\mathbb Z\).  Polar arc angles live in
\(\mathbb T_{2\pi}\).  Let

\[
q:\mathbb T_{2\pi}\longrightarrow\mathbb T_\pi
\]

be reduction modulo \(\pi\).  Li proves that every relevant central-angle arc
has length \(t\leqslant\pi/2\), so \(q\) is injective and length preserving on
each individual arc.

Rotate a fixed arc so that its polar-angle lift is \([0,t]\).  In Li's first
small-angle case, put

\[
s=\arcsin(\delta_0/r).
\]

The paper gives

\[
\alpha_1=s,
\qquad
|\alpha_1-\alpha_2|=2s-t.
\]

Since \(\alpha_2<\alpha_1\), this forces

\[
\alpha_2=t-s.
\]

Thus the actual containing interval is

\[
J_\Gamma\subset[t-s,s],
\]

whose centre is \(t/2\), exactly the centre of \(q([0,t])\).

In the bounded exterior-needle subcase, Li obtains

\[
S=\arcsin(R_1\sin t)
\]

and

\[
J_\Gamma\subset[t-S,S].
\]

This interval also has centre \(t/2\).  If both subcases occur, their union is
contained in the larger of two intervals with the same centre.

Li's ratio estimates bound the length of these intervals by \(g(r)t\).  Hence,
in the small-angle cases, they imply the stronger statement

\[
J_\Gamma\subset g(r)\,q(\theta_\Gamma)
\]

as a same-centre dilation on \(\mathbb T_\pi\).

In the large-angle case,

\[
t\geqslant\frac{\pi}{2}-\arctan(2r)
\]

and the third branch of \(g(r)\) gives \(g(r)t\geqslant\pi\).  The dilated
interval therefore saturates to all of \(\mathbb T_\pi\), so the same
containment is again valid.

The load-bearing correction is that Li's printed Lemma 3.2 states only a
length inequality.  The endpoint formulas in the preceding proof supply the
same-centre containment actually used later.

## 3. Why projection modulo \(\pi\) costs no extra factor

For an arbitrary polar-angle set \(A\subset\mathbb T_{2\pi}\),

\[
m_\pi^*(q(A))\leqslant m_{2\pi}^*(A).
\]

This follows by projecting interval covers; the quotient map preserves the
length of intervals shorter than \(\pi\) and can only identify points.

Put

\[
E_{\rm all}
=
\bigcup_{\alpha\in[0,\pi)}\Delta_\alpha
\subset E.
\]

Let \(A_r\) be the union of the polar central-angle arcs
\(\theta_{\alpha,i}\).  Radial parametrization of \(S_r\) gives

\[
r\,m_{2\pi}^*(A_r)
\leqslant
\mathcal H_1^*(E_{\rm all}\cap S_r).
\]

For the confined direction set \(\mathscr A\) of outer measure at least
\(p\pi\), the same-centre containment and the circle-dilation theorem give

\[
\begin{aligned}
p\pi
&\leqslant
m_\pi^*\left(\bigcup_{\alpha\in\mathscr A}
J_{\Gamma_{\alpha,1}}\right)\\
&\leqslant
m_\pi^*\left(\bigcup_{\alpha,i}g(r)\,q(\theta_{\alpha,i})\right)\\
&\leqslant
g(r)\,m_\pi^*\left(q(A_r)\right)\\
&\leqslant
g(r)\,m_{2\pi}^*(A_r)\\
&\leqslant
\frac{g(r)}{r}\mathcal H_1^*(E_{\rm all}\cap S_r).
\end{aligned}
\]

Therefore the proposed replacement for Li (3.11) is

\[
\mathcal H_1^*(E_{\rm all}\cap S_r)
\geqslant
\frac{p\pi r}{g(r)}.
\]

The quotient \(\mathbb T_{2\pi}\to\mathbb T_\pi\) reduces measure; it does not
introduce a multiplicity \(2\).

## 4. Audit of the proposed iterative candidate

Li's Case I assumption controls only a direction set

\[
\mathscr A
=\{\alpha:\Delta_\alpha\subset B_{R_1}\}
\]

of outer measure at least \(p\pi\).  The global Case I expression contains the
full-direction baseline term \(\pi f(r_0)/4\), obtained by applying Lemma 2.5
to all directions.

The statement

\[
\mathcal L_2^*(E\cap B_a)
\geqslant
\left(\frac a{R_1}\right)^2
\left[
p\pi kI+\frac{\pi f(r_0)}4
\right]
\]

does not follow from the displayed Case I hypothesis by direct rescaling:
only the triangles with directions in \(\mathscr A\) are known to lie in
\(B_{R_1}\).  Applying Lemma 2.5 to that confined family gives the baseline
\(p\pi f(r_0)/4\), not \(\pi f(r_0)/4\).

This is a `theorem-strength` gap in the direct justification of Remark 4.1,
not an exact counterexample to the resulting numerical constant.  A valid
repair would have to construct a full-direction Kakeya configuration inside
\(B_{R_1}\), or derive a different scale recurrence with the correct
direction measure.

The first parameter set in the user draft needs the iterative denominator:
without it, its Case I coefficient is approximately
\(0.0178204469\), below \(1/56\).  It is therefore not used for the current
non-iterative proof route.

## 5. Non-iterative parameter set

Use

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

Exact arithmetic gives

\[
r_\lambda=\lambda a+(1-\lambda)r_0.
\]

Put

\[
L=\frac{2241}{10000},
\qquad
U=\frac{2353}{10000},
\qquad
G_0=\frac{1+2r_\lambda}{1-2r_\lambda}=\frac{41}{15}.
\]

These rational radii replace numerical root finding.

For \(x\in[0,1)\), set \(y=(1-x)/(1+x)\).  The identity

\[
\arctan x=\frac{\pi}{4}-\arctan y
\]

and the lower alternating partial sum

\[
y-\frac{y^3}{3}+\frac{y^5}{5}-\frac{y^7}{7}
+\frac{y^9}{9}-\frac{y^{11}}{11}
<\arctan y
\]

are combined with Mathlib's rigorous decimal bounds

\[
\frac{314159265358979323846}{10^{20}}
<\pi<
\frac{314159265358979323847}{10^{20}}.
\]

At \(L\), cross multiplication gives the exact positive residual

\[
\frac{
100284965253947086936934600310433341007409821951525568978989949
}{
477230837113020912408896462144833071541942851120000000000000000000
}>0,
\]

which proves that the third branch is below \(G_0\).

At \(U\), the lower bound for

\[
F(x)=\frac{\pi(3x-1)}2-(1+x)\arctan x
\]

has exact positive residual

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
=\frac{3\pi}{2}-\arctan x-\frac{1+x}{1+x^2}>2
\]

for \(0\leqslant x<1\), using \(\pi>3\),
\(\arctan x<1\), and

\[
\frac{1+x}{1+x^2}\leqslant\frac32.
\]

Consequently the rational branch dominates from \(U\) to \(r_0\).

On the middle interval \([L,U]\), all three branches are bounded above by

\[
G_1=\frac{1+2U}{1-2U}.
\]

Thus no transcendental root occurs in the certificate.

## 6. Exact non-iterative Case I

The certified integral lower bound is

\[
\begin{aligned}
I_{\rm lb}
={}&
\frac{L^2-a^2}{2G_0}
+\frac{U^2-L^2}{2G_1}\\
&+\left[
-\frac{r^2}{2}+r-\frac12\log(1+2r)
\right]_{r=U}^{r=r_0},
\end{aligned}
\]

where the last logarithm is bounded by the nine-term alternating upper sum
with

\[
\frac{1+2r_0}{1+2U}-1=\frac{283}{817}.
\]

The resulting exact rational lower bound is

\[
I_{\rm lb}
=
\frac{
2393594915164504298667197428312219853
}{
111709895934537651989183224893600000000
}.
\]

With \(k=4899/4900\), exact reduction gives

\[
p\,k\,I_{\rm lb}+\frac{f(r_0)}4-\frac1{56}
=
\frac{
116569153710187543639191405603945643017
}{
72983798677231265966266373597152000000000000
}>0.
\]

The negative control replaces the nine-term log upper bound by the seven-term
upper bound.  It gives

\[
-\frac{
641269113124626808494726855865047
}{
109340826106844106743731168000000000000
}<0.
\]

The Lean analytic layer uses the positive series for
\(\log(1+x)\) with \(z=283/1917\) and a geometric tail.  It gives the
independent exact margin

\[
\frac{
9903508366951835577422590421
}{
7802487979617077230176000000000000
}>0.
\]

## 7. Exact non-iterative Case II

Define

\[
d=
\frac{
a\left(1-\sqrt{4r_\lambda^2+4a^2r_\lambda^2-a^2}\right)
}{
2(1+a^2)
},
\qquad
R_1=
\frac{\sqrt{1+4d^2}}
{1-2\sqrt{r_\lambda^2-d^2}}.
\]

Square comparisons give

\[
\frac{302897}{10^7}<d<\frac{302898}{10^7}.
\]

The literal positive square residuals are

\[
\frac{
2068927724139165489041
}{
3951379600000000000000000000
}>0,
\]

\[
\frac{
1099333053906887342751
}{
987844900000000000000000000
}>0.
\]

The numerator and denominator envelopes for \(R_1\) have residuals

\[
\frac{14097323}{3125000000000}>0,
\qquad
\frac{22730591}{612500000000000}>0.
\]

They imply

\[
R_1>\frac{18563}{10000},
\]

with final quotient residual

\[
\frac{408333}{13492090000}>0.
\]

Hence

\[
\frac{a}{R_1-1}<\frac{2245}{17126}.
\]

The square-root estimate

\[
1-\left(\frac{2245}{17126}\right)^2
-\left(\frac{99}{100}\right)^2
=
\frac{1991606331}{733249690000}>0
\]

and the integral identity for \(\arcsin\) give

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

This proves the strict finite Case II comparison with \(1/56\).  It does not
by itself justify the printed Theorem 3.5 outside its source scope.  Round 2
supplies a new parametric geometric theorem for the present \(\rho>1/2\).

## 8. Height case

Mathlib proves \(\pi<3.1416\).  The simpler rational comparison

\[
28a-\frac{22}{7}=\frac1{7000}>0
\]

and \(\pi<22/7\) give

\[
\frac a2>\frac{\pi}{56}.
\]

This height comparison is already compiled in Lean.

## 9. Remaining bridges

The exact certificate no longer depends on Li Remark 4.1.  Round 2 closes the
paper-level Lemma 2.5 and Case II bridges.  The remaining mandatory work is
Lean: the atan/radical/arcsin and integral links, circle outer measure, Li
endpoint geometry, parametric Case II selection/fan theorem, and final
universal assembly.
