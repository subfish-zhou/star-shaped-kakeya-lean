# Universal radial-sliver lower bound: \(\mathcal L^{2*}(E)\ge 1/15\)

Date: 2026-08-03
Scope: arbitrary star-shaped Kakeya sets; no measurability, continuity, boundedness, or selector regularity.

## Theorem

Let \(E\subset\mathbb R^2\) be star-shaped about \(O\) and contain a unit segment in every projective direction. Then

\[
\boxed{\mathcal L^{2*}(E)\ge \frac1{15}.}
\]

Consequently,

\[
\mathcal L^{2*}(E)>\frac{131\pi}{6250},
\]

because \(\pi<22/7\) gives

\[
\frac1{15}-\frac{131\pi}{6250}
>
\frac1{15}-\frac{131}{6250}\frac{22}{7}
=\frac{52}{65625}>0.
\]

The proof uses the radial-sliver covering theorem from `THEORY.md`, exact unit-chord geometry, and disjoint radial ledgers. It does not use the Li confined/escaping split.

## Inputs

Translate \(O\) to the origin. Choose one unit needle \(N_\theta\subset E\) in every projective direction \(\theta\in\mathbb T_\pi\). Define

\[
h_\theta=\operatorname{dist}(0,\operatorname{aff}N_\theta),\qquad
m_\theta=\min_{x\in N_\theta}|x|,\qquad
M_\theta=\max_{x\in N_\theta}|x|.
\]

Let \(\rho\) be the radial envelope of the selected full chords, and

\[
q(u)=\bigl|\{\phi\in S^1:\rho(\phi)>u\}\bigr|^*.
\]

The exact capacity identity gives

\[
\mathcal L^{2*}(E)\ge \operatorname{Cap}_2
\ge \int_0^\infty u q(u)\,du. \tag{1}
\]

We use the already independently reviewed radial-sliver theorem:

> For \(0<r<R\), \(r'<r\), and
> \[
> \Theta(r,R)=\{\theta:m_\theta\le r,\ M_\theta\ge R\},
> \]
> one has
> \[
> q(r')\ge |\Theta(r,R)|^*\frac{R-r}{R+r}. \tag{2}
> \]

For every unit chord,

\[
M_\theta^2\ge m_\theta^2+\frac14. \tag{3}
\]

If the perpendicular foot lies outside the segment, exact signed-line coordinates give

\[
M_\theta^2
=m_\theta^2+1+2\sqrt{m_\theta^2-h_\theta^2}. \tag{4}
\]

Finally, \(\operatorname{conv}(0,N_\theta)\subset E\) has area \(h_\theta/2\).

## 1. Height split

Set

\[
\eta=\frac2{15},\qquad H=\sup_\theta h_\theta.
\]

If \(H=+\infty\), then for every \(L>0\) some selected needle has height
larger than \(L\).  Its origin triangle has area larger than \(L/2\), so
\(\mathcal L^{2*}(E)=+\infty\) and the theorem is immediate.

Assume now that \(H<+\infty\).  If \(H\ge\eta\), then for every
\(\varepsilon>0\) some selected needle has height greater than
\(H-\varepsilon\). Its origin triangle lies in \(E\), hence

\[
\mathcal L^{2*}(E)\ge\frac{H-\varepsilon}{2}.
\]

Letting \(\varepsilon\downarrow0\) yields

\[
\mathcal L^{2*}(E)\ge\frac H2\ge\frac1{15}. \tag{5}
\]

It remains to treat \(H<\eta\), so every \(h_\theta<\eta\).

## 2. Direction classes

Define

\[
S_- = \{\theta:m_\theta\le\eta\}.
\]

For \(k\ge0\), put

\[
a_k=\eta+\frac{k}{2},\qquad
b_k=a_k+\frac12,
\]

and

\[
S_k=\{\theta:a_k<m_\theta\le b_k\}.
\]

These classes form a pointwise disjoint countable partition of \(\mathbb T_\pi\). No class is assumed measurable. Outer-measure subadditivity gives

\[
\pi
=|\mathbb T_\pi|^*
\le |S_-|^*+\sum_{k\ge0}|S_k|^*. \tag{6}
\]

For \(a\ge\eta\), define

\[
R(a)=\sqrt{a^2+1+2\sqrt{a^2-\eta^2}}. \tag{7}
\]

If \(\theta\in S_k\), then \(m_\theta>a_k>h_\theta\), so the perpendicular foot lies strictly outside the segment. By (4), monotonicity in \(m\), and antitonicity in \(h\),

\[
M_\theta>R(a_k). \tag{8}
\]

## 3. Disjoint radial ledgers

Use the radial intervals

\[
I_-=[\eta,1/2],\qquad
I_k=[b_k,R(a_k)]. \tag{9}
\]

They are nonempty and pairwise disjoint.

First,

\[
b_0=\eta+\frac12>\frac12,
\]

so \(I_-\cap I_0=\varnothing\).

Next, if \(a\ge\eta\), then

\[
R(a)<a+1, \tag{10}
\]

because \(\sqrt{a^2-\eta^2}<a\). Therefore

\[
R(a_k)<a_k+1=b_{k+1}, \tag{11}
\]

so consecutive high ledgers are separated.

For nonemptiness, let \(D(a)=R(a)-a\). For \(a>\eta\), writing \(s=\sqrt{a^2-\eta^2}\),

\[
R'(a)=\frac{a(1+1/s)}{R(a)}>1,
\]

since

\[
a^2(1+1/s)^2-R(a)^2
=\frac{2\eta^2}{s}+\frac{\eta^2}{s^2}>0.
\]

Thus \(D\) is increasing. At \(a_0=\eta\),

\[
R(a_0)=\frac{\sqrt{229}}{15}>\frac{121}{120},
\]

so

\[
R(a_0)-b_0>\frac38.
\]

Hence every \(I_k\) is nonempty, with width greater than \(3/8\).

## 4. Level-set payment on each ledger

### Low class

For \(u\in[\eta,1/2)\), take in (2)

\[
r'=u,\qquad r=u+\varepsilon,\qquad R=1/2.
\]

Every \(\theta\in S_-\) satisfies \(m_\theta\le\eta\le u<r\), while (3) gives \(M_\theta\ge1/2\). Letting \(\varepsilon\downarrow0\),

\[
q(u)\ge |S_-|^*\frac{1/2-u}{1/2+u}. \tag{12}
\]

Therefore

\[
\int_{I_-}u q(u)\,du\ge C_-|S_-|^*, \tag{13}
\]

where

\[
C_-:=\int_{2/15}^{1/2}u\frac{1/2-u}{1/2+u}\,du. \tag{14}
\]

### High classes

Fix \(k\ge0\) and write \(R_k=R(a_k)\). For \(u\in[b_k,R_k)\), take

\[
r'=u,\qquad r=u+\varepsilon,
\]

with \(0<\varepsilon<R_k-u\), and \(R=R_k\) in (2). Every \(\theta\in S_k\) has \(m_\theta\le b_k\le u<r\) and \(M_\theta>R_k\). Letting \(\varepsilon\downarrow0\),

\[
q(u)\ge |S_k|^*\frac{R_k-u}{R_k+u}. \tag{15}
\]

Thus

\[
\int_{I_k}u q(u)\,du\ge C_k|S_k|^*, \tag{16}
\]

where

\[
C_k:=\int_{b_k}^{R_k}u\frac{R_k-u}{R_k+u}\,du. \tag{17}
\]

Because the ledgers are pairwise disjoint Borel intervals, (1), (13), and (16) give

\[
\operatorname{Cap}_2
\ge C_-|S_-|^*+\sum_{k\ge0}C_k|S_k|^*. \tag{18}
\]

The angular contact images may overlap completely; this causes no double counting because different classes are charged on disjoint radial intervals.

## 5. Uniform coefficient certificate

The accompanying script `certify_one_fifteenth.py` checks every rational comparison below exactly.

### Low coefficient

The function

\[
f(u)=\frac{u}{1/2+u}
\]

is concave on \([2/15,1/2]\). On each of

\[
[2/15,19/60],\qquad[19/60,1/2],
\]

its endpoint chord is a lower bound. Multiplying by \(1/2-u\) and integrating the two rational linear functions gives

\[
C_-
\ge
\frac{12221}{837900}+\frac{605}{84672}
=\frac{873983}{40219200}. \tag{19}
\]

Moreover,

\[
\frac{873983}{40219200}>\frac{10}{471}>
\frac{106}{4995}>\frac1{15\pi}. \tag{20}
\]

The last inequality follows from the classical rational lower bound
\(\pi>333/106\); the intermediate comparison
\(10/471>106/4995\) is exact rational arithmetic.

### First high coefficient

For any \(b<R\),

\[
\int_b^R u\frac{R-u}{R+u}\,du
\ge \frac bR\frac{(R-b)^2}{4}. \tag{21}
\]

At \(k=0\),

\[
b_0=\frac{19}{30},\qquad R_0=\frac{\sqrt{229}}{15}.
\]

The exact comparisons

\[
R_0<\frac{101}{100},\qquad R_0>\frac{121}{120}
\]

give

\[
R_0-b_0>\frac38,
\qquad
\frac{b_0}{R_0}>\frac{190}{303}.
\]

Hence

\[
C_0>\frac{190}{303}\frac{(3/8)^2}{4}
=\frac{285}{12928}
>\frac{10}{471}
>\frac{106}{4995}
>\frac1{15\pi}. \tag{22}
\]

### Remaining high coefficients

For \(k\ge1\), monotonicity of \(D(a)=R(a)-a\) gives

\[
R_k-b_k>\frac38.
\]

Also, by (10),

\[
\frac{b_k}{R_k}
>
\frac{a_k+1/2}{a_k+1}
\ge\frac{34}{49}.
\]

Therefore

\[
C_k>\frac{34}{49}\frac{(3/8)^2}{4}
=\frac{153}{6272}
>\frac{10}{471}
>\frac{106}{4995}
>\frac1{15\pi}. \tag{23}
\]

Thus every coefficient in (18) is bounded below by the common rational number

\[
c_*:=\frac{10}{471}>\frac1{15\pi}. \tag{24}
\]

## 6. Assembly

If \(|S_-|^*+\sum_{k\ge0}|S_k|^*=+\infty\), apply (18) first to
finite partial sums and use \(C_-,C_k\ge c_*>0\).  The partial lower bounds
diverge, so \(\operatorname{Cap}_2=+\infty\), and the theorem is immediate.

Otherwise the sum of direction outer measures is finite.  Using (6), (18),
and (20)–(24),

\[
\begin{aligned}
\mathcal L^{2*}(E)
&\ge \operatorname{Cap}_2\\
&\ge C_-|S_-|^*+\sum_{k\ge0}C_k|S_k|^*\\
&\ge c_*
\left(|S_-|^*+\sum_{k\ge0}|S_k|^*\right)\\
&\ge c_*\pi\\
&>\frac1{15}.
\end{aligned}
\]

Together with the height branch, this proves the theorem.

## Evidence boundary

- The radial-sliver theorem used as (2) received an independent paper-level review with no BLOCK or IMPORTANT finding.
- The universal assembly received two independent reviews: one line-by-line proof audit and one adversarial boundary/random-geometry audit. Both returned PASS.
- `certify_one_fifteenth.py` is an exact arithmetic check of the frozen rational comparisons and a high-precision diagnostic of the analytic integrals. It is not a proof assistant.
- No Lean formalisation is claimed yet.
