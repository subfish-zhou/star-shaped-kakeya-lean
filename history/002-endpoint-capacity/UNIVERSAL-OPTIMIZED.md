# Intermediate optimized radial-sliver bound: area at least 1717/25000

Date: 2026-08-03

**Status:** superseded as the current headline by the exact variational theorem
`FINITE-SCHEDULE-VARIATIONAL.md`.  The 32-segment schedule in
`UNIVERSAL-141-OVER-2000.md` certifies the witness `C_FS >= 141/2000`; the later
`7/100` witness in `UNIVERSAL-SEVEN-HUNDREDTHS.md` and this `1717/25000`
theorem remain independently certified intermediate results.

This note optimizes the rational height threshold in
`UNIVERSAL-ONE-FIFTEENTH.md`.  The geometric mechanism and all arbitrary-selector
outer-measure arguments are unchanged.

## Theorem

Every star-shaped Kakeya set `E` satisfies

\[
\boxed{\mathcal L^{2*}(E)\ge \frac{1717}{25000}=0.06868.}
\]

This is unconditional: no measurability, continuity, boundedness, or selector
regularity is assumed.

Using \(\pi<355/113\),

\[
\frac{1717}{25000}-\frac{131\pi}{6250}
>
\frac{1717}{25000}-\frac{131}{6250}\frac{355}{113}
=
\frac{8001}{2825000}>0.
\]

Thus the theorem improves the previous \(131\pi/6250\) bound by more than

\[
\frac{8001}{186020}>4.30115\%.
\]

## 1. General radial-ledger assembly

The radial-sliver theorem proved in `THEORY.md` states that, for

\[
\Theta(r,R)=\{\theta:m_\theta\le r,\ M_\theta\ge R\},
\]

and \(r'<r<R\),

\[
|\{\phi:\rho(\phi)>r'\}|^*
\ge
|\Theta(r,R)|^*\frac{R-r}{R+r}. \tag{1}
\]

Fix any threshold \(0<\eta<1/2\).  If
\(H=\sup_\theta h_\theta\ge\eta\), the single-triangle argument gives

\[
\mathcal L^{2*}(E)\ge\frac\eta2. \tag{2}
\]

The cases \(H=+\infty\) and a non-attained finite supremum are handled exactly
as in `UNIVERSAL-ONE-FIFTEENTH.md`.

Assume henceforth that every \(h_\theta<\eta\).  Partition the projective
direction circle into

\[
S_-:=\{\theta:m_\theta\le\eta\},
\]

and, for \(k\ge0\),

\[
a_k=\eta+\frac{k}{2},\qquad
b_k=a_k+\frac12,
\qquad
S_k:=\{\theta:a_k<m_\theta\le b_k\}.
\]

For

\[
R(a)=\sqrt{a^2+1+2\sqrt{a^2-\eta^2}},
\]

use the radial ledgers

\[
I_-=[\eta,1/2],
\qquad
I_k=[b_k,R(a_k)].
\]

The exact unit-chord argument in the one-fifteenth proof gives

\[
\operatorname{Cap}_2
\ge
C_-(\eta)|S_-|^*+
\sum_{k\ge0}C_k(\eta)|S_k|^*, \tag{3}
\]

where

\[
C_-(\eta)=
\int_\eta^{1/2}u\frac{1/2-u}{1/2+u}\,du,
\]

and

\[
C_k(\eta)=
\int_{b_k}^{R(a_k)}u\frac{R(a_k)-u}{R(a_k)+u}\,du.
\]

The ledgers are pairwise disjoint: first
\(b_0=\eta+1/2>1/2\), so \(I_-\cap I_0=\varnothing\); and then
\(R(a)<a+1\) gives \(R(a_k)<b_{k+1}\) for every \(k\).  If the sum of
direction outer measures is infinite, finite partial sums in (3) force infinite
capacity.  Otherwise outer-measure subadditivity gives

\[
\pi\le |S_-|^*+\sum_{k\ge0}|S_k|^*. \tag{4}
\]

It therefore suffices to prove the uniform coefficient bounds

\[
C_-(\eta),C_0(\eta),C_1(\eta),\ldots
>
\frac{\eta}{2\pi}. \tag{5}
\]

## 2. Rational witness

Take

\[
\boxed{\eta=\frac{1717}{12500}.}
\]

Then the height branch (2) is exactly

\[
\frac\eta2=\frac{1717}{25000}. \tag{6}
\]

All rational identities and inequalities below are checked from their defining
expressions by `certify_optimized_radial_bound.py`.

## 3. Low ledger

The exact expression is

\[
C_-(\eta)
=
\frac38-\eta+\frac{\eta^2}{2}
-
\frac12\log\frac{2}{1+2\eta}. \tag{7}
\]

Set

\[
y=\frac{2}{1+2\eta}=\frac{12500}{7967},
\qquad
z=\frac{y-1}{y+1}=\frac{4533}{20467}.
\]

Since \(0<z<1\),

\[
\log y
=2\sum_{j\ge0}\frac{z^{2j+1}}{2j+1}
<
2\left(
 z+\frac{z^3}{3}+\frac{z^5}{5}
 +\frac{z^7}{7(1-z^2)}
\right)
=:U_{\log}. \tag{8}
\]

The last term bounds the complete positive tail beginning with \(z^7/7\).
Exact arithmetic gives

\[
U_{\log}
=
\frac{2255392730789667442828102686477}
{5007302326850532853032257075000}.
\]

Substitution in (7) yields

\[
C_-(\eta)>
B_-:=
\frac{1368465910852584744183198399925437}
{62591279085631660662903213437500000}. \tag{9}
\]

From \(\pi>333/106\),

\[
\frac{\eta}{2\pi}
<
\frac{53\eta}{333}
=
\frac{91001}{4162500}. \tag{10}
\]

The exact positive margin is

\[
B_--\frac{91001}{4162500}
=
\frac{29629268185379654216641093095521}
{20842895935515343000746770074687500000}>0. \tag{11}
\]

Hence \(C_-(\eta)>\eta/(2\pi)\).

## 4. First high ledger

At \(a_0=\eta\),

\[
R_0=\sqrt{1+\eta^2},
\qquad
b_0=\eta+\frac12.
\]

The exact rational enclosure

\[
\frac{50469}{50000}<R_0<\frac{100939}{100000}
\]

has squared margins

\[
R_0^2-\left(\frac{50469}{50000}\right)^2
=
\frac{49463}{2500000000}>0,
\]

and

\[
\left(\frac{100939}{100000}\right)^2-R_0^2
=
\frac{161}{400000000}>0.
\]

Therefore

\[
R_0-b_0>\frac{18601}{50000}=:w. \tag{12}
\]

For any \(b<R\),

\[
\int_b^R u\frac{R-u}{R+u}\,du
\ge
\frac{b}{R+b}\frac{(R-b)^2}{2}. \tag{13}
\]

Using (12) and the upper enclosure on \(R_0\),

\[
C_0(\eta)>
B_0:=
\frac{2756559700367}{102921875000000}. \tag{14}
\]

The exact margin over (10) is

\[
B_0-\frac{91001}{4162500}
=
\frac{168654896472211}{34272984375000000}>0. \tag{15}
\]

Thus \(C_0(\eta)>\eta/(2\pi)\).

## 5. All remaining ledgers

The function \(D(a)=R(a)-a\) is strictly increasing for \(a>\eta\), as proved
in the one-fifteenth note.  Consequently every high ledger has width greater
than the same \(w\) in (12).

For \(k\ge1\), \(R(a_k)<a_k+1\) and monotonicity of the rational factor give

\[
\frac{b_k}{R(a_k)+b_k}
>
\frac{a_k+1/2}{2a_k+3/2}
\ge
\frac{\eta+1}{2\eta+5/2}
=
\frac{14217}{34684}. \tag{16}
\]

Using (13),

\[
C_k(\eta)>
B_{\ge1}:=
\frac{4919042206617}{173420000000000}. \tag{17}
\]

Again the exact margin is positive:

\[
B_{\ge1}-\frac{91001}{4162500}
=
\frac{375529581203461}{57748860000000000}>0. \tag{18}
\]

Thus (5) holds for every ledger.

## 6. Assembly

Let

\[
c_*:=\frac{53\eta}{333}.
\]

Equations (9)--(18) show that every coefficient in (3) is greater than
\(c_*>\eta/(2\pi)\).  If the outer-measure sum in (4) is infinite, finite
partial sums force infinite capacity.  Otherwise,

\[
\begin{aligned}
\mathcal L^{2*}(E)
&\ge\operatorname{Cap}_2\\
&\ge C_-(\eta)|S_-|^*+\sum_{k\ge0}C_k(\eta)|S_k|^*\\
&\ge c_*\left(|S_-|^*+\sum_{k\ge0}|S_k|^*\right)\\
&\ge c_*\pi\\
&>\frac\eta2
=\frac{1717}{25000}.
\end{aligned}
\]

Together with the height branch, this proves the claimed non-strict universal
bound.

## Evidence boundary

- The geometric radial-sliver theorem and the general disjoint-ledger assembly
  were independently reviewed before this parameter optimization.
- `certify_optimized_radial_bound.py` derives and checks every frozen rational
  identity and margin above.  It is an exact arithmetic certificate, not a
  proof assistant.
- The numerical optimum of this fixed mechanism is approximately
  `0.06868430842034249`; the rational witness `0.06868` is below it by
  `4.30842034e-6`.
- No Lean formalization or peer-reviewed publication is claimed yet.
