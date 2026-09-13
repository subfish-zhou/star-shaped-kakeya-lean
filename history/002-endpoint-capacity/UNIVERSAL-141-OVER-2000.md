# Explicit 32-segment witness: C_FS at least 141/2000

Date: 2026-08-03

## Witness theorem

The schedule frozen below is admissible for the exact variational problem in
`FINITE-SCHEDULE-VARIATIONAL.md` and satisfies

\[
\boxed{C_{\rm FS}\ge\frac{141}{2000}=0.0705.}
\]

Consequently Theorem V implies the explicit numerical corollary
\(\mathcal L^{2*}(E)\ge141/2000\) for every star-shaped Kakeya set.  The
headline constant remains \(C_{\rm FS}\), not this rational witness.

No measurability, continuity, boundedness, or selector regularity is assumed.
This note refines the finite schedule proved in
`UNIVERSAL-SEVEN-HUNDREDTHS.md`; its finite outer-measure covering lemma is used
unchanged.

The exact improvement is

\[
\frac{141}{2000}-\frac7{100}=\frac1{2000}>0.
\]

## 1. Inputs retained from the finite-schedule theorem

For each selected unit needle write `m`, `M`, and `h` for its closest radius,
farthest radius, and supporting-line height.  The exact geometry gives

\[
M^2\ge m^2+\frac14,
\]

and each origin triangle has area `h/2`.  Theorem A supplies, for `0<r<R` and
`r'<r`,

\[
|\{\rho>r'\}|^*
\ge
|\{\theta:m_\theta\le r,\ M_\theta\ge R\}|^*
\frac{R-r}{R+r}.
\]

As in the previous proof, left limits remove the strict-level mismatch at only
countably many radial values.

We also reuse Lemma F: for finitely many arbitrary direction sets `B_i` and
weights `d_i>=0`, a pointwise simple payment

\[
\sum_i d_i1_{B_i}\ge c1_X
\]

implies

\[
\sum_i d_i|B_i|^*\ge c|X|^*.
\]

Its proof uses strong submodularity of Lebesgue outer measure and the finite
Lovasz--Choquet extension.  It does not use selector measurability or continuum
Fubini.

## 2. Height split and 32 low classes

Set

\[
\eta=\frac{141046}{10^6}.
\]

If `sup h >= eta`, the single-triangle branch gives

\[
\mathcal L^{2*}(E)\ge\frac\eta2
=\frac{70523}{10^6}
>\frac{141}{2000}.
\]

Assume every `h<eta`.  Partition `0<=m<=eta` into 32 classes

\[
L_0=\{\theta:0\le m_\theta\le b_0\},
\qquad
L_j=\{\theta:a_j<m_\theta\le b_j\}\quad(j\ge1),
\qquad a_j=b_{j-1}.
\]

Put

\[
L:=\bigcup_{j=0}^{31}L_j=\{\theta:m_\theta\le\eta\}.
\]

Use the following rational window
schedule; adjacent radial intervals are interpreted half-open and hence have
disjoint interiors.

| j | class upper b_j | window R_j | radial interval [t_j,t_{j+1}) |
|---:|---:|---:|---:|
| 0 | `27226/1000000` | `500000/1000000` | `[27226/1000000, 339842/1000000)` |
| 1 | `38590/1000000` | `500740/1000000` | `[339842/1000000, 344933/1000000)` |
| 2 | `47324/1000000` | `501486/1000000` | `[344933/1000000, 349939/1000000)` |
| 3 | `54682/1000000` | `502234/1000000` | `[349939/1000000, 354888/1000000)` |
| 4 | `61151/1000000` | `502981/1000000` | `[354888/1000000, 359794/1000000)` |
| 5 | `66981/1000000` | `503725/1000000` | `[359794/1000000, 364671/1000000)` |
| 6 | `72321/1000000` | `504466/1000000` | `[364671/1000000, 369526/1000000)` |
| 7 | `77266/1000000` | `505203/1000000` | `[369526/1000000, 374368/1000000)` |
| 8 | `81884/1000000` | `505934/1000000` | `[374368/1000000, 379204/1000000)` |
| 9 | `86225/1000000` | `506660/1000000` | `[379204/1000000, 384040/1000000)` |
| 10 | `90323/1000000` | `507380/1000000` | `[384040/1000000, 388883/1000000)` |
| 11 | `94208/1000000` | `508092/1000000` | `[388883/1000000, 393740/1000000)` |
| 12 | `97900/1000000` | `508797/1000000` | `[393740/1000000, 398615/1000000)` |
| 13 | `101419/1000000` | `509494/1000000` | `[398615/1000000, 403517/1000000)` |
| 14 | `104778/1000000` | `510182/1000000` | `[403517/1000000, 408452/1000000)` |
| 15 | `107987/1000000` | `510860/1000000` | `[408452/1000000, 413428/1000000)` |
| 16 | `111058/1000000` | `511528/1000000` | `[413428/1000000, 418453/1000000)` |
| 17 | `113996/1000000` | `512185/1000000` | `[418453/1000000, 423537/1000000)` |
| 18 | `116807/1000000` | `512830/1000000` | `[423537/1000000, 428690/1000000)` |
| 19 | `119496/1000000` | `513462/1000000` | `[428690/1000000, 433923/1000000)` |
| 20 | `122066/1000000` | `514081/1000000` | `[433923/1000000, 439251/1000000)` |
| 21 | `124519/1000000` | `514684/1000000` | `[439251/1000000, 444691/1000000)` |
| 22 | `126854/1000000` | `515271/1000000` | `[444691/1000000, 450264/1000000)` |
| 23 | `129071/1000000` | `515841/1000000` | `[450264/1000000, 455995/1000000)` |
| 24 | `131166/1000000` | `516390/1000000` | `[455995/1000000, 461917/1000000)` |
| 25 | `133135/1000000` | `516918/1000000` | `[461917/1000000, 468075/1000000)` |
| 26 | `134969/1000000` | `517421/1000000` | `[468075/1000000, 474531/1000000)` |
| 27 | `136656/1000000` | `517896/1000000` | `[474531/1000000, 481375/1000000)` |
| 28 | `138174/1000000` | `518338/1000000` | `[481375/1000000, 488752/1000000)` |
| 29 | `139487/1000000` | `518740/1000000` | `[488752/1000000, 496925/1000000)` |
| 30 | `140523/1000000` | `519092/1000000` | `[496925/1000000, 506472/1000000)` |
| 31 | `141046/1000000` | `519371/1000000` | `[506472/1000000, 519371/1000000)` |

The tables satisfy, by exact rational arithmetic,

\[
R_0=\frac12,
\qquad
R_j^2\le\frac14+a_j^2\quad(j\ge1),
\qquad
t_{j+1}\le R_j.
\]

Thus a direction in `L_j` is completely eligible for window `0` once
`u>=b_j`, and for every window `1,...,j` on its full radial interval.
At almost every radial level exactly one window is active.

## 3. Finite simple payment

Let

\[
F_R(x,y)=\int_x^y u\frac{R-u}{R+u}\,du.
\]

A direction in class `L_j` receives at least

\[
P_j=F_{R_0}(b_j,t_1)
+\sum_{i=1}^jF_{R_i}(t_i,t_{i+1}).
\]

Cutting the radial schedule additionally at all class upper endpoints makes the
eligible direction union constant on finitely many radial atoms.  Integrating
Theorem A on those atoms gives a finite simple payment, and Lemma F aggregates
it for arbitrary nonmeasurable classes.

The exact certificate proves all 32 inequalities

\[
P_j>c_*:=\frac{22447}{10^6}.
\]

The smallest certified rational margin is positive; numerically it exceeds
`9.89e-7`.

## 4. High closest-radius classes

For `k>=0`, put

\[
A_k=\eta+\frac{k}{2},
\qquad
B_k=A_k+\frac12,
\qquad
S_k=\{A_k<m\le B_k\},
\]

and

\[
R(a)=\sqrt{a^2+1+2\sqrt{a^2-\eta^2}}.
\]

Because `h<eta<m` on `S_k`, exact foot-outside geometry forces
`M>R(A_k)`.  Assign the pairwise-disjoint radial ledger

\[
[B_k,R(A_k)].
\]

The low schedule ends at `519371/10^6`, while the first high ledger starts at

\[
B_0=\eta+\frac12=\frac{641046}{10^6},
\]

so the low and high payments are radially disjoint.

For a uniform high-ledger bound, use

\[
R(\eta)>\frac{5049}{5000},
\qquad
R(\eta)-B_0>\frac{184377}{500000},
\]

and

\[
\frac{B_k}{R(A_k)+B_k}
>
\frac{A_k+1/2}{2A_k+3/2}
\ge\frac{320523}{891046}.
\]

Consequently every high coefficient is greater than

\[
\frac{320523}{891046}
\frac{(184377/500000)^2}{2}
=
\frac{10896140322541467}{445523000000000000}
>c_*.
\]

## 5. Assembly

The low classes and the countable high classes partition the projective circle,
so outer-measure subadditivity gives

\[
\pi\le|L|^*+\sum_{k\ge0}|S_k|^*.
\]

The finite low schedule and high ledgers are pairwise disjoint in radius.
Layer-cake integration and the two uniform coefficient bounds yield

\[
\mathcal L^{2*}(E)
\ge c_*\left(|L|^*+\sum_{k\ge0}|S_k|^*\right)
\ge c_*\pi.
\]

Finally, using `pi>333/106`,

\[
\frac{22447}{10^6}\pi
>
\frac{22447}{10^6}\frac{333}{106}
>
\frac{141}{2000};
\]

the exact last margin is `1851/106000000`.  Together with the height branch,
this proves the witness theorem.

## 6. Exact certificate

Run

```bash
python3 spikes/002-endpoint-capacity/certify_141_over_2000.py
```

The checker verifies all class boundaries, geometry margins, radial-budget
inequalities, 32 low payments, high-ledger lower bound, low--high separation,
height margin, pi margin, and the exact gain over `7/100`.  Each logarithm is
bounded above by three positive atanh-series terms plus a strict rational tail,
so every payment comparison is a Fraction decision.

## Evidence boundary

- This theorem uses the already-reviewed finite Lemma F and Theorem A.
- The 32-segment rational schedule was independently checked for radial budget,
  complete-class eligibility, finite outer-measure atoms, and high-tail cover.
- The certificate is exact rational arithmetic, not a proof assistant.
- No Lean formalization or peer-reviewed publication is claimed yet.
