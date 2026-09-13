# The exact finite-schedule variational constant

Date: 2026-08-03

## 1. Purpose

The rational bounds `1717/25000`, `7/100`, and `141/2000` are explicit
certified witnesses.  They are not the exact output of the finite radial-schedule
mechanism.  This note defines that output as a variational constant.

No irrationality or transcendence claim is made.  An implicit variational
characterisation is an exact mathematical definition even when no elementary
closed form is known.

## 2. Admissible finite schedules

For `N>=1`, an admissible schedule is

\[
\sigma=(N,\eta,\alpha_0,\ldots,\alpha_N,
              R_0,\ldots,R_{N-1},t_0,\ldots,t_N)
\]

satisfying:

1. \(0<\eta<1/2\);
2. \(0=\alpha_0<\alpha_1<\cdots<\alpha_N=\eta\);
3. \(R_0=1/2\), the radii are nondecreasing, and
   \[
   R_j^2\le\frac14+\alpha_j^2\qquad(1\le j<N);
   \]
4. the radial switches satisfy
   \[
   t_0=\alpha_1,
   \qquad
   t_0<t_1<\cdots<t_N,
   \qquad
   t_{j+1}\le R_j\quad(0\le j<N);
   \]
5. the first long window begins above every low-class cap,
   \[
   t_1\ge\eta;
   \]
6. the low schedule ends before the first high ledger,
   \[
   t_N\le\eta+\frac12.
   \]

The low closest-radius classes are

\[
L_0=\{0\le m\le\alpha_1\},
\qquad
L_j=\{\alpha_j<m\le\alpha_{j+1}\}\quad(1\le j<N).
\]

The radial interval \([t_j,t_{j+1})\) uses window radius \(R_j\).
All data are real; rational data are merely convenient for explicit certificates.

Let \(\mathscr S_N\) be this finite-dimensional feasible set and
\(\mathscr S=\bigcup_{N\ge1}\mathscr S_N\).

## 3. Payments

For \(0\le x\le y\le R\), put

\[
F_R(x,y)=\int_x^y u\frac{R-u}{R+u}\,du.
\]

Its elementary primitive is

\[
-\frac{u^2}{2}+2Ru-2R^2\log(R+u).
\]

A direction in class \(L_j\) is fully eligible for the first window from
\(u=\alpha_{j+1}\) to \(t_1\), and for windows \(1,\ldots,j\) on their full
radial intervals.  Define

\[
P_j(\sigma)
=
F_{R_0}(\alpha_{j+1},t_1)
+
\sum_{i=1}^{j}F_{R_i}(t_i,t_{i+1}),
\qquad 0\le j<N. \tag{1}
\]

For the high closest-radius classes, let

\[
A_k=\eta+\frac{k}{2},
\qquad
B_k=A_k+\frac12,
\]

\[
R_\eta(a)
=
\sqrt{a^2+1+2\sqrt{a^2-\eta^2}},
\qquad a\ge\eta,
\]

and the corresponding direction classes are

\[
S_k=\{\theta:A_k<m_\theta\le B_k\}.
\]

Define

\[
H_k(\eta)
=
F_{R_\eta(A_k)}(B_k,R_\eta(A_k)),
\qquad
H(\eta)=\inf_{k\ge0}H_k(\eta). \tag{2}
\]

The exact value delivered by one schedule is

\[
\Phi(\sigma)
=
\min\left\{
\frac\eta2,
\ \pi\min_{0\le j<N}P_j(\sigma),
\ \pi H(\eta)
\right\}. \tag{3}
\]

## 4. Exact variational constant

Define

\[
C_N=\sup_{\sigma\in\mathscr S_N}\Phi(\sigma),
\qquad
\boxed{C_{\rm FS}=\sup_{N\ge1}C_N
      =\sup_{\sigma\in\mathscr S}\Phi(\sigma).} \tag{4}
\]

This is the exact finite-schedule variational constant.  The definition contains
only finite-dimensional schedule data, elementary integrals, and the explicit
high-tail infimum.  It does not refer to a selector and is not self-referential.

For each fixed partition, the inner optimisation over radii and switches is
solved exactly by Theorem W in `FIXED-PARTITION-WATERFILLING.md`: radii may be
raised to their geometric caps, and a monotone one-dimensional water-level
frontier computes the global switch max--min.  In the free regime this frontier
coincides with the unique backward equal-payment schedule; active/pooling
regimes are handled by the same frontier without a uniqueness claim.

## 5. Universal theorem

> **Theorem V.** Every star-shaped Kakeya set satisfies
> \[
> \mathcal L^{2*}(E)\ge C_{\rm FS}.
> \]
> Consequently the universal infimum \(A_*\) obeys
> \[
> A_*\ge C_{\rm FS}.
> \]

**Proof.** Fix an arbitrary \(\sigma\in\mathscr S_N\).

If \(\sup h\ge\eta\), then for every \(\varepsilon>0\) some selected needle
has height greater than \(\eta-\varepsilon\).  Its origin triangle gives area
at least \((\eta-\varepsilon)/2\); letting \(\varepsilon\downarrow0\) yields
\(\eta/2\).  This also covers a non-attained or infinite supremum.

Assume every \(h<\eta\).  For \(L_j\), the geometry

\[
M^2\ge m^2+\frac14
\]

and the radius constraints imply \(M\ge R_i\) for every \(i\le j\).  Cut the
low radial schedule at its finitely many switches and class upper endpoints.
On each resulting radial atom the union of fully eligible classes is fixed.
Theorem A, radial integration, and the finite Lovasz--Choquet covering lemma
therefore give

\[
\operatorname{LowPay}
\ge
\left(\min_jP_j(\sigma)\right)
\left|\bigcup_{j=0}^{N-1}L_j\right|^*.
\]

No direction class is assumed measurable; only a finite simple payment function
is used.

For \(m>\eta\), the half-unit classes \((A_k,B_k]\) use the disjoint ledgers
\([B_k,R_\eta(A_k)]\).  Exact foot-outside geometry gives their eligibility, and

\[
\operatorname{HighPay}
\ge
H(\eta)\sum_{k\ge0}|S_k|^*.
\]

The low schedule ends no later than \(B_0=\eta+1/2\), so low and high ledgers are
radially disjoint.  The classes cover the projective circle, hence

\[
\pi
\le
\left|\bigcup_jL_j\right|^*
+
\sum_{k\ge0}|S_k|^*.
\]

Layer-cake assembly yields

\[
\mathcal L^{2*}(E)\ge\Phi(\sigma).
\]

This holds for every finite admissible \(\sigma\).  Taking the supremum over
\(\mathscr S\) proves Theorem V. \(\square\)

The proof uses no continuum family of arbitrary direction sections and no
selector pushforward or Fubini theorem.

## 6. Certified witnesses and numerical estimate

The current exact certificate proves

\[
C_{\rm FS}\ge\frac{141}{2000}=0.0705.
\]

Earlier certified witnesses give `7/100`, `1717/25000`, and `1/15`.
These rational numbers are useful audit artefacts, not proposed closed forms for
\(C_{\rm FS}\).

Floating-point finite-dimensional local optimisation gives the following
stationary candidate values:

\[
\begin{array}{c|c}
N&\widehat C_N^{\rm loc}\\ \hline
8&0.070382176463101\\
16&0.070477177302338\\
32&0.070522751353567\\
48&0.070537622521368\\
64&0.070544992619664
\end{array}
\]

These values are not certified global optima for the nonconvex finite problems.
A formal continuum-limit calculation defines a separate numerical candidate,
which we denote by

\[
C_{\rm BVP}^{\rm num}\approx0.0705668.
\]

The formal analysis suggests that \(C_{\rm FS}\) may be approximated by
\(C_{\rm BVP}^{\rm num}\), but this identification is not proved.  The displayed
decimal is neither a validated enclosure nor an error-bounded approximation of
\(C_{\rm FS}\).  What is rigorously established is the variational definition
(4), Theorem V, and the certified lower witness `141/2000`.  Identifying (4)
with the proposed ODE boundary-value limit still requires compactness, a limsup
inequality, and a recovery sequence.  A narrow certified decimal interval also
requires global upper bounds for the finite-dimensional problems and a
discretisation-error theorem.

## 7. Formal implicit characterisation of the continuum candidate

The formal equal-payment limit uses

\[
K(u,R)=u\frac{R-u}{R+u},
\qquad
R(x)=\sqrt{\frac14+x^2}.
\]

The candidate is characterised by a boundary-value system

\[
T'(x)=\frac{K(x,1/2)}{K(T(x),R(x))},
\qquad
T(\eta)=R(\eta),
\]

combined with

\[
\int_0^{T(0)}K(u,1/2)\,du=\frac{\eta}{2\pi}.
\]

Its floating-point shooting solution is

\[
\eta_{\rm BVP}\approx0.1411336,
\qquad
C_{\rm BVP}^{\rm num}=\eta_{\rm BVP}/2\approx0.0705668.
\]

The terminal condition is singular because \(K(T(\eta),R(\eta))=0\).  A
well-posedness and uniqueness theorem for the admissible singular branch has not
yet been supplied.  Accordingly, this system is a formal continuum candidate,
not an exact definition of \(C_{\rm FS}\) or a proved numerical approximation
to it.  No claim is made that the numerical candidate is irrational
or transcendental.

## Evidence boundary

- `C_FS` and Theorem V are exact paper-level statements.
- `141/2000` is an exact certified witness.
- The displayed higher-`N` local stationary candidates and BVP decimal are
  numerical scouting only.
- A validated local KKT root would not by itself prove a global optimum or an
  upper bound on `C_FS`.
- No Lean formalisation or peer-reviewed publication is claimed.
