# Round 4: strict raw-family constant

Provider: `[Codex]`  
Date: 2026-07-31  
Evidence type: `analytic-proof` plus `symbolic-proof` for the fixed rational
kernel.

Final verdict: `proved-draft` after a fresh-context adversarial audit.  The
self-contained proof addendum is `STRONGER-100-OVER-5599-PROOF.md`.

## Candidate

The exact parameters are

\[
(a,r_\lambda,r_0,p,\lambda)=\left(\frac{1123}{10000},\frac{581}{2500},\frac{2453}{5000},\frac{83301}{100000},\frac{2582}{3783}\right).
\]

The target constant is (100/5599=0.01786033220217896\ldots), strictly above
(1/56).  This is a raw-family candidate in the corrected domain
\(0<a\le r_\lambda\le r_0<1/2\), with the separate geometric audit still
requiring \(\rho>1/2\).

## Exact certificate kernel

The branch switches are enclosed by

\[
\frac{2249}{10000}<r_{23}<\frac{2354}{10000},
\]

and the positive-series logarithm bound gives

\[
I\ge
\frac{22793357350571006116275623711763}
{1064174925446566790615478200000000}.
\]

The exact positive margins over (100/5599) are:

\[
M_{\rm I}=
\frac{139158989937085958631189100903645702101397}
{664352167944649011863150962260700000000000000000} >0,
\]

\[
M_{\rm II}=
\frac{227923075074420651443585972857}
{74854501574905182351967200000000000}>0,
\qquad
M_H=\frac{22458464102067615300}{1758977726744925234219353}>0.
\]

The radical/R1 envelope uses (d\in[302738/10^7,302739/10^7]),
\(R_1>185813/100000\), and hence the arcsin rational upper bound has the
strict Case-II margin above.  All signs and identities are checked by
`verify_pi56_stronger_candidate.py`.

## Teeth and scope

Replacing the positive-series log tail by the seven-term alternating bound
produces the exact negative mutation margin

\[
-\frac{102307073124674754126774830746397279660372227033}
{14543104472264293417969377841271107700000000000000000000}<0.
\]

Thus the certificate has a nontrivial negative control.  The analytic
remainder, branch monotonicity, and measure-theoretic assembly are discharged
in `STRONGER-100-OVER-5599-PROOF.md` using the frozen Round-2 framework.  No
global optimization claim is made.  The dedicated JSON record is
`50-computation/results/stronger-candidate-100-over-5599.json`.
