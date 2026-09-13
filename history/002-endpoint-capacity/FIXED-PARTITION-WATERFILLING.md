# Exact waterfilling for a fixed finite-schedule partition

Date: 2026-08-03

## 1. Scope

This note solves the switch max--min problem inside one fixed low-radius
partition.  It does **not** identify the full variational constant `C_FS` with a
continuum BVP.

Fix

\[
0=\alpha_0<\alpha_1<\cdots<\alpha_N=\eta<\frac12,
\qquad
\rho_j=\sqrt{\frac14+\alpha_j^2}.
\]

Write

\[
K_R(u)=u\frac{R-u}{R+u},
\qquad
F_R(a,b)=\int_a^b K_R(u)\,du.
\]

For capped radii `R_j=rho_j`, define the closed switch polytope

\[
\overline{\mathcal T}
=
\left\{
\eta\le t_1\le\frac12,
\quad
t_j\le t_{j+1}\le\rho_j\ (1\le j<N)
\right\}.
\tag{1}
\]

The payments are

\[
P_0=F_{1/2}(\alpha_1,t_1),
\tag{2}
\]

\[
P_j
=
P_0+
\sum_{i=1}^j
\left[
F_{\rho_i}(t_i,t_{i+1})
-F_{1/2}(\alpha_i,\alpha_{i+1})
\right],
\qquad 1\le j<N.
\tag{3}
\]

Equation (3) is equivalent to the payment formula in
`FINITE-SCHEDULE-VARIATIONAL.md` by additivity of the first-window integral.

## 2. Dominating normalisations

For `0<u<R`,

\[
\partial_RK_R(u)=\frac{2u^2}{(R+u)^2}>0.
\tag{4}
\]

Hence increasing any legal window radius to its geometric cap `rho_j` cannot
decrease any payment.  Likewise, after capping the radii, increasing `t_N` to
`rho_(N-1)` changes only `P_(N-1)` and cannot decrease the minimum payment.
The terminal cap also remains below `eta+1/2`.

Thus a globally optimal representative can always be chosen with

\[
R_j=\rho_j,
\qquad
t_N=\rho_{N-1}.
\tag{5}
\]

This is a domination statement.  It does not say that every optimiser must use
all caps; active problems can have nonunique uncapped optimisers.

## 3. Forward water-level frontier

Fix a target water level `lambda`.

If

\[
\lambda>F_{1/2}(\alpha_1,1/2),
\]

the target is infeasible.  Otherwise define

\[
x_1(\lambda)
=
\min\left\{
x\in[\eta,1/2]:
F_{1/2}(\alpha_1,x)\ge\lambda
\right\}.
\tag{6}
\]

Suppose `x_1,...,x_j` have been defined.  Put

\[
G_j(y)
=
F_{1/2}(\alpha_{j+1},x_1)
+
\sum_{i=1}^{j-1}F_{\rho_i}(x_i,x_{i+1})
+
F_{\rho_j}(x_j,y),
\tag{7}
\]

for `y in [x_j,rho_j]`.  If the set is nonempty, define

\[
x_{j+1}(\lambda)
=
\min\left\{
y\in[x_j,\rho_j]:G_j(y)\ge\lambda
\right\}.
\tag{8}
\]

Otherwise the recursion fails.  Each `G_j` is continuous and strictly
increasing on its interval, although its derivative may vanish at the right
cap.

The recursion automatically handles:

- a free step, where `x_j<x_(j+1)<rho_j` and `G_j=lambda`;
- pooling, where `x_(j+1)=x_j` and `G_j(x_j)>=lambda`;
- an active cap, where `x_(j+1)=rho_j`.

## 4. Frontier theorem

> **Theorem W (fixed-partition waterfilling).**
> There exists `t in overline(T)` satisfying
> \[
> P_j(t)\ge\lambda\qquad(0\le j<N)
> \]
> if and only if the recursion (6)--(8) completes through `x_N(lambda)`.
> Whenever it completes, `x(lambda)` itself is feasible, and every feasible
> `t` satisfies
> \[
> t_i\ge x_i(\lambda)\qquad(1\le i\le N).
> \tag{9}
> \]

### Proof

For `j>=1`, direct differentiation gives

\[
\frac{\partial P_j}{\partial t_1}
=K_{1/2}(t_1)-K_{\rho_1}(t_1)<0,
\tag{10}
\]

and, for `2<=i<=j`,

\[
\frac{\partial P_j}{\partial t_i}
=K_{\rho_{i-1}}(t_i)-K_{\rho_i}(t_i)<0.
\tag{11}
\]

Also

\[
\frac{\partial P_j}{\partial t_{j+1}}
=K_{\rho_j}(t_{j+1})\ge0,
\tag{12}
\]

and the corresponding integral is strictly increasing in `t_(j+1)`.

The inequality `P_0(t)>=lambda` forces `t_1>=x_1`.  Inductively, assume
`t_i>=x_i` for `i<=j`.  Equations (10)--(11) imply

\[
P_j(t_1,\ldots,t_j;t_{j+1})
\le
P_j(x_1,\ldots,x_j;t_{j+1}).
\]

Thus `P_j(t)>=lambda` forces `t_(j+1)>=x_(j+1)`.  This proves (9).
Conversely, substituting the recursively minimal frontier verifies every
payment inequality.  The recursion therefore completes exactly at the feasible
water levels.  \(\square\)

It follows that

\[
\Lambda
=
\max\left\{
\lambda:x(\lambda)\text{ completes}
\right\}
\tag{13}
\]

is the exact closed-polytope max--min value.  The vector `x(Lambda)` is the
unique coordinatewise-minimal optimal frontier.  Numerically, (13) is a
one-dimensional bisection with monotone scalar root solves, not a nonconvex
multi-start optimisation.

## 5. Free backward equalisation

Start from

\[
t_N^*=\rho_{N-1}
\]

and solve backwards

\[
F_{\rho_j}(t_j^*,t_{j+1}^*)
=
F_{1/2}(\alpha_j,\alpha_{j+1}),
\qquad j=N-1,\ldots,1.
\tag{14}
\]

Suppose every root exists uniquely and the resulting switches satisfy

\[
\eta\le t_1^*\le\frac12,
\qquad
t_j^*<t_{j+1}^*\le\rho_j.
\tag{15}
\]

Then (14) gives

\[
P_0(t^*)=\cdots=P_{N-1}(t^*)=:\lambda^*.
\tag{16}
\]

> **Corollary W1 (free backward regime).** Under (15), `t*` is the unique global
> switch optimiser for capped radii.

Indeed, any schedule with all payments at least `lambda*` must lie
coordinatewise above the minimal frontier `t*`.  But its terminal coordinate is
at most `rho_(N-1)=t_N*`.  Hence the terminal coordinates agree.  Since
`P_(N-1)` is strictly decreasing in every preceding switch, any earlier strict
increase would force `P_(N-1)<lambda*`.  All coordinates therefore agree.

When (14) is infeasible, one must use Theorem W.  Pooling or an active cap can
produce many original optimisers even though the canonical frontier remains
unique.

## 6. Strict schedules and `N=1`

The strict switch set is dense in (1).  For example, choose a fixed strict point

\[
s_i=\eta+\frac{i}{N+1}\left(\frac12-\eta\right),
\]

and approximate any closed feasible `x` by

\[
x^{(\varepsilon)}=(1-\varepsilon)x+\varepsilon s.
\]

Payment continuity gives

\[
\sup_{\text{strict schedules}}\min_jP_j
=
\max_{\overline{\mathcal T}}\min_jP_j.
\tag{17}
\]

The strict supremum need not be attained when the frontier pools or hits a
boundary.

For `N=1`, the only payment is

\[
P_0(t_1)=F_{1/2}(\eta,t_1),
\]

so the unique switch optimum is `t_1=1/2`.

## 7. Active nonuniqueness

Caps are not necessary conditions for every optimiser.  For example, with

\[
N=2,\qquad \alpha_1=0.4,\qquad\eta=0.47,
\]

`P_0` is maximised at `t_1=1/2`.  Once `t_2` is large enough that
`P_1>=P_0`, an interval of terminal values gives the same global max--min.
The backward terminal-cap equation is infeasible in this example.  This is why
Theorem W distinguishes domination, the canonical frontier, and uniqueness in
the free regime.

## 8. Evidence boundary

- Theorem W is an exact finite-dimensional theorem.
- Independent brute-force comparisons for 600 random partitions with
  `N=2,3,4,5` found no discrepancy between the frontier value and direct SLSQP;
  the maximum absolute difference was about `2.71e-9`.
- This theorem does not prove that partition refinement is monotone, that
  near-optimal meshes converge to zero, or that `C_FS` equals the formal BVP
  candidate.
- No Lean formalisation or peer-reviewed publication is claimed.
