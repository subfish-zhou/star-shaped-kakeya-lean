# A two-separator theorem for seven centered, common-height chords

## 1. Literal statement and scope

Let $J$ denote rotation by $\pi/2$. Choose seven unit vectors
$u_i=(\cos\theta_i,\sin\theta_i)$, considered as labelled directions on
$\mathbb {RP}^1=\mathbb R/\pi\mathbb Z$, and a common $0\le h\le1/5$.
Set
\[
v_i^\pm=\pm u_i/2+hJu_i,\qquad
T_i=\operatorname{conv}(0,v_i^-,v_i^+),\quad
B_i=T_i\cup(-T_i),\quad
P_i=\operatorname{conv}\{v_i^-,v_i^+,-v_i^-,-v_i^+\}.
\]
Write $S=|\bigcup_i B_i|$ and $H=|\bigcup_i P_i|$ for **physical union
areas**, not sums over labels. Reversing the orientation of $u_i$ does not
change these sets. The same statement therefore allows either sign of the
common height magnitude. Fix $\tau=1665/424$.

Sort the labelled directions in cyclic order, allowing collisions. Their
seven actual directed gaps are nonnegative and sum to $\pi$. Designate two
of these gaps $g_1,g_2$ and the other five $G_1,\ldots,G_5$. Assume
\[
q_j=\tan(g_j/2)\le2h,\qquad Q_i=\tan(G_i/2)\ge2h,
\tag{1}
\]
and assume **at least two distinct actual gaps have half-gap tangent at
least $3/7$**. These are among the five longs, since $2h\le2/5<3/7$.
All tangent coordinates here are nonnegative. In particular the separator
assumption bounds each gap away from $\pi$, so they are finite. The angle
closure is literal; an unguarded polynomial closure equation is not a
substitute. A directed gap larger than $\pi/2$ is not folded to its shorter
projective distance.

For $h>0$, put $\beta=\arctan(2h)$. Join consecutive centers across the
**designated** short gaps to form five collar blocks. A block $b$ has span
$s_b$, from its first to last center, and two incident boundary longs
$Q_{b,L},Q_{b,R}$. A singleton has span zero. Define
\[
\begin{aligned}
F(Q,h)&=h-2h^2/Q,\\
A(Q,h)&=\frac{h^3(1+Q^2)^2}{Q^2-h^2(Q^2-1)^2},\\
L(Q,h)&=(\tau-1)F(Q,h)+\tau A(Q,h)-h,\\
\delta(h,q)&=\frac{(2h-q)(1+q^2-4hq)}{2(1-q^2)},\\
E(Q;r,h)&=h^2[\cot(G+\beta)-\cot(G+2\arctan r+\beta)],
\quad G=2\arctan Q,\\
\mathcal E&=\sum_b\bigl(E(Q_{b,L};\tan(s_b/2),h)
                      +E(Q_{b,R};\tan(s_b/2),h)\bigr),\\
\Phi&=\sum_{i=1}^5 L(Q_i,h)+\frac\tau2\mathcal E
       +\delta(h,q_1)+\delta(h,q_2)-2h.
\end{aligned}\tag{2}
\]
The incidences in $\mathcal E$ are physical block incidences, not extra
copies of a long reserve. Pole guards for every expression are proved below.

**Theorem.** Under (1) and the two-separator assumption, if $h>0$, then
\[
\boxed{\quad \tau S-H\ge\Phi>
\frac{1012129}{15582000}h+\delta(h,q_1)+\delta(h,q_2)>0.\quad}
\tag{3}
\]
If $h=0$, then $S=H=0$; no strict inequality or divided formula is asserted.

This theorem requires only the two separators, not a component-size
hypothesis. In particular, it applies when the strict proximity graph
joining directions at projective distance $<\Delta=2\arctan(3/7)$ has
components of sizes two and five and (1) holds. To see the implication,
each cyclic transition between components is a nonedge, so its directed
gap $G$ satisfies $\min(G,\pi-G)\ge\Delta$. A cyclic word with both
component labels has at least two transitions. This proof retains a
transition across the chosen seam. Collisions are edges, not transitions;
equality at $\Delta$ is a nonedge. In fact four transitions are impossible:
$\tan\Delta=21/20>1$ implies $4\Delta>\pi$.

There is **no claim** here for the separator-free scalar superset, arbitrary
offsets or unequal heights, all support roots, arbitrary cardinality, or
continuum Kakeya area. No production root count is changed.

## 2. Literal roofs, the partition, and outsider exclusion

For angular displacement $x=\phi-\theta_i$, the squared radial roofs are
\[
R_{P_i}(x)=\min\{\tfrac14\sec^2x,h^2\csc^2x\},\qquad
R_{B_i}(x)=
\begin{cases}h^2\csc^2x,&|\tan x|\ge2h,\\0,&|\tan x|<2h.\end{cases}
\tag{4}
\]
Indeed $P_i$ is the rectangle $|a|\le1/2,|b|\le h$ in the $(u_i,Ju_i)$
coordinates; the triangle pair additionally requires $|b|\ge2h|a|$.
At tangent-chart poles use these coordinate inequalities, or their radial
limits, not undefined products such as $0\cdot\infty$. Each roof is finite.
All sets are centrally symmetric, so the polar factor $1/2$ cancels the two
antipodal periods: their union areas are the integrals of the maximum
squared roof over **one projective period**.

A center has collar $[\theta_i-\beta,\theta_i+\beta]$. In a long gap $G$,
the uncovered core is $[\beta,G-\beta]$. Every center is at projective
distance at least $\beta$ there, so its source and target roofs coincide.
Among them an endpoint of the gap is nearest: either route to any other
center first passes an endpoint. Since $h^2\csc^2d$ decreases for projective
distance $0<d\le\pi/2$, the core mass is exactly
\[
2h^2\int_\beta^{G/2}\csc^2x\,dx
=2h^2(\cot\beta-\cot(G/2))=F(Q,h)\ge0.
\tag{5}
\]
Removing five such cores leaves five blocks (disjoint apart from endpoint
rays): either one three-center block and four singletons, or two two-center
blocks and three singletons. Collars within a block cover its entire lift
$[-\beta,s_b+\beta]$. A long at equality makes only its core null; keep the
chosen designation rather than merging or charging that wall twice.

**Outsiders do not alter the target roof of a block.** Every route from
an outsider to a block center crosses a boundary long; both projective
routes have length at least $2\beta$. Given a ray in the block, choose a
center whose collar contains it and let its distance be $v\le\beta$.
An outsider has projective distance at least $2\beta-v\ge\beta$, hence
is on its outer branch. Its roof is at most $h^2\csc^2(2\beta-v)$.
Since $\beta<\pi/4$, the identity
\[
[\sin(2\beta-v)-\tan\beta\cos v]\cos\beta
=\cos(2\beta)\sin(\beta-v)\ge0
\tag{6}
\]
shows this is at most the chosen inner roof $\sec^2v/4$.
This pointwise argument covers ties, aliases and nonadjacent competitors.
A singleton therefore has target mass
$\int_{-\beta}^{\beta}\sec^2x/4\,dx=h$.

## 3. Two-center integral and direct three-center insertion

For centers $0,g$, $0\le g\le2\beta$, write $q=\tan(g/2)$. On the left
half $[-\beta,g/2]$ the target winners are, in order:

| Interval | Winning roof |
|---|---|
| $[-\beta,x_*]$ | center 0 inner |
| $[x_*,g-\beta]$ | center 1 outer |
| $[g-\beta,g/2]$ | center 1 inner |

Here $\tan x_*=(\sin g-2h)/\cos g$ on this lift. The first two roofs
cross where $\sin(g-x)=2h\cos x$. On $[-\beta,g-\beta]$, their difference
in this unsquared comparison changes sign once: $\cos g>0$, and
$\sin g-\cos g\tan x$ is decreasing. At $-\beta$ and $g-\beta$ its
comparison with $2h$ has opposite weak signs, so the switch lies between
them. Once both centers are inner, center 1 is farther on this half and
wins. All intervals are allowed to collapse. The directed distances used
here are at most $3\beta<\pi/2$ (five longs imply $10\beta\le\pi$).
Reflection about $g/2$ gives the other half. Thus the block mass is
\[
\begin{aligned}
B(h,q)&=2\left[\frac{\tan x_*+2h}{4}
+h^2\{\cot\beta-\cot(g-x_*)\}
+\frac{2h-q}{4}\right]\\
&=h+\frac{q(1+q^2+8h^2-8hq)}{2(1-q^2)}.
\end{aligned}\tag{7}
\]
The outer primitive has the indicated sign:
$\frac{d}{dx}\cot(g-x)=\csc^2(g-x)$. Subtraction yields
$2h-B=\delta(h,q)\ge0$, because $q\le2h\le2/5$ and
$1+q^2-4hq=(q-2h)^2+1-4h^2>0$.

For a three-center block at $0,g_1,s=g_1+g_2$, the two short gaps give
$s\le4\beta$. Five longs give $10\beta\le\pi$, hence
$s+\beta\le5\beta\le\pi/2$. Write $R_0,R_1,R_2$ for the actual target
roofs on this lift. Insert center 2 into the pair $0,1$:

* On $[-\beta,g_1-\beta]$, centers 1 and 2 are outer, and center 2 is
  farther; it adds no roof.
* On the middle collar $I=[g_1-\beta,g_1+\beta]$,
  $(R_2-\max(R_0,R_1))_+\le(R_2-R_1)_+$.
* On the appended interval $K=[g_1+\beta,s+\beta]$, center 0 is farther
  than center 1, both are outer, and $R_0\le R_1$.

Monotonicity of the outer roof is valid on all these directed distances
by $s+\beta\le\pi/2$. Integrating, and noting that the pair $1,2$ block
is $I\cup K$ while $\int_I R_1=h$, proves the **cap**, not an equality,
\[
H_3\le B(h,q_1)+B(h,q_2)-h.
\tag{8}
\]
No mixed-event chart is used, and no nonadjacent winner is discarded.
Combining the target blocks with (5), both topologies satisfy
\[
H\le\sum_iF(Q_i,h)+3h+B(h,q_1)+B(h,q_2)
=\sum_iF(Q_i,h)+7h-\delta_1-\delta_2.
\tag{9}
\]
The first inequality is equality for disjoint two-center blocks.

## 4. One source bank, including all exposure and pole guards

For a block with centers spanning $[0,s]$, use its immediate outside
centers at $-G_L$ and $s+G_R$. On the whole block $[-\beta,s+\beta]$,
use each of their **actual source roofs with weight $1/2$**. Their mean
is bounded by the one physical source maximum.

For the left branch the directed argument is between $G_L-\beta$ and
$G_L+s+\beta$. Apart from $G_L$ and the shorts in this span, the remaining
arc contains the other four longs. Thus
\[
\beta\le G_L-\beta\le G_L+s+\beta\le\pi-7\beta<\pi-\beta.
\tag{10}
\]
The right branch has the same bounds with reversed direction. Both
branches are eligible on the entire block, with arguments in $(0,\pi)$;
this is a physical pole guard, not analytic continuation of inactive roofs.
The left integral equals
\[
h^2[\cot(G_L-\beta)-\cot(G_L+s+\beta)]
=A(Q_L,h)+E(Q_L;\tan(s/2),h).
\tag{11}
\]
The analogous right integral has the same form. Cotangent is decreasing
on $(0,\pi)$, so every $E\ge0$. Every long has exactly two endpoint-block
incidences, each of weight $1/2$: its base $A$ is entered **once**. Each
block is integrated once, and cores and blocks have disjoint interiors.
Consequently
\[
S\ge\sum_i(F(Q_i,h)+A(Q_i,h))+\mathcal E/2.
\tag{12}
\]
Subtracting (9) from $\tau$ times (12) proves $\tau S-H\ge\Phi$.

For explicit topology labels, let C mean adjacent shorts; their full
half-span is $p=(q_1+q_2)/(1-q_1q_2)$. Let D1 mean disjoint short blocks
sharing a boundary long, and D2 mean disjoint blocks not sharing a long.
Up to cyclic order and reflection these exhaust two short edges on a
seven-cycle. Naming boundary longs as indicated gives
\[
\begin{array}{c|l}
\mathrm C&\mathcal E=E(Q_1;p)+E(Q_2;p)\\
\mathrm {D1}&\mathcal E=E(Q_1;q_1)+E(Q_1;q_2)+E(Q_2;q_1)+E(Q_3;q_2)\\
\mathrm {D2}&\mathcal E=E(Q_1;q_1)+E(Q_2;q_1)+E(Q_3;q_2)+E(Q_4;q_2).
\end{array}\tag{13}
\]
Here $h$ is suppressed in $E$. In D1 the shared long $Q_1$ supplies two
distinct physical block incidences but only one base $A$. In C the full
span is charged at each outside endpoint, never two unshifted overlapping
short-span increments. The denominator $1-q_1q_2$ is positive.

For a rational exposure expression valid also at the auxiliary seam
$Q=1$, put $z_d=1-r^2-4hr$ and $z_n=2h(1-r^2)+2r$. Then
\[
E=\frac{h^2(1+Q^2)^2(z_n-2hz_d)}
{[2Q+2h(1-Q^2)][2Qz_d+(1-Q^2)z_n]},\qquad
z_n-2hz_d=2r(1+4h^2)\ge0.
\tag{14}
\]
The denominator factors represent the sines of $G+\beta$ and
$G+s+\beta$, with positive common scaling. They are positive by (10).
In particular $Q>1$ is harmless. No $\tan G$ chart is required.
The height bound below also gives $s+\beta\le5\beta<13/10<\pi/2$,
so the optional shifted-tangent denominator $z_d$ is positive too.

## 5. The scalar reserve pays the deficit

### Height and gap bounds

The other separator implies every actual gap $G\le\pi-\Delta$, so every
half-gap tangent is at most $7/3$. The five longs, including two
separators, imply
\[
3\arctan(2h)+2\arctan(3/7)\le\pi/2.
\tag{15}
\]
At $h=13/100$, direct exact multiplication gives
\[
(1+13i/50)^3(1+3i/7)^2
=-\frac{8363}{3062500}+\frac{399871}{306250}i.
\tag{16}
\]
The total argument is positive and less than
$3(13/50)+2(3/7)<2<\pi$. Its negative real and positive imaginary parts
therefore place it strictly above $\pi/2$. Monotonicity in (15) proves
$h<13/100$.

### Every long has $L>h/4$

This estimate holds on the entire box $0<h\le1/5$, $2h\le Q\le7/3$.
Put $r=h/Q\le1/2$ and $\bar D=1-r^2(Q^2-1)^2$. For $Q\le1$,
$\bar D\ge3/4$. For $1\le Q\le7/3$, write the subtracted term as
$h^2(Q-1/Q)^2$; monotonicity of $Q-1/Q$ gives
\[
\bar D\ge1-\tfrac1{25}(7/3-3/7)^2=377/441>0.
\]
In particular the denominator of $A$ is positive. Clearing this positive
denominator in $L/h-1/4$ gives
\[
\bar D(L/h-1/4)=f(r)
+r^2[4\tau-9/2-4(\tau-1)r]Q^2
+r^2[9/4+2(\tau-1)r]Q^4,
\tag{17}
\]
where
\[
f(r)=\tau-9/4-2(\tau-1)r+(9/4)r^2+2(\tau-1)r^3.
\]
The $Q^2$ bracket is at least $2\tau-5/2>0$; the $Q^4$ bracket is
positive. On each interval $[a,b]$ below, express $f(a+(b-a)t)$ as
$\sum_{k=0}^3 b_k\binom3k t^k(1-t)^{3-k}$:

| Interval | $b_0,b_1,b_2,b_3$ |
|---|---|
| $[0,1/4]$ | $711/424,\ 3025/2544,\ 7613/10176,\ 6045/13568$ |
| $[1/4,3/8]$ | $6045/13568,\ 23953/81408,\ 28903/162816,\ 11595/108544$ |
| $[3/8,1/2]$ | $11595/108544,\ 2941/81408,\ 233/20352,\ 75/1696$ |

All twelve coefficients are strictly positive, so $f>0$ including the
interval endpoints. This proves $L>h/4$ without a search or a limiting
argument. The checker derives $f$ from (11), (5) and the definition of $L$,
and reconstructs each coefficient in the Bernstein basis.

### A separator has the stronger reserve

For $Q\ge3/7$, put $r=h/Q\le91/300$. Since
$0<D=Q^2-h^2(Q^2-1)^2\le Q^2$ and $1+Q^2\ge58/49$,
\[
L/h\ge g(r)=\tau-2-2(\tau-1)r+\tau(58/49)^2r^2.
\tag{18}
\]
The derivative increases, but
\[
g'(91/300)=-228688/90895<0,\qquad
g(91/300)-5/8=1012129/31164000>0.
\tag{19}
\]
Thus $g$ is decreasing on $[0,91/300]$ and each separator has reserve at
least $(5/8+1012129/31164000)h$. Select two separators and use the strict
$h/4$ bound on the other three longs (even if some are also separators):
\[
\sum_iL(Q_i,h)>
3h/4+2(5/8+1012129/31164000)h
=(2+1012129/15582000)h.
\tag{20}
\]
Discarding only the already justified nonnegative exposure term in (2)
proves (3).

## 6. Weak walls and the zero-height face

* $h=0$: every $B_i$ and $P_i$ is contained in a line segment. Finite
  unions have zero planar area. Do not evaluate $L/h$, $h/Q$ or cotangents.
* $q=0$: labels coincide within their block; $B(h,0)=h$ and
  $\delta(h,0)=h$. Zero exposure span gives zero $E$. No generic-winner
  assumption excludes positive-measure ties.
* $q=2h$ or $Q=2h$: collapsed intervals and null cores are retained with
  their designated status. End rays are area-null; each physical interval
  has just the block/core assignment used above.
* Separator equality $Q=3/7$ is allowed, including simultaneous ties.
  An internal graph threshold tie may change the graph, but does not
  invalidate a configuration retaining the two explicit separators.
* Rotating the projective seam permutes the cyclic gaps and incidences.
  Neither $Q=1$ nor a gap $G>\pi/2$ introduces a physical pole. Bounds
  (10), not an unguarded tangent chart, govern all exposures.

## 7. Precise errata; accepted dependency boundary

The old `c2c5_two_short_cluster_lane.md`, lines 58–74, first sets
$t_1=2q_1/(1-q_1^2)=\tan\theta_1$, then uses
$((1-t_j^2)/(1+t_j^2),2t_j/(1+t_j^2))$ as $(\cos\theta_j,\sin\theta_j)$.
Those expressions instead represent $(\cos2\theta_j,\sin2\theta_j)$.
The printed claim that its equations (3)–(7) give a complete exact envelope
recipe is therefore not accepted. The correct direction pair is obtained
from the **half-angle** tangent $q_1$ (or $p$ for the second cluster center).
This artifact does not certify the other parts of an old evaluator by
silently changing that input, and does not modify the historical file.

The exact diagnostic at $q_1=1/10$ is
\[
t_1=20/99,\quad \cos\theta_1=99/101,\quad
c_{\rm erroneous}=9401/10201,\quad
c_{\rm erroneous}-\cos\theta_1=-598/10201.
\]
The literal proof (4)–(12), especially insertion (8), is independent of
that erroneous chart.

Also, closed auxiliary intervals for a strict proximity graph can touch
across components at threshold ties. Use open intervals, or the direct
cyclic-transition proof in §1. At simultaneous separator ties the internal
span is $\le\pi-2\Delta$, not necessarily strictly smaller. None of these
prose corrections asserts a new production-domain census.

**Verification boundary.** The finite rational identities, coefficient
reconstruction, three cyclic incidence ledgers, and exact angle-coordinate
regression are executable in `verify.py`. The derivation of literal roofs,
area normalization, geometry of the partition, winner ordering, insertion
cap, outsider distance bounds, physical eligibility, and standard analytic
monotonicity/positivity arguments are the handwritten proof above. A green
symbolic check does not mechanically validate arbitrary edits to that
geometry or to this theorem statement. This is not a proof-assistant result.
