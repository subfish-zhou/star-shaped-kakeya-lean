# A seven-row universal lower bound for star-shaped Kakeya sets

## Theorem and scope

Let E be any subset of the Euclidean plane. Suppose there is a point o such
that [o,x] is contained in E for every x in E, and E contains a closed unit
segment in every unoriented direction. Then its Lebesgue outer area satisfies

\[
 |E|^*\ge \boxed{0.082812499999972190}.
\]

No measurability, boundedness, closedness, convexity, or continuity of segment
choice is assumed. Direction length on the projective circle is normalized to
π; polar angular length on the ordinary circle is 2π. The displayed finite
decimal is an exact rational lower bound, not a rounded numerical estimate.
This is a **human mathematical proof plus outward Arb arithmetic**, not a Lean
theorem and not a claim about the sharp constant or a proof of the 0.1 target.

The proof uses one interval-union lemma, a direct radial collar inclusion, and
fixed prices. Their purpose is to pay every direction while never charging a
physical point more than once. The prices below are the coalesced original
witness, not newly optimized parameters; their discovery is not reconstructed.

## 1. Recover a finite-valued Borel midpoint selector

Translate o to 0. Given any open G containing E, choose one unit segment for
each direction q and its anchored triangle T_q=conv(0,A_q,B_q). Star-shapedness
puts T_q in E. A compact T_q has positive clearance from the complement of G
(unless G is the whole plane, where there is nothing to check). Holding its
midpoint fixed while changing its unoriented direction changes the triangle
continuously in Hausdorff distance. Thus this midpoint works throughout an
open neighborhood of q. Compactness of the projective circle gives finitely
many such neighborhoods. Assign each direction to the first neighborhood
containing it and use that neighborhood's midpoint.

This is a finite-valued **Borel midpoint** selector, not a finite family of
triangles: q still ranges over all directions. Every recovered triangle lies
in G. A Borel parameterization of triangles by q and a compact simplex shows
that the union W, and the union W(V) over any Borel direction cut V, are
analytic, hence Lebesgue measurable. Their fixed-radius angular sections are
analytic too. Polar integration is therefore legitimate. We do not assert
that any original arbitrary selector was measurable.

Write a recovered segment as

\[
 A=(s-\tfrac12)u_q+h n_q,\qquad
 B=(s+\tfrac12)u_q+h n_q,
 \quad M=\max(|A|,|B|),\quad N=\min(|A|,|B|).
\]

Here N means the smaller **endpoint** radius, not the minimum radius along the
segment. Rerun the height dichotomy after recovery: if some |h|≥H=1/5, its
triangle has area |h|/2≥1/10, so G already has sufficient area. Otherwise all
|h|<H. Fix M₀=99/100 and R=8/5, and partition directions into

* L: M<M₀;
* F: M₀≤M<R, further partitioned into P: h≠0 and Z: h=0;
* D_n: m_n≤M<2m_n, where m_n=2ⁿR and n≥0.

These are exhaustive Borel cuts. The estimates below allow their closed
boundary cases. Write S_r(V) for the angular section of W(V). Use the common
physical measure

\[
 d\nu=\min(r,1)\,dr\,d\theta
      =\min(1,1/|x|)\,dx,\qquad \nu(W)\le |W|.
\]

The density at 0 is immaterial. The weighting outside radius one is a deliberate
loss, not equality with ordinary area.

## 2. The interval-union lemma and the low kernel

**Interval lemma.** Let J_i be arbitrary circular intervals, allowing singletons
and repeats. Extend each to one side to K_i by at most (Λ−1)|J_i|, where Λ≥1.
Then

\[
 |\bigcup_i K_i|^*\le(2\Lambda-1)|\bigcup_i J_i|^*.
 \tag{1}
\]

Indeed, enclose the J-union in an open set O. Each J_i lies in one component C
of O. If |C|=ℓ, every associated K_i lies in the enlargement of C by
(Λ−1)ℓ on each side, of length at most (2Λ−1)ℓ. Sum over the countably many
components and infimize over O. If O is the whole circle the estimate is
immediate. Repeated bases are still charged only through their physical union;
a singleton has no permitted positive extension.

Put m=1−M₀=1/100. For a low segment its positive and negative tangential
endpoint magnitudes p=s+1/2 and n=1/2−s satisfy p+n=1 and

\[
 p,n\ge1-\sqrt{M_0^2-h^2}\ge m>0.
\]

For 0<r<m and |h|≤r the two real endpoint angular components have lengths

\[
 a_r-b_+,\ a_r-b_-,\qquad
 a_r=\arcsin(|h|/r),\quad b_+=\arctan(|h|/p),\quad b_-=\arctan(|h|/n).
\]

Extending either component to its ideal direction anchor adds b_±. Since
b_±/a_r≤r/m, each extension has dilation at most m/(m−r). At h=0 retain the
two actual radial rays as singleton components; at |h|=r retain the closed
touching arcs. Thus no zero-height or tangency directions are discarded.

For |h|>r the whole endpoint-angle interval is present. Its length is at least

\[
 \alpha=2\arcsin(1/(2M_0)).
\]

To see this, the cosine law gives cos γ=(a²+b²−1)/(2ab) for endpoint radii
0<a,b≤M₀<1. Each partial derivative of this expression is positive (for example
its a-derivative has numerator a²−b²+1>0). Hence its largest value is at
a=b=M₀. Each ideal anchor is at most β=arctan(H/m) beyond the corresponding
end of this interval. Use the same physical interval twice as a base, extending
it separately toward the two anchors, each with dilation at most 1+β/α.
Apply (1) to all bases together: the extended union covers both lifts of L,
of total length 2|L|. Since H>m here, the resulting small-radius kernel is

\[
 |S_r(L)|\ge g(r)|L|,\quad
 g(r)=\min\!\left\{\frac{2(m-r)}{m+r},\frac{2\alpha}{\alpha+2\beta}\right\}
 \quad(0<r<m).
 \tag{2}
\]

For m≤r<1/2 select just the far endpoint, whose radius M is at least 1/2 by
the triangle inequality. If |h|≤r, the far component has length
arcsin(|h|/r)−arcsin(|h|/M). The function arcsin(t)/t is increasing: it is
the average over [0,t] of the increasing function (1−u²)^(−1/2).
Consequently the ratio of the omitted endpoint drift to arcsin(|h|/r) is at
most r/M≤2r. Extending to the far anchor and applying (1) gives coefficient
(1/2−r)/(1/2+r). If |h|>r, the full endpoint interval has length at least α
and the far drift is at most arcsin(2H). The same lemma gives coefficient

\[
 k=\frac{\alpha}{\alpha+2\arcsin(2H)}.
\]

The two cases can be combined *inside one application* of (1), using the
larger dilation; adding separate physical-union bounds would be invalid.
The extended union contains a Borel choice of one lift of every low direction,
whose length is |L|. Thus a valid (possibly weakened when r≥H) kernel is

\[
 g(r)=\min\!\left\{k,\frac{1/2-r}{1/2+r}\right\}
 \quad(m\le r<1/2),\qquad g(r)=0\quad(r\ge1/2).
 \tag{3}
\]

In the h=0 case the selected anchor is an actual radial ray, so the same
argument includes it literally. All statements also apply to Borel subcuts
of L and charge unions, not triangle multiplicities.

## 3. Direct radial terminal inclusion

Take a Borel cut V with m'≤M≤R', where m'>1/2. From each far endpoint take a
collar of length 0<t≤1/2 along its chord. Every collar point has radius at
least m'−t>0 and at most R'. Let P_t(V) be the union of its angular images.
We claim

\[
 |P_t(V)|\ge\frac{t}{\pi R'}|V|. \tag{4}
\]

Enclose P_t(V) in any open angular set O. Each collar image is connected and
lies in a component C. If C has length ℓ≥t/R', the trivial projective length
bound π is at most πR'ℓ/t. Otherwise ℓ<t/R'<1, and let c be C's midpoint.
Transverse projection of the two collar endpoints gives

\[
 t|\sin(q-c)|\le2R'\sin(\ell/2).
\]

The possible projective directions therefore have total length at most
2 arcsin(2R' sin(ℓ/2)/t)≤πR'ℓ/t: use sin(ℓ/2)≤ℓ/2 and
arcsin u≤πu/2 on [0,1]. Cover V by these direction sets, sum over C, and
infimize over O. This argument includes radial collars. If O is the entire
circle, the required bound is again trivial.

Now fix 0<r<m' and take t=min(1/2,m'−r). The radial segment from 0 to each
collar point is in its triangle, so

\[
 P_t(V)\subset S_r(V),\qquad
 |S_r(V)|\ge\frac{\min(1/2,(m'-r)_+)}{\pi R'}|V|. \tag{5}
\]

Multiply by any fixed nonnegative radial price p(r) and min(r,1), and integrate.
This gives the terminal payment

\[
 C_{m',R'}[p]=\frac1{\pi R'}\int_0^\infty
 p(r)\min(r,1)\min(1/2,(m'-r)_+)\,dr.
 \tag{6}
\]

There is no first-birth parameter, Stieltjes boundary term, or matching claim.
For F apply (6) once with (m',R')=(M₀,R), to the whole finite-high cut, including
both P and Z.

## 4. The other finite-high payments

Orient a segment toward its far endpoint and write its tangential coordinate
as x=√(M²−h²)≥1/2. Its other endpoint has

\[
 N(M,h)^2=M^2+1-2\sqrt{M^2-h^2}. \tag{7}
\]

This increases with |h|. At fixed h, its M-derivative has sign
1−1/√(M²−h²), so it first decreases and then increases. Its maximum over
M∈[M₀,R], |h|≤H is therefore attained at h=H and an M endpoint.
Both endpoints satisfy N<5/8. The verifier checks this with exact rational
squaring: for M=M₀,R,

\[
 D=(M^2+1-(5/8)^2)/2>0,\qquad M^2-H^2>D^2.
\]

On 5/8≤r≤4/5 we have N<r<M₀≤M, so the entire far angular component formula
used above is legal, even if the perpendicular foot is outside the segment.
For P its one-sided extension gives

\[
 |S_r(P)|\ge\frac{M_0-r}{M_0+r}|P|. \tag{8}
\]

For Z, N=|M−1|≤3/5, and every r∈[31/40,4/5] is strictly between N and M.
Each selected far direction is therefore an actual radial ray of its triangle.
The far anchors form one lift of Z, so

\[
 |S_r(Z)|\ge |Z|\quad(31/40\le r\le4/5). \tag{9}
\]

This support is active for **every** M∈[M₀,R]; no pole-event sweep or sampled
parameter argument is needed.

## 5. Seven fixed price rows and explicit primitives

Write p_L,p_T,p_P,p_Z,p_D for the five columns below; unspecified radii have
price zero. Endpoints are half-open to fix ownership (individual radii are
null for ν).

| Radius interval | p_L | p_T | p_P | p_Z | p_D |
|---|---:|---:|---:|---:|---:|
| [0,17/40) | 1 | 0 | 0 | 0 | 0 |
| [17/40,9/20) | x | 1−x−ε | 0 | 0 | 0 |
| [9/20,19/40) | y | 1−y−ε | 0 | 0 | 0 |
| [19/40,5/8) | 0 | 1 | 0 | 0 | 0 |
| [5/8,31/40) | 0 | 0 | 1 | 0 | 0 |
| [31/40,4/5) | 0 | 0 | z | 1−z−ε | 0 |
| [4/5,8/5) | 0 | 0 | 0 | 0 | 1 |

\[
 x=\frac{316269962741}{999999000000},\quad
 y=\frac{96233328491}{142857000000},\quad
 z=\frac{9039395633}{111111000000},\quad
 \varepsilon=\frac1{999999000000}.
\]

All prices are nonnegative. Exact rational addition gives load 1−ε in the
three mixed rows and 1 in every other row. In particular, one must not reject
an exact unit load merely because separately rounded Arb summands have an
upper endpoint above one.

Here are the actual branch primitives; no quadrature is hidden in the checker.
Define

\[
 Q_b(r)=-\frac{r^2}{2}+2br-2b^2\log(1+r/b),\qquad
 Q_b'(r)=\frac{r(b-r)}{b+r},
\]
\[
 c_H=\frac{2\alpha}{\alpha+2\beta},\quad
 a=\frac{m\beta}{\alpha+\beta},\quad
 c=\frac{1-k}{2(1+k)}.
\]

Outward arithmetic checks 0<a<m<c<17/40 and a<H. An antiderivative from 0 of
r g(r), for 0≤r≤1/2, is

\[
 F_L(r)=
 \begin{cases}
 c_Hr^2/2,&0\le r\le a,\\
 c_Ha^2/2+2[Q_m(r)-Q_m(a)],&a\le r\le m,\\
 F_L(m)+k(r^2-m^2)/2,&m\le r\le c,\\
 F_L(c)+Q_{1/2}(r)-Q_{1/2}(c),&c\le r\le1/2.
 \end{cases}
\]

Thus the low per-radian payment is exactly

\[
 C_L=F_L(17/40)+x[F_L(9/20)-F_L(17/40)]
                  +y[F_L(19/40)-F_L(9/20)].
\]

Let J_s(u,v)=∫_u^v min(r,1)min(1/2,(s−r)_+)dr. Split only at
r=1,s−1/2,s. On each resulting interval the following primitives apply:

| Region | Primitive |
|---|---|
| r≤1, r≤s−1/2 | r²/4 |
| r≥1, r≤s−1/2 | r/2 |
| r≤1, s−1/2≤r≤s | sr²/2−r³/3 |
| r≥1, s−1/2≤r≤s | sr−r²/2 |
| r≥s | 0 (zero integrand) |

For each piece use the primitive difference, not one globally continuous
primitive without its constants. All J-values at the price endpoints are
computed as exact Fractions. With T=C_{M₀,R}[p_T], the finite-high payments are

\[
 \pi T=\frac1R\sum_{[u,v)}p_TJ_{M_0}(u,v),
\]
\[
 C_P=Q_{M_0}(31/40)-Q_{M_0}(5/8)
       +z[Q_{M_0}(4/5)-Q_{M_0}(31/40)],
\]
\[
 C_Z=(1-z-\varepsilon)\frac{(4/5)^2-(31/40)^2}{2}.
\]

The three finite branch area coefficients are πC_L, π(T+C_P), π(T+C_Z).
The independently implemented checker uses 192-bit outward Arb for log, asin,
atan and π, never floating-point comparisons. It verifies the following
rational lower bounds, each strictly larger than the theorem's floor:

| Branch | Certified strict lower bound |
|---|---:|
| πC_L | 0.082812499999998901998654 |
| π(T+C_P) | 0.082812499999991696642604 |
| π(T+C_Z) | 0.082812499999972190411137 |

These are conservative endpoints, not claimed exact values. The last branch
is the smallest of these three; retaining its original fractions preserves
the current sharper floor instead of substituting a simpler 0.0828 theorem.

## 6. Fresh tail bands and one final source sum

For D₀ use (6) with (m',R')=(R,2R) and the last table row. Exact integration
across r=1 and r=11/10 gives

\[
 J_{8/5}(4/5,8/5)=\frac{53}{200},\qquad
 \pi C_0=\frac{53}{640}=0.0828125.
\]

For each n≥1 use full price on the fresh band [m_n/2,m_n). These bands are
pairwise disjoint and lie beyond every seven-row price. Since m_n≥16/5, the
whole band lies above 1, and

\[
 \int_{m_n/2}^{m_n}\min(1/2,m_n-r)\,dr
   =\frac{m_n}{4}-\frac18,
\]
\[
 C_n=\frac1{8\pi}-\frac1{16\pi m_n},\qquad
 \pi C_n\ge\frac{27}{256}.
\]

This is an exact increasing function of m_n. It proves every remaining scale;
there is no extrapolation from finitely many samples.

All the prices were fixed before choosing a cut. Equations (2)–(9) and polar
integration give

\[
 C_L|L|+T|F|+C_P|P|+C_Z|Z|+\sum_{n\ge0}C_n|D_n|
 \le \int_W\!\left(p_L+p_T+p_P+p_Z+p_D
                 +\sum_{n\ge1}\mathbf1_{[m_n/2,m_n)}\right)d\nu
 \le\nu(W)\le|G|.
\]

For example the terminal integral is first taken over W(F)⊆W and appears
**once**; it is not independently reissued to overlapping subclasses. Other
subunions can overlap spatially, but their nonnegative prices have pointwise
sum at most one. Countable summation is justified by monotone convergence.
Since |F|=|P|+|Z| and all the disjoint direction classes have total length π,
the left side is at least

\[
 \pi\min\{C_L,T+C_P,T+C_Z,C_0,\inf_{n\ge1}C_n\}
 >0.082812499999972190.
\]

The bound is uniform in G. Infimizing over open supersets gives the stated
outer-area inequality. This last step does not assume that E is measurable,
and no claim of a strict infimum or an attained extremizer is needed. ∎

## Verification boundary

`run.py` checks the fixed price identity, exact source loads, endpoint support
guards, splice ordering, the five arithmetic comparisons and seven focused
tests. The geometric and measurable-set arguments above are human proofs;
the script does not formalize them. `README.md` gives the exercised normal and
optimized replay; `PROVENANCE.md` records comparison with the immutable
original witness. No old optimizer, dense schedule, old receipt namespace,
Lean build, or unrelated research lane is a runtime dependency.
