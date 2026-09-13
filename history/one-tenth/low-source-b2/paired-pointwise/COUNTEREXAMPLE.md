# PL is false: a literal two-host, positive-measure counterexample

**Theorem.** There is a Borel unit-chord selector with common star center 0 and `|h|<=1/5`, and a Borel cut V consisting exclusively of chords with far endpoint radius `M<99/100`, such that

\[
 |V|=\frac{43}{1000},\qquad
 |S_{1/4}(V)|=\frac1{50}
 <\frac12\frac{43}{1000}=\frac{43}{2000}.
\]

Since `min(11/15,1-2(1/4))=1/2`, this **refutes PL**. Its exact deficit is `3/2000`. Both actual endpoints, both active lobes when present, and all cross-label physical overlaps are retained. The construction is a continuum of literal unit chords, not a finite-direction or independent-arc example.

**Scope:** IL is not decided. Neither area 1/10 nor any accepted lower bound is refuted. No change to accepted B1 sources is made. The geometric proof below is an analytic proof, supported only by a tiny rational-margin checker; it still requires independent parent review.

## 1. Fixed geometry and the one physical source

Write `e_t=(cos t,sin t)` and `n_t=(-sin t,cos t)`. Fix

\[
 \varepsilon=\frac1{100},\quad r=\frac14,\quad
 a=\frac45,\quad \delta=\frac25,\quad
 d=\frac52,\quad g=d-1=\frac32,\quad k=1-\varepsilon^2.
\]

On the **ordinary physical circle**, use exactly two hosts

\[
 A=[0,\varepsilon],\qquad
 B=[\pi+d\varepsilon,\pi+(d+1)\varepsilon].                  \tag{1}
\]

These hosts are disjoint. The projective direction cut is the injective image modulo pi of the real interval

\[
 I=[-\delta\varepsilon,(d+1+\delta)\varepsilon]
   =[-(2/5)\varepsilon,(39/10)\varepsilon].                  \tag{2}
\]

Use q in I as its unique real representative. Its length is `(43/10)epsilon`. Partition this interval into a left exterior piece, a central piece, and a right exterior piece at

\[
 q=(1+\delta)\varepsilon=(7/5)\varepsilon,
 \qquad q=(d-\delta)\varepsilon=(21/10)\varepsilon.          \tag{3}
\]

Either adjoining formula may be used at the two boundary points; for definiteness assign them to the exterior pieces. This has no measure effect and all formulas satisfy the same geometric bounds there.

For the chord `[P(q),F(q)]` specified below, let

\[
 T_q=\operatorname{conv}(0,P(q),F(q)),\quad
 W(V)=\bigcup_{q\in I}T_q,
 \quad S_r(V)=\{\theta:r e_\theta\in W(V)\}.
\]

We prove the exact physical identity

\[
                         S_r(V)=A\cup B.                   \tag{4}
\]

In particular, no labelled lengths or reflected copies are added.

## 2. The exterior pieces: actual unit chords with an inactive near endpoint

This single construction is used twice. Let `[c epsilon,(c+1)epsilon]` be the host in projective coordinates and let sigma be the physical lift: `(c,sigma)=(0,0)` on the left piece and `(d,pi)` on the right piece. For

\[
 q\in[(c-\delta)\varepsilon,(c+1+\delta)\varepsilon]
\]

let alpha be the nearest point to q in `[c epsilon,(c+1)epsilon]`. Set

\[
 \theta=q+\sigma,\qquad \Delta=\alpha-q,\qquad
 h=a\tan\Delta,
\]
\[
 F=a e_\theta+h n_\theta,\qquad
 P=-(1-a)e_\theta+h n_\theta.                               \tag{5}
\]

Then `F-P=e_theta`, so the chord has exactly unit length and projective direction q. Its far endpoint is F, since `a>1/2`. Its far endpoint angle is precisely `alpha+sigma`. The endpoints in these actual oriented coordinates are `(a-1,h),(a,h)`.

We have `|Delta|<=delta epsilon`. The elementary uniform trigonometric bounds used throughout are

\[
 kz\le\sin z\le z\quad(0\le z\le (7/4)\varepsilon),
 \qquad \cos z\ge k\quad(0\le z\le\delta\varepsilon).        \tag{6}
\]

They follow from `sin z>=z-z^3/6`, `cos z>=1-z^2/2`, and `(7/4)^2/6<1`, `delta^2/2<1`. All angles are in the first quadrant when these bounds are used. Hence

\[
 |h|\le\frac{a\delta\varepsilon}{k}
      =\frac{32}{9999}<\varepsilon<\frac15.
\]

Writing M and N for the far and near radii gives

\[
 M^2=a^2+h^2<a^2+\varepsilon^2<(99/100)^2,
 \qquad
 N^2=(1-a)^2+h^2<(1-a)^2+\varepsilon^2<r^2.                 \tag{7}
\]

Thus the near endpoint is genuinely below the radius-r circle: it contributes **no** radius-r lobe. This is not an omitted active endpoint.

If `Delta=0`, the actual section is the singleton `{q+sigma}`. If `Delta!=0`, put `eta=|Delta|` and

\[
 b_r=\arcsin((a/r)\tan\eta).
\]

We claim

\[
                        \eta<b_r<\varepsilon+\eta.         \tag{8}
\]

The lower inequality follows from `a/r>1`. For the upper one, by (6) it suffices to prove

\[
 (a/r)\eta<(\varepsilon+\eta)k^2.
\]

The quotient `eta/(epsilon+eta)` increases in eta, so it suffices to check the fixed endpoint `eta=delta epsilon`. The exact rational margin is

\[
 (1+\delta)k^2-(a/r)\delta
                =\frac{59860007}{500000000}>0.             \tag{9}
\]

This also ensures the arcsine argument is below one. By the actual triangle-circle formula (or by radial projection of the base), its single lobe has endpoints

\[
 \alpha+\sigma,\qquad
 q+\sigma+\operatorname{sgn}(\Delta)b_r.
\]

If q is below the host, (8) puts this lobe between the lower and upper host endpoints. If q is above the host, the reflected inequality does the same. If q lies inside the host, the singleton already lies there. Therefore every left exterior chord contributes only to A, and every right exterior chord only to B.

Moreover, for **every** q in `[0,epsilon]`, the left formula has h=0 and contributes the physical angle q. For every q in `[d epsilon,(d+1)epsilon]`, the right formula similarly contributes q+pi. Consequently the exterior families alone already cover every angle of both hosts in (1).

## 3. The central gap: both endpoints lie on the two existing host rays

For the central q put

\[
 s=q/\varepsilon,\quad u=s-1,\quad v=d-s,
 \quad u+v=g=3/2.
\]

Thus

\[
 2/5\le u,v\le11/10,\qquad
 2/5\le w:=\min(u,v)\le3/4.
\]

Define the two **actual endpoint radii**

\[
 R_A=\frac{\sin(v\varepsilon)}{\sin(g\varepsilon)},\qquad
 R_B=\frac{\sin(u\varepsilon)}{\sin(g\varepsilon)},
\]

and endpoints

\[
 F=R_A e_\varepsilon,\qquad
 P=R_B e_{\pi+d\varepsilon}=-R_B e_{d\varepsilon}.          \tag{10}
\]

The sine addition identity gives exactly

\[
 R_A e_\varepsilon+R_B e_{d\varepsilon}=e_q,
 \qquad F-P=e_q.                                          \tag{11}
\]

Indeed, after rotation by -q the imaginary parts cancel and the real part is
`[sin(v epsilon)cos(u epsilon)+sin(u epsilon)cos(v epsilon)]/sin(g epsilon)=1`.
Thus these are actual unit chords with direction q, not arbitrarily prescribed arcs.

Their **common signed height** in direction e_q is

\[
 h=-\frac{\sin(u\varepsilon)\sin(v\varepsilon)}
             {\sin(g\varepsilon)}.                        \tag{12}
\]

Both longitudinal endpoint signs are opposite because all angles `u epsilon,v epsilon` are acute. Either endpoint can be the far one; reversing the actual orientation when necessary gives precisely the admitted coordinates `(x-1,h'),(x,h')` with `x>=1/2`. Since both endpoint radii are below 99/100, also `x<1`.

From (6), both radii obey

\[
 \frac4{15}k\le R_A,R_B\le\frac{11}{15k},
\]

and the exact bounds are

\[
 \frac4{15}k=\frac{3333}{12500}>\frac14,
 \qquad \frac{11}{15k}=\frac{2000}{2727}<\frac{99}{100}.     \tag{13}
\]

So **both lobes are active**. Also

\[
 |h|\le\frac{\varepsilon uv}{gk}
       \le\frac{3\varepsilon}{8k}
       =\frac{25}{6666}<\min(r,1/5).                       \tag{14}
\]

In particular this construction stays strictly in the disconnected two-lobe regime; no merged cone is being divided or charged twice.

Put `b_r=arcsin(|h|/r)`. Since both endpoints are outside the circle, the actual complete section consists of precisely

\[
 [q-b_r,\varepsilon]\quad\text{and}\quad
 [\pi+d\varepsilon,q+\pi+b_r].                             \tag{15}
\]

To put these inside A and B simultaneously, it suffices to prove

\[
 b_r\le\min(q,(d+1)\varepsilon-q)
             =(1+w)\varepsilon.                           \tag{16}
\]

This is the exact coupled-geometry step. By (6), (12), and monotonicity of sine/arcsine on the acute range, it suffices that

\[
 \frac{uv}{g}\le\frac{1+w}{4}k^2.                          \tag{17}
\]

Since `uv=w(g-w)`, complete the square:

\[
 \frac{1+w}{4}-\frac{uv}{g}
 =\frac23\left(w-\frac9{16}\right)^2+\frac5{128}.
\]

The change from 1 to `k^2` costs at most

\[
 \frac{1+w}{4}(1-k^2)
 \le\frac78\varepsilon^2.
\]

The surviving exact margin is

\[
 \frac5{128}-\frac78\varepsilon^2
                 =\frac{1559}{40000}>0.                  \tag{18}
\]

This proves (17), hence (16), **uniformly for every central direction**, without a grid or numerical trigonometric check. Formula (15) now proves containment in the same two already-covered physical hosts.

## 4. Borel realization, union equality, and strict failure

The exterior formulas are continuous on their pieces apart from the harmless clamp breakpoints; the central formula is continuous with a nonzero denominator. A fixed choice at the two seams makes the entire selector Borel. The real lift I has length less than pi and therefore gives a Borel positive-measure projective cut with exactly its real length.

Every selected chord is exactly unit, has `|h|<1/5`, and has `M<99/100`. All triangles use the same center 0. Sections 2 and 3 show `S_r(V) subset A union B`; the zero-height rows inside each host give the reverse inclusion. This proves (4) for the **entire physical source once**.

If a selector on every projective direction is desired, extend outside V by the radial unit chord `[0,e_q]`, using any standard Borel representative modulo pi. Its far radius is 1 and height is zero. Thus the low set is exactly L=V; this extension does not enter `W(V)` and changes none of the conclusions. No continuity of the selector is required by PL.

Finally,

\[
 |S_{1/4}(V)|=|A|+|B|=2\varepsilon=\frac1{50},
 \qquad |V|=(d+1+2\delta)\varepsilon=\frac{43}{1000},
\]

so

\[
 \min(11/15,1-2r)|V|-|S_r(V)|
       =\frac{43}{2000}-\frac1{50}=\frac3{2000}>0.
\]

The addition here is only between the two explicitly disjoint physical hosts after taking the union of **all** labels. Central chords place one lobe in each host, while exterior chords place their single active lobe in one host. These cross-label collisions are exactly what invalidates the proposed scalar-to-union inference. QED.

## 5. Verification and stopping boundary

`ADMISSION-LOCAL.md` preregistered one fixed exact control before arithmetic execution. `check.py` uses only rational arithmetic and verifies the displayed margins and the square-completion identity. It does not evaluate a finite sample of the continuum and call that a proof: (6), (8), and (17) prove the continuum inequalities analytically. Checks use explicit exceptions rather than Python assertions, so optimized mode retains all gates.

`CHECK-RESULT.txt` contains the actual replay output. No optimization, scan, random scout, LP, SMT, numerical quadrature, or new parameter choice was used. The first certified counterexample triggers the stop rule: no further PL candidate work is pursued. Remaining work is artifact verification and commit only.

**New mathematical state:** PL is false on a literal admissible positive-measure Borel family. IL remains OPEN/independent in this lane. The conditional bridge must not assume PL, but an independent IL proof could still suffice. The accepted B1 theorems and global lower bound are untouched.
