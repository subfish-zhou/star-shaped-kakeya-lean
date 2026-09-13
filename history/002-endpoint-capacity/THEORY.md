# Spike 002 — selector-independent endpoint-paired radial capacity

Date: 2026-08-03 · branch `research/endpoint-capacity` · base `f5693b9`

**Scope of this channel.** Universal *lower*-bound structural theory only. Nothing
here is an upper-profile/KKT optimisation and nothing here is a variation of the
Li confined/escaping split. The published constant `131*pi/6250` and the
certified upper construction are used only as *comparison anchors*.

---

## 0. Evidence boundary

| Item | Grade | What it establishes |
|---|---|---|
| §1–§3 (Theorem 1, Lemma 2, Theorem 3) | **proved**, paper level, self-contained | exact arbitrary-selector capacity identity; exact paired-chord identities; sharp `pi/4` for origin-crossing needles |
| §5 (Lemma 7) | **proved**, paper level, self-contained, **sharp** | one-dimensional sliver covering inequality |
| §6 (Theorem A, Corollaries A1/A2) | **proved**, paper level, self-contained | `|{rho >= r}|` lower bound and the capacity constant `(3/8 - (ln 2)/2) pi` |
| §7 (Proposition A3) | **proved** but with **unoptimised** constants | far-needle branch |
| §8 (Theorem NG) | **refutation**, backed by an explicit legal family + closed-form computation | the dyadic endpoint Hall–Carleson candidate is dead |
| §9 | **resolved no-go plus remaining open routes** | universal two-sided covering gain refuted; other structural losses catalogued |
| `RESULTS.json` | numerical evidence / exact reconstruction | see `README.md` |

No statement below is machine checked. No Lean was attempted (per the workflow
instruction: derive and probe first).

---

## 1. Arbitrary-selector formulation, and the exact capacity theorem

### 1.1 Setting

`E ⊂ R^2` is a **star-shaped Kakeya set**: star-shaped about some `O` (we take
`O = 0`), and for every `alpha` in the projective circle `Tp = R/piZ` it
contains a closed unit segment of direction `alpha`. No measurability, no
closedness, no boundedness, no continuity is assumed. `Tp` carries Haar measure
of total mass `pi`; `S^1 = R/2piZ` carries mass `2pi`. `L*` is planar Lebesgue
**outer** measure, `|·|*` one-dimensional outer measure.

Fix, by the axiom of choice, **one** needle `N_theta ⊂ E` for each `theta ∈ Tp`
and retain the **full paired chord**

```text
Gamma_theta(u) = p_theta + u e(theta),      u ∈ [0,1],   |q_theta - p_theta| = 1,
```

together with its origin triangle `Delta_theta = conv({0} ∪ Gamma_theta) ⊂ E`
(triangle reduction; this is the only use of star-shapedness). Write

```text
Tri(E) = union_{theta ∈ Tp} Delta_theta  ⊂  E .
```

The selector `theta ↦ (p_theta, q_theta)` is **completely arbitrary**: it may be
non-measurable, everywhere discontinuous, and its endpoint marginals may be
atomic. Every statement below quantifies over all such selectors.

### 1.2 The radial function and the three equivalent capacities

```text
rho(phi) := sup { |x| : x ∈ union_theta Gamma_theta ,  x ≠ 0 ,  arg x = phi } ,
            sup(empty) := 0 ,                                  phi ∈ S^1 .
```

`rho` is in general **non-measurable**. Let `∫^*` denote the upper Lebesgue
integral, `∫^* f = inf { ∫ G : G measurable, G >= f pointwise }`.

> **Theorem 1 (exact capacity identity; arbitrary selector).**
> For every star-shaped Kakeya set `E`, every star centre `O = 0` and every
> needle selection,
>
> ```text
> Cap2 := (1/2) ∫^*_{S^1} rho(phi)^2 dphi
>       =  L*( Tri(E) )
>       =  inf { |U| : U ⊂ R^2 open, U ⊇ Tri(E) }
>       <=  L*(E) .
> ```

*Proof.* The third expression equals the second by the definition of Lebesgue
outer measure through open covers, so only `L*(Tri(E)) = (1/2)∫^* rho^2` needs
proof.

`(>=)` Let `eps > 0` and let `U ⊇ Tri(E)` be open with `|U| <= L*(Tri(E)) + eps`.
Put `U_phi = { t > 0 : t e(phi) ∈ U }` and `G(phi) = 2 ∫_{U_phi} t dt ∈ [0,∞]`.
`U` is open, hence measurable, so `G` is measurable and, by polar coordinates,
`|U| = (1/2) ∫_{S^1} G`. Fix `phi` with `rho(phi) > 0` and `t < rho(phi)`. There
is `x` in some `Gamma_theta` with `arg x = phi` and `|x| > t`; star-shapedness
puts the whole segment `[0,x]` inside `Delta_theta ⊂ Tri(E) ⊂ U`, so
`(0,t] ⊂ U_phi`. Letting `t ↑ rho(phi)` gives `G(phi) >= rho(phi)^2`. Since `G`
is a measurable majorant of `rho^2`, `∫ G >= ∫^* rho^2`, hence
`L*(Tri(E)) + eps >= |U| >= (1/2) ∫^* rho^2`.

`(<=)` Let `G` be any measurable majorant of `rho^2` and put
`V = {0} ∪ { x ≠ 0 : |x|^2 <= G(arg x) }`. `V` is measurable (preimage of a
measurable set under the measurable map `x ↦ (|x|, arg x)`) and
`|V| = (1/2) ∫ G`. If `y ∈ Tri(E)` then `y = lambda x` with `x ∈ Gamma_theta`,
`lambda ∈ [0,1]`; if `y ≠ 0` then `arg y = arg x` and
`|y| <= |x| <= rho(arg y)`, so `y ∈ V`. Hence `L*(Tri(E)) <= (1/2) ∫ G`, and
taking the infimum over `G` finishes. `∎`

**Remarks.**

* No measurability of `E`, of `rho`, of the selector, or of any fibre is used.
  The proof is exactly the open-cover argument demanded by the arbitrary-selector
  setting; the `inf over open U` form is the definition one should formalise.
* `Cap2` is **monotone in the selection**: enlarging the family of retained
  chords enlarges `Tri(E)` and hence `Cap2`. Writing `Cap2^max(E)` for the value
  obtained by retaining *every* unit segment of `E`, one has
  `Cap2(selector) <= Cap2^max(E) <= L*(E)` for every selector.
* Theorem 1 by itself is **a reformulation, not a bound** (this is fatal control
  6). Its value is that it fixes the exact object every later lemma must bound,
  and that it does so without any measurable-selection assumption. §6 is the
  first place where an actual lower bound appears.
* Layer cake, in the same generality: for every `r > 0`,
  `Cap2 >= ∫_0^∞ r · |{phi : rho(phi) > r}|* dr`, because for any measurable
  `G >= rho^2` one has `{rho > r} ⊂ {G > r^2}` and
  `(1/2)∫G = ∫_0^∞ r |{G > r^2}| dr`. The map `r ↦ |{rho > r}|*` is
  nonincreasing, hence measurable. This is the only route from level sets to
  capacity used below.

---

## 2. Exact paired-chord geometry

Let `Gamma` be a closed unit segment with endpoints `p, q`, let `A = |p|`,
`B = |q|`, `h = dist(0, aff Gamma)`, and let

```text
delta := pi - angle(p, 0, q)  ∈ [0, pi]
```

be the **antipodal defect**, defined whenever `A > 0` and `B > 0`;
`delta = 0` exactly when `0` lies on the open segment. If one endpoint is the
origin (`A = 0`, say) then `delta` is undefined and that case is excluded from
(i), (ii), (v) below; there `B = 1`, `m = 0`, `M = 1`, and (iii), (iv), (vi)
hold trivially.

> **Lemma 2 (exact paired-chord identities).**
> Items (i), (ii), (iii), (v) assume `A > 0` and `B > 0`, so that `delta` is
> defined. The *consequence* `A + B >= 1` of (iii), and items (iv) and (vi),
> hold unconditionally: `A + B = |p| + |q| >= |q - p| = 1` is the triangle
> inequality, (iv) follows from it, and (vi) is proved directly below. (If
> `A = 0` then `B = 1`, `m = 0`, `M = 1`, and (iv), (vi) read off directly.)
> ```text
> (i)   A^2 + B^2 + 2 A B cos(delta) = 1               (law of cosines)
> (ii)  A B sin(delta) = h                             (twice the triangle area)
> (iii) (A+B)^2 = 1 + 4 A B sin^2(delta/2) >= 1        hence A + B >= 1
> (iv)  A^2 + B^2 >= (A+B)^2 / 2 >= 1/2                (universal, all h)
> (v)   if the foot of the perpendicular lies in Gamma then
>       delta = arcsin(h/A) + arcsin(h/B)
> (vi)  M := max(A,B) >= 1/2, and M^2 >= m^2 + 1/4 where m = dist(0, Gamma)
> ```

*Proof.* (i) is the law of cosines in triangle `0pq` with `|pq| = 1` and
`angle(p,0,q) = pi - delta`. (ii): the area of `0pq` is both `h/2` and
`(1/2) A B sin(pi - delta)`. (iii) add `2AB` to (i). (iv) is (iii) plus
`2(A^2+B^2) >= (A+B)^2`. (v) the angles of `0pq` at `p` and at `q` are
`arcsin(h/A)` and `arcsin(h/B)` when the foot is interior, and they sum with
`angle(p,0,q)` to `pi`.

(vi) `M >= (A+B)/2 >= 1/2` by (iii). For `M^2 >= m^2 + 1/4`, parametrise the
chord by signed arclength `tau` from the foot, `tau ∈ [t0, t0+1]`, so that
`|Gamma(tau)|^2 = h^2 + tau^2`; then
`M^2 = h^2 + max(t0^2, (t0+1)^2)` and `m^2 = h^2 + min_{tau ∈ [t0,t0+1]} tau^2`.
If `t0 <= 0 <= t0+1` (foot interior) then `m^2 = h^2` and
`max(|t0|, t0+1) >= (|t0| + (t0+1))/2 = 1/2`, so `M^2 - m^2 >= 1/4`. If
`t0 > 0` then `m^2 = h^2 + t0^2` and `M^2 - m^2 = (t0+1)^2 - t0^2 = 2 t0 + 1 >= 1`;
the case `t0 + 1 < 0` is symmetric. `∎`

**Reading.** `(iv)` is the *paired* endpoint inequality: it is universal, it is
sharp, and it is exactly the `h ≡ 0` mechanism. `(i)`–`(ii)` say precisely how
the pairing degrades: the two endpoints subtend `pi - delta` at the origin,
never `pi`, and `delta` is *not* small compared with the angular scale on which
`h` varies. §8 turns this into the fatality of every "small defect ⇒ almost
`pi/4`" statement.

---

## 3. The origin-crossing class: sharp `pi/4`, arbitrary selector

> **Theorem 3.** Suppose the selection can be made so that `0 ∈ N_theta` for
> every `theta ∈ Tp` (this implies `h ≡ 0`, but is strictly stronger than it:
> the origin may also lie on the line of the needle without lying on the needle,
> see FATALITY.md F5-OC). Then
> `L*(E) >= Cap2 >= pi/4`, and `pi/4` is attained by the closed disk of
> radius `1/2` with `N_theta` its diameters. No measurability or continuity of
> the selection is used.

*Proof.* Fix `theta` and distinguish two cases.

*The origin is interior to `N_theta`.* Then both endpoints are nonzero, they lie
on opposite rays of the line through `0` of direction `theta`, so their oriented
arguments are exactly `theta` and `theta + pi`, with radii `A, B > 0` and
`A + B = 1` (Lemma 2 (i) with `delta = 0`). Hence
`rho(theta)^2 + rho(theta+pi)^2 >= A^2 + B^2 >= 1/2` by Lemma 2 (iv).

*The origin is an endpoint of `N_theta`.* Say `p_theta = 0`; then
`q_theta = ±e(theta)` has modulus `1` and argument `theta` or `theta + pi`, so
`rho(theta)^2 + rho(theta+pi)^2 >= 1 >= 1/2`.

In both cases, pointwise on `S^1`,

```text
rho(theta)^2 + rho(theta + pi)^2 >= 1/2 .
```

Let `G` be any measurable majorant of `rho^2` on `S^1` and set
`G~(phi) = G(phi) + G(phi + pi)` for `phi ∈ [0,pi)`. Then `G~` is measurable and
`G~ >= 1/2` everywhere, so `∫_{S^1} G = ∫_0^{pi} G~ >= pi/2`. Taking the infimum
over `G` gives `∫^* rho^2 >= pi/2`, i.e. `Cap2 >= pi/4`. `∎`

This is the *only* clean place where paired endpoints alone do the whole job,
and §8 shows it does not survive any perturbation of the hypothesis.

---

## 4. The dyadic contact relation and the Hall–Carleson candidate

The candidate this spike was asked to test, stated precisely.

**Tiles.** For `m >= 0` let `D_m` be the dyadic partition of `Tp` into `2^m`
arcs of length `pi 2^{-m}`, and `E_m` the dyadic partition of `S^1` into `2^m`
arcs of length `2 pi 2^{-m}`. Radial levels `r_k = 2^{-k}`, `k >= 1`.

**Contact relation.** For `I ∈ D_m`, `J ∈ E_m`, `k >= 1`,

```text
R_{k,m} := { (I,J) : ∃ theta ∈ I, ∃ u ∈ [0,1],
             |Gamma_theta(u)| ∈ [2^{-k}, 2^{-k+1}) and arg Gamma_theta(u) ∈ J } ,
```

split into the **endpoint part** (`u ∈ {0,1}`) and the **interior-contact part**
(`0 < u < 1`). Neighbourhood `N_{k,m}(S) = { J : (I,J) ∈ R_{k,m} for some I ∈ S }`.

**Candidate (Hall–Carleson alternative).** *There are absolute
`lambda, c > 0` such that for every star-shaped Kakeya set, every selector,
every `k` and every `m`, either*

```text
(Expansion)   |N^{endpoint}_{k,m}(S)| >= lambda |S|   for every union of tiles S,
```

*or the failure of expansion forces a quantitative interior-contact payment*

```text
(Payment)     Cap2 >= c · 2^{-2k} · |S| .
```

**Proposed functional.** `HC(E) = sum_k 2^{-2k} sum_{m} 2^{-m}
inf_{S ⊂ D_m} |N^{endpoint}_{k,m}(S)| / |S|`, i.e. a Carleson-type sum of the
Hall deficiencies of the endpoint relation over all direction scales.

§8 refutes the candidate: `(Expansion)` is vacuous on a legal family, so `HC`
carries no information, and `(Payment)` as stated cannot be derived because the
compressed set is a *full-measure* set of directions at *every* scale.

---

## 5. The engine: a sharp one-dimensional covering lemma

> **Lemma 7 (sliver covering; sharp).**
> Let `T` be `R` or a circle of length `L`, let `Theta ⊂ T`, and suppose that for
> each `theta ∈ Theta` we are given a nonempty bounded interval `W_theta ⊂ T`
> (a single point is allowed) with
>
> ```text
> dist(theta, W_theta) <= mu · |W_theta| ,        mu >= 0 fixed.
> ```
>
> Put `U = union_{theta ∈ Theta} W_theta`. Then
>
> ```text
> |Theta|*  <=  (1 + 2 mu) · |U|* .
> ```
>
> The constant `1 + 2 mu` is sharp.

*Proof.* Each `W_theta` is connected, hence contained in a unique connected
component `C(theta)` of `U`; components of a subset of `R` are intervals. Then
`dist(theta, C(theta)) <= dist(theta, W_theta) <= mu |W_theta| <= mu |C(theta)|`,
so `theta` lies in the closed `mu|C(theta)|`-neighbourhood of `C(theta)`.

Let `C` be the family of components of positive length. Distinct components are
disjoint intervals, so `C` is countable and `N := union C` is measurable with
`|N| = sum_{C ∈ C} |C| <= |U|*`. Split
`Theta = A ⊔ B`, `A = { theta : |C(theta)| > 0 }`, `B = Theta \ A`. For
`theta ∈ B` the component is the singleton `{theta}`, so `B ⊂ U \ N`.

For `A`: `A ⊂ union_{C ∈ C} C^{(mu|C|)}` and `|C^{(mu|C|)}| <= (1+2mu)|C|`
(equality on the line; on a circle the neighbourhood may wrap and saturate, in
which case it is strictly smaller, so the inequality is the correct statement).
Hence `|A|* <= (1+2mu) |N|`. Since `N` is measurable, Carathéodory splitting gives
`|U|* = |N| + |U \ N|* >= |N| + |B|*`. Therefore

```text
|Theta|* <= |A|* + |B|* <= (1+2mu)|N| + |B|* <= (1+2mu)(|N| + |B|*) <= (1+2mu)|U|* .
```

*Sharpness.* On a circle of length `L = k ell (1+2mu)` take `U` to be `k`
equally spaced intervals of length `ell` separated by gaps of length `2 mu ell`;
each point of a gap is within `mu ell` of an adjacent component, so the
hypothesis holds with `Theta = T`, and `|U| = L/(1+2mu)`. `∎`

**Independent falsification attempt.** `benchmark_capacity.py` runs a randomised
greedy adversary on a discretised circle (`N = 600` cells, periodic and full
seeds, 24 trials, `mu ∈ {0.1, 0.25, 0.5, 1, 2}`) searching for a feasible `U` of
density below `1/(1+2mu)`. Every solution that satisfies the exact continuum
budget `sum_C |C|(1+2mu) >= L` has density **exactly** `1/(1+2mu)`; the
apparent sub-optimal grid solutions all fail that budget and are discretisation
artefacts. Nothing falsified. (`RESULTS.json → sliver_covering_probe`.)

---

## 6. Theorem A: the radial sliver covering bound

This is the replacement for the refuted endpoint Hall–Carleson candidate. It
uses the **whole chord at every radial level**, never the endpoints alone, and
it has no measurability, continuity, boundedness or monotonicity hypothesis.

Notation, for each `theta ∈ Tp`:

```text
h(theta) = dist(0, aff N_theta),   m(theta) = dist(0, N_theta),
M(theta) = max_{x ∈ N_theta} |x|  ( >= 1/2  by Lemma 2(vi) ).
```

> **Theorem A (radial sliver covering).**
> Let `E` be a star-shaped Kakeya set about `0`, with an arbitrary needle
> selection. Let `0 < r < R < ∞` and put
>
> ```text
> Theta(r,R) = { theta ∈ Tp : m(theta) <= r  and  M(theta) >= R } .
> ```
>
> Then for every `r' < r`
>
> ```text
> | { phi ∈ S^1 : rho(phi) > r' } |*   >=   |Theta(r,R)|* · (R - r)/(R + r) .
> ```
>
> (The auxiliary `r'` is what makes the conclusion a statement about a strict
> super-level set; it is used in Corollary A1 with `r' = u` fixed and `r ↓ u`.)

*Proof.* Fix `theta ∈ Theta(r,R)` and drop it from the notation. Choose the
orientation of `e(theta)` so that the farthest point of the chord has positive
signed arclength. Parametrise the chord by signed arclength `tau` from the foot
`F` of the perpendicular from `0`, so `|Gamma(tau)|^2 = h^2 + tau^2` and
`tau` ranges over an interval `[t0, t0 + 1]` with `t1 := t0 + 1 > 0`.

On the branch `tau >= 0` the radius `x(tau) = sqrt(h^2 + tau^2)` is continuous
and increasing, it equals `m` at the left end of the branch (either `tau = 0`
with `x = h = m` when the foot is interior, or `tau = t0 > 0` with `x = m` when
the foot is exterior) and `M` at `tau = t1`. Since `m <= r < R <= M`, every
radius `x ∈ [r,R]` is attained on that branch at exactly one `tau(x) >= 0`.

*Case `h = 0`.* Then the point of radius `M` has argument `theta` modulo `pi`.
Set `W_theta = {theta} ⊂ Tp`; `dist(theta, W_theta) = 0`.

*Case `h > 0`.* Let `beta = arg F` and let `s ∈ {+1,-1}` be the orientation of
the frame `(F/h, e(theta))`. For a chord point of radius `x` on the branch
`tau >= 0`,

```text
arg Gamma(tau(x)) = beta + s · arctan( tau(x)/h )
                  = theta - s · arcsin( h / x )         (mod pi) ,
```

because `arg e(theta) = beta + s·pi/2`. Hence, projectively,

```text
W_theta := { theta - s · arcsin(h/x) : x ∈ [r,R] }
         = theta - s · [ arcsin(h/R), arcsin(h/r) ]
```

is a closed interval of `Tp` of length `d - d'`, at distance exactly `d'` from
`theta`, where `d = arcsin(h/r)` and `d' = arcsin(h/R)` (both defined because
`h <= m <= r`).

`arcsin` is convex on `[0,1]` and vanishes at `0`, so `arcsin(c y) <= c arcsin(y)`
for `c ∈ [0,1]`; with `c = r/R`, `y = h/r` this gives `d' <= (r/R) d`, whence in
both cases

```text
dist(theta, W_theta) / |W_theta|  <=  d' / (d - d')  <=  (r/R)/(1 - r/R) = r/(R-r) =: mu .
```

Every `phi ∈ W_theta` is the projective argument of a chord point of radius
`x ∈ [r,R]`; the corresponding oriented argument `phi^ ∈ S^1` therefore satisfies
`rho(phi^) >= x >= r > r'`. Let `W^_theta ⊂ S^1` be the set of these oriented
arguments; it is an interval of length `< pi/2`, projecting isometrically onto
`W_theta`, and `W^_theta ⊂ { rho > r' }`.

Apply Lemma 7 on the circle `Tp` (length `pi`) to `Theta(r,R)` and the intervals
`W_theta`:

```text
|Theta(r,R)|*  <=  (1 + 2 mu) · | union_theta W_theta |*
               =   ((R + r)/(R - r)) · | union_theta W_theta |* .
```

Finally `union_theta W_theta` is the image of `union_theta W^_theta` under the
`2:1` covering `S^1 → Tp`; splitting `S^1` into two measurable half-circles on
each of which the covering is an isometry and using Carathéodory,
`|union W_theta|* <= |union W^_theta|* <= |{rho > r'}|*`. `∎`

> **Corollary A1 (the constant).** Suppose the selection satisfies
> `m(theta) <= r0` for every `theta`, i.e. **every needle meets the closed disk
> `B(O, r0)`**, with `0 <= r0 < 1/2`. Then, taking `R = 1/2` (legitimate since
> `M >= 1/2` always) and `Theta(r, 1/2) = Tp` for every `r ∈ [r0, 1/2)`,
>
> ```text
> |{ rho > r }|*  >=  pi (1 - 2r)/(1 + 2r) ,          r0 <= r < 1/2 ,
> ```
> and therefore
> ```text
> L*(E) >= Cap2 >= pi ∫_{r0}^{1/2} r (1-2r)/(1+2r) dr
>                = pi [ r - r^2/2 - (1/2) log(1+2r) ]_{r0}^{1/2}
>                = pi ( 3/8 - (log 2)/2 - r0 + r0^2/2 + (1/2) log(1+2 r0) ) .
> ```
> In particular for `r0 = 0`
> ```text
> L*(E)  >=  ( 3/8 - (log 2)/2 ) pi  =  0.028426409720027...  pi .
> ```

*Proof.* Fix a level `u ∈ [r0, 1/2)`. For every `eps ∈ (0, 1/2 - u)` apply
Theorem A with the radial window `(r, R) = (u + eps, 1/2)` and with `r' = u`.
The hypothesis `m <= r0 <= u < u + eps` and `M >= 1/2 = R` (Lemma 2 (vi)) give
`Theta(u+eps, 1/2) = Tp`, hence

```text
|{ rho > u }|*  >=  pi (1/2 - u - eps)/(1/2 + u + eps) .
```

Now let `eps ↓ 0` in the (continuous, explicit) right-hand side — no continuity
of outer measure is used, since `u` is fixed and only the constant moves. This
gives `|{rho > u}|* >= pi (1-2u)/(1+2u)` for every `u ∈ [r0, 1/2)`. Insert into
the layer-cake inequality of Remark §1.2, restricting the integral to
`[r0, 1/2]`. The antiderivative is elementary:
`r(1-2r)/(1+2r) = (1-r) - 1/(1+2r)`. `∎`

> **Corollary A2 (ledger form).** For `r0 <= 0.1487420408...` the constant of
> Corollary A1 exceeds the published `131 pi/6250 = 0.020960 pi`. Numerically
> (`RESULTS.json → target_ledger`):
>
> | `r0` | coefficient `/pi` | ratio to `131/6250` | fraction of the certified ceiling |
> |---|---|---|---|
> | `0` | `0.0284264097` | `1.3562` | `0.3142` |
> | `1/32` | `0.0279770019` | `1.3348` | `0.3092` |
> | `1/16` | `0.0267710525` | `1.2772` | `0.2959` |
> | `1/8` | `0.0228106854` | `1.0883` | `0.2521` |
> | `0.1475` | `0.0210598823` | `1.0048` | `0.2328` |
> | `3/16` | `0.0177314003` | `0.8460` | `0.1960` |
> | `1/4` | `0.0124089638` | `0.5920` | `0.1371` |

**Scope discipline.** The hypothesis of Corollary A1 is *not* "bounded set",
*not* "confined direction class", *not* a radius split at some `R1`, and *not* a
measurability assumption. It is the single geometric condition **every needle
comes within `r0` of the star centre**. This class contains:

* the closed disk of radius `1/2` with its diameters (`r0 = 0`);
* every origin-crossing family (`r0 = 0`), where Theorem 3 gives the much better
  `pi/4`;
* the **certified near-extremizer** `E_n` of the production upper construction:
  its needles have `m(theta) = h(theta) = pi s(t)/n`, and the reconstruction
  measures `sup h = 1.318e-2, 6.657e-3, 3.345e-3, 1.677e-3, 8.394e-4` for
  `n = 51, 101, 201, 401, 801` (`RESULTS.json →
  finite_cell_reconstruction`), so `E_n ∈ C(r0)` with `r0 → 0`;
* the whole `kappa`-family of §8, and the astroid/sliding-ladder set (`r0 = 0`).

**Consistency with the certified ceiling.** `0.0284264 < 0.0904778`, so
Corollary A1 does not contradict the certified upper construction; it uses
`31.4%` of the available headroom. The near-extremizer is checked **level by
level** (`RESULTS.json → level_set_margins`; its `R` is nonincreasing on the
fundamental sector with `R(0) = 0.853553`, `R(1/2) = 0.228510`,
`R(1) = 0.146621`):

| `r` | Corollary A1 bound `|{rho>r}|/pi` | near-extremizer actual | slack |
|---|---|---|---|
| `0.05` | `0.818182` | `1.000000` | `0.181818` |
| `0.10` | `0.666667` | `1.000000` | `0.333333` |
| `0.146` | `0.547988` | `1.000000` | `0.452012` |
| `0.20` | `0.428571` | `0.625404` | `0.196833` |
| `0.25` | `0.333333` | `0.425653` | `0.092320` |
| `0.30` | `0.250000` | `0.297499` | `0.047499` |
| `0.40` | `0.111111` | `0.148968` | `0.037857` |
| `0.45` | `0.052632` | `0.104717` | `0.052086` |

Every level is satisfied, with minimum slack `0.037857`. The bound is within
`19%` of the truth at `r = 0.3` and within `34%` at `r = 0.25`; essentially all
of the remaining factor `3.2` in the integrated constant comes from the small-`r`
levels, where the near-extremizer has `rho >= 0.1466` everywhere while
Corollary A1 only asserts `(1-2r)/(1+2r)`.

**Sharpness.** Not claimed as a theorem, but measured. Besides the abstract
probe of §5, `benchmark_capacity.py` runs a *geometric* falsification attempt on
Theorem A itself: the adversary chooses `h(theta) ∈ [0,r]` and the side
`s ∈ {+1,-1}` freely per direction, the sliver keeps its **rigid** shape
`theta - s[arcsin(h/R), arcsin(h/r)]`, and the minimal density of a periodic
`U` serving every direction is located by bisection
(`RESULTS.json → theorem_a_geometric_probe`, `R = 1/2`):

| `r` | Theorem A density `(R-r)/(R+r)` | minimal feasible periodic density | slack |
|---|---|---|---|
| `0.05` | `0.818182` | `0.840690` | `0.022508` |
| `0.10` | `0.666667` | `0.698866` | `0.032200` |
| `0.20` | `0.428571` | `0.460955` | `0.032384` |
| `0.30` | `0.250000` | `0.272397` | `0.022397` |
| `0.40` | `0.111111` | `0.122308` | `0.011197` |

Nothing falsified, and the relative slack is only `2.8%`–`10.1%`. **The
remaining factor `3.2` to the certified ceiling therefore does not live in the
covering constant.** It lives in the three discards: (a) only the far-side
sliver is used, (b) all radial levels above `1/2` are thrown away, (c) the
`arcsin` convexity bound `d' <= (r/R) d`. §9 quantifies them.

---

## 7. Far needles

> **Proposition A3 (far branch).** Let `S ⊂ Tp` and suppose `m(theta) <= m1`,
> `M(theta) >= R1` for all `theta ∈ S`, with `0 < m1 < R1`. Then
> ```text
> Cap2  >=  |S|* · R1^2 · G(m1/R1) ,      G(lam) = ∫_lam^1 x(1-x)/(1+x) dx
>                                                = [2x - x^2/2 - 2 log(1+x)]_lam^1 .
> ```
> Moreover for every single `theta`, `Cap2 >= L*(Delta_theta) = h(theta)/2`, and
> `M^2 >= m^2 + 1/4` always, while `M^2 = m^2 + 2 sqrt(m^2 - h^2) + 1` when the
> foot is exterior.

*Proof.* Theorem A with `r` running over `[m1, R1]` and `R = R1`, then layer
cake; the triangle bound is the triangle reduction plus Theorem 1. The identities
are Lemma 2(vi) and its proof. `∎`

**Numbers** (`RESULTS.json → adversary_far_needles`), for the needle of direction
`theta` centred at `T e(theta) + eta nu(theta)`:

| `T` | `eta` | `m` | `M` | `lambda = m/M` | `R1^2 G(lambda)` per unit direction mass |
|---|---|---|---|---|---|
| `1` | `1e-3` | `0.5000` | `1.5000` | `0.3333` | `0.17541` |
| `2` | `1e-3` | `1.5000` | `2.5000` | `0.6000` | `0.21071` |
| `10` | `1e-3` | `9.5000` | `10.5000` | `0.90476` | `0.24177` |
| `100` | `1e-3` | `99.500` | `100.500` | `0.99005` | `0.24917` |

So a family of far needles **does not** evade the argument: pushing the needles
out drives `lambda → 1` but drives `R1^2` up faster, and the payment increases
towards `1/4` per unit direction mass. The only far configuration with a small
sliver payment is the *perpendicular* one, `h ≈ m`, and there the elementary
triangle bound `h/2 ≈ m/2` takes over.  The earlier draft treated a direct
class split as losing a factor `2`.  The disjoint radial-ledger assembly in
`UNIVERSAL-ONE-FIFTEENTH.md` supersedes that estimate and proves the
intermediate unconditional bound `L*(E) >= 1/15`; the optimized witness in
`UNIVERSAL-OPTIMIZED.md` strengthens it to the intermediate bound
`L*(E) >= 1717/25000`; the finite schedule in
`UNIVERSAL-SEVEN-HUNDREDTHS.md` gives the intermediate `L*(E) >= 7/100`, and
`UNIVERSAL-141-OVER-2000.md` certifies the explicit witness
`C_FS >= 141/2000`.
Corollary A1 remains the stronger class-scoped statement when every needle
meets a sufficiently small central disk.

---

## 8. Theorem NG: the endpoint Hall–Carleson candidate is dead

Two independent kills.

### 8.1 The endpoint-collapse family (kills the expansion branch)

Inside the Cunningham–Schoenberg cell family put, for `kappa ∈ [0,1]`,

```text
a(t) = kappa (1 - 2t)/2 ,     s(t) = gamma t(1-t) ,     gamma = (1 + kappa)/2 ,
H(t) = 1/2 + a(t) ,           J = H^2 - s'H + s H' .
```

`E_n^{(kappa)}` is the literal odd-cell set of the manuscript built from this
profile pair. It is compact, star-shaped about `0` and admissible for every odd
`n` (the proof of the manuscript's admissibility proposition uses only the
reflection identities `a(1-t) = -a(t)`, `s(1-t) = s(t)`, `s(0) = s(1) = 0`, all
of which hold here). `kappa = 1/sqrt 2` is the classical baseline.

Exact closed forms (derived in §S6 of `benchmark_capacity.py`, verified against
the reconstruction):

```text
endpoint-branch capacity  = ∫_0^1 J dzeta   = 1/4 + kappa^2/12 - gamma kappa/3
                                            = 1/4 - kappa/6 - kappa^2/12  ,
interior-branch capacity  = ∫ R_sta^2 dy    = 2 gamma^2 ( tau*^2/2 - tau*^3/3 ) ,
                                              tau* = sqrt 2 - 1 .
```

| `kappa` | endpoint branch | note |
|---|---|---|
| `0` | `0.250000` | centred chords; `pi/4` regime |
| `0.25` | `0.203125` | |
| `1/sqrt2 = 0.70711` | `0.0904822` | classical baseline; agrees with the reconstructed rational-seven value `0.0904778` |
| `0.85` | `0.048125` | |
| `0.95` | `0.016458` | already below `131/6250 = 0.020960` |
| `0.99` | `0.003325` | |
| `1` | `0.000000` | **total collapse** |

At `kappa = 1` one has `a(t) = (1-2t)/2`, `H(t) = 1 - t`, `s(t) = t(1-t)`, and

```text
J = H^2 - s'H + sH' = (1-t)[ (1-t) - (1-2t) - t ] ≡ 0 ,
```

so the leading-endpoint argument map `zeta ↦ y = zeta - s(zeta)/H(zeta) ≡ 0`
sends the **entire projective direction circle onto a single output angle**
inside each cell. Meanwhile the interior branch gives `0.124194`, and the
literal finite-cell reconstruction at `kappa = 0.99, n = 101` measures

```text
full chord capacity        = 0.123122   (per pi)
endpoints-only capacity    = 0.004593   (per pi)      < 131/6250 = 0.020960
```

(`RESULTS.json → mutations → MUT-2`).

> **Theorem NG-1.** There is a one-parameter family of compact admissible
> star-shaped Kakeya sets on which the endpoint contact relation has Hall
> expansion constant `lambda = 0` at every dyadic scale and the endpoint-only
> capacity tends to `0`, while `Cap2` stays above `0.123 pi`. Consequently:
> * no lower bound for `Cap2` can be derived from endpoint data alone;
> * the `(Expansion)` branch of the Hall–Carleson candidate of §4 is vacuous on
>   a legal family, so the candidate carries no information;
> * every universal constant must be extracted from interior chord contacts.

Even the *certified near-extremizer* is close to this degeneracy: its endpoint
Jacobian satisfies

```text
min_{zeta ∈ [0,1]}  J(zeta)/H(zeta)^2  =  0.0069530...
```

and the dyadic endpoint expansion constants are

| scale `m` | `lambda_m = min` dyadic expansion |
|---|---|
| `1` | `0.143936` |
| `2` | `0.059406` |
| `3` | `0.023105` |
| `4` | `0.010029` |
| `6` | `0.0071622` |
| `8` | `0.0069685` |
| `10` | `0.0069556` |
| `12` | `0.0069533` |

so the expansion branch is worth at most `0.7%` at fine scales even on the
near-extremizer. This is exactly why the mutation "coarsen one scale" flips the
verdict (`RESULTS.json → mutations → MUT-3`: `lambda_1 = 0.1439` versus
`lambda_12 = 0.0069533`, a factor `20.7`).

### 8.2 The defect is a derivative phenomenon (kills every `sup delta → 0` statement)

For the certified rational-seven construction `E_n`, Lemma 2 gives the exact
antipodal defect `delta(theta) = arcsin(h/A) + arcsin(h/B)` with
`h = pi s(t)/n`. Hence both `sup h` and `sup delta` are `O(1/n) → 0`, and the
leading-endpoint argument map satisfies
`| arg q_theta - theta | = arcsin(h/B) <= 2h → 0` **uniformly**. Nevertheless

```text
Cap2(E_n)/pi  =  0.090569, 0.090509, 0.090494, 0.090490, 0.090489
                 (n = 51, 101, 201, 401, 801, literal reconstruction, lower bounds)
             →  0.0904778111246769...   <<   1/4 .
```

> **Theorem NG-2.** There is no function `F` with `F(0) = 1/4` and `F`
> continuous at `0` such that `Cap2 >= pi F(sup_theta h(theta))` or
> `Cap2 >= pi F(sup_theta delta(theta))` for all star-shaped Kakeya sets.

The reason is structural and worth recording: the endpoint displacement
`theta ↦ arg q_theta - theta` is uniformly small, but its *derivative* is `O(1)`
because `h` oscillates at frequency `n`. Compression of the endpoint image is a
derivative phenomenon, invisible to any modulus-of-continuity hypothesis. This
also kills "continuous selectors suffice": the selector of `E_n` is real
analytic in `theta`.

### 8.3 Why Theorem A survives both kills

Lemma 7 is *scale free*: its hypothesis is a ratio `dist/length`, not a size.
In Theorem A the sliver `W_theta` is a positive-length interval whose length is
proportional to its distance from `theta`, for **every** `h > 0` however small,
and the degenerate `h = 0` case contributes the point `theta` itself. Neither
branch refers to endpoints: the sliver is cut out of the chord *interior* at the
radial window `[r,R]`. Concretely, on the endpoint-collapse family the endpoint
image is a single point but the level sets `{rho > r}` still obey
`|{rho > r}| >= pi(1-2r)/(1+2r)`, which the reconstruction confirms
(`Cap2 = 0.1231 pi > 0.0284 pi`).

---

## 9. Target ledger and what would be needed to go further

All numbers per `pi`; `RESULTS.json → target_ledger`.

```text
published lower bound                 0.020960          (131/6250)
certified upper ceiling               0.0904778120      (production continuum certificate)
reconstructed here (independent)      0.0904778111246790  (six-piece)
                                      [0.0904709089, 0.0904847186]  (monotone bracket, N = 51200)
head-room ratio                       4.3167x
Theorem A class-scoped, r0 = 0        0.0284264097      1.3562x published, 31.4% of ceiling
Theorem A class-scoped break-even r0  0.1487420408
```

**Ceilings of the individual routes** — a universal bound proved through route
`X` can never exceed the value of route `X`'s functional on the certified
near-extremizer:

| route | functional | value on the near-extremizer | verdict |
|---|---|---|---|
| endpoint-only capacity | `∫ J dzeta` | `0` on the `kappa → 1` family | **dead** (Theorem NG-1) |
| uniform radial floor `rho >= c` | `c^2` with `c = min R` | `c = 0.1466`, ceiling `0.021498` | at most `+2.6%` over published, and **false in general**: the origin-crossing family `Gamma_theta = [T e(theta), (T+1) e(theta)]`, `theta ∈ [0,pi)`, is a legal star-shaped Kakeya selection with `rho ≡ 0` on the whole half circle `[pi, 2pi)` |
| pointwise antipodal pair floor | `c/2` with `c = essinf_phi [rho(phi)^2+rho(phi+pi)^2]` | best universal `c=0` | **refuted** by far common-centre radial support; full-angle average is only capacity |
| radial sliver covering (Theorem A, class-scoped `m<=r0`) | `∫_{r0}^{1/2} r(1-2r)/(1+2r) dr` | proved `0.0284264` at `r0=0` | **live class-scoped corollary**, `1.3562x` published |
| radial sliver + forced near-side sliver | would require a universal improvement over `1+2mu` | former envelope `<=0.05685` | **refuted for arbitrary chords** by foot-at-endpoint side vanishing |

**Potential losses and resolved dead ends.**

1. **A universal two-sided covering gain is impossible.**  A legal unit chord
   may have its perpendicular foot at an endpoint.  For every window with
   `h<r<R<=sqrt(h^2+1)`, one radial-window side is then empty and the other is an
   arbitrary one-sided rigid sliver.  Hence the full two-sided admissible class
   contains the sharp one-sided microstructures, and no universal covering
   constant can improve on `1+2mu`.  The historical `0.056852 pi` figure assumed
   constant `1`; the later `0.037902 pi` proposal used an unproved constant and
   an incorrect variable-factor integration.  Neither is a valid bound from
   this mechanism.  See `TWO-SIDED-NO-GO.md` and the reproducible periodic
   adversary.
2. **Radial levels above `1/2` are discarded.** `R = 1/2` is the worst case
   `M = 1/2`, but `M = 1/2` forces `A = B = 1/2`, `delta = 0`, `h = 0`, which is
   exactly the `pi/4` regime. A trade-off lemma quantifying "`M` close to `1/2`
   implies `h` small implies the `h = 0` mechanism" should recover a further
   factor. *CONJECTURAL, no proof attempted.*
3. **`arcsin` convexity slack.** `d' <= (r/R) d` is an equality only as `h → 0`;
   for `h` comparable with `r` it is lossy. Bounded gain, `< 10%` on the
   near-extremizer's parameter range.

**Ceiling check.** The certified near-extremizer would numerically permit
`0.056852 pi`, but the universal two-sided covering mechanism needed to reach
it is refuted above.  The near-extremizer's former pair-floor value `0.052217`
is only a benchmark diagnostic; far common-centre sets force the universal
pointwise pair constant to zero.  No universal constant may exceed `0.0904778112`, and no claim above
`0.0214976` can follow from a uniform radial floor alone.

---

## 10. Statement inventory with quantifiers

```text
T1  ∀E star Kakeya ∀O ∀selector:            Cap2 = L*(Tri E) = inf_{open U ⊇ Tri E} |U| <= L*(E).
L2  ∀ unit chord:                            A^2+B^2+2AB cos d = 1 ; AB sin d = h ; A+B >= 1 ;
                                             A^2+B^2 >= 1/2 ; M >= 1/2 ; M^2 >= m^2 + 1/4.
T3  ∀E ∀selector with 0 ∈ N_theta ∀theta:    Cap2 >= pi/4 ; sharp.
L7  ∀T ∀Theta ∀{W_theta} with dist <= mu|W|: |Theta|* <= (1+2mu)|U|* ; sharp.
TA  ∀E ∀selector ∀ 0<r<R ∀r'<r:              |{rho>r'}|* >= |Theta(r,R)|* (R-r)/(R+r).
A1  ∀E ∀selector with m <= r0 < 1/2:         L*(E) >= pi ∫_{r0}^{1/2} r(1-2r)/(1+2r) dr.
A3  ∀S ⊆ Tp with m<=m1, M>=R1 on S:          Cap2 >= |S|* R1^2 G(m1/R1) ; and ∀theta Cap2 >= h(theta)/2.
NG1 ∃ legal family:                          endpoint Hall expansion ≡ 0 while Cap2 >= 0.123 pi.
NG2 ¬∃F cont. at 0 with F(0)=1/4:            Cap2 >= pi F(sup h) fails (E_n family).
NG3 ∃ legal foot-at-endpoint families:         every one-sided sharp sliver embeds in the full-chord class;
                                                no universal two-sided covering factor beats 1+2mu.
NG4 ∃ far common-centre convex Kakeya sets:     rho(phi)=rho(phi+pi)=0 on a positive-measure interval;
                                                pointwise/a.e./essinf/local antipodal floors have best constant zero.
```

Boundary cases explicitly covered by the proofs above: `h = 0` (degenerate
sliver, handled by the singleton branch of Lemma 7); foot exterior (the branch
`tau >= 0` still realises every radius in `[m,M]`); `M = ∞` / unbounded sets
(Theorem A never uses boundedness); non-measurable `rho`, `Theta`, `U` (outer
measures and Carathéodory splitting throughout); atomic endpoint marginals (no
endpoint is used in Theorem A); `Cap2 = ∞` (all inequalities are in `[0,∞]`).

**Resolved no-go / still open.** A universal two-sided improvement over Lemma 7
is refuted when side vanishing is allowed; see `TWO-SIDED-NO-GO.md`.  Pointwise
and local antipodal floors are also refuted; see `ANTIPODAL-FLOOR-NO-GO.md`.
Still open is the `M`-close-to-`1/2` trade-off through a mechanism that does not
double-count cross-direction sliver overlap.

---

## 11. Unconditional finite-schedule assembly

The earlier versions of this note stopped first at the class-scoped Corollary A1
and then at individual rational schedules.  Optimising over the entire family of
admissible finite schedules gives an exact variational constant.

> **Theorem V (exact finite-schedule variational bound).** For every
> star-shaped Kakeya set, with no measurability, continuity, boundedness, or
> selector regularity hypothesis,
> ```text
> L*(E) >= C_FS >= 141/2000 = 0.0705.
> ```

The exact definition of `C_FS` and the proof that every finite schedule is valid
for arbitrary selectors are in `FINITE-SCHEDULE-VARIATIONAL.md`.  For each fixed
closest-radius partition, `FIXED-PARTITION-WATERFILLING.md` solves the inner
radius/switch max--min globally by a monotone water-level frontier.  The quantity
`C_FS` is then the supremum over all finite partitions, not a rational closed
form.  The optimized 32-segment schedule in
`UNIVERSAL-141-OVER-2000.md`, checked by `certify_141_over_2000.py`, supplies the
certified witness `C_FS >= 141/2000`.

Floating-point local optimisers and a formal singular BVP suggest a continuum
candidate near `0.0705668`, but this is not a validated enclosure or a proved
approximation of `C_FS`.  Establishing that identification requires global
finite-dimensional upper bounds and a discrete-to-continuum theorem.

The finite Choquet-cover lemma aggregates every fixed finite schedule without
measurable-selection or continuum-Fubini assumptions; disjoint high ledgers
handle the unbounded closest-radius tail.
