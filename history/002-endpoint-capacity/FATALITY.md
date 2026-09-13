# FATALITY.md — adversarial models for the endpoint-paired capacity programme

Date: 2026-08-03 · companion to `THEORY.md` · numbers from `RESULTS.json`

Every entry below is a **concrete configuration with a calculation**, not a
prose objection. Each entry names the lemma it kills and gives the number that
kills it. Sections marked **SURVIVES** record what the surviving statement of
`THEORY.md` does on that configuration.

Normalisation throughout: capacities are reported divided by `pi`, so the
published lower bound is `0.020960` and the certified upper ceiling is
`0.0904778120`.

---

## F0. Index

| # | model | kills |
|---|---|---|
| F1 | centred radial disk, `h ≡ 0` | nothing; it is the sharp case of Theorem 3 and pins `pi/4` |
| F2 | sliding ladder / astroid | every endpoint-marginal functional (endpoint arguments are 4 atoms) |
| F3 | certified rational-seven `E_n`, `sup h → 0` | every `F(sup h) → pi/4` or `F(sup delta) → pi/4` statement; every "continuous selector suffices" statement |
| F4 | endpoint-collapse family `kappa → 1` | the Hall–Carleson endpoint expansion branch; the uniform radial floor; every endpoint-only functional |
| F5 | far needles, origin crossings, far common-centre disk | naive far-endpoint readings; uniform radial floor; pointwise/a.e./local antipodal floors; perpendicular needle kills sliver branch alone |
| F6 | discontinuous and multiscale-nested selectors | closed-graph / extremum-of-the-chosen-family arguments; single-scale Hall tests |
| F7 | null-fibre a.e. relaxation | every LP/continuum relaxation whose constraints are imposed a.e. in the output angle |
| F8 | naive `L^2` overlap energy | the Córdoba-logarithm and degenerate-triangle route |
| F8b | foot-at-endpoint sliver family | every universal two-sided covering improvement over `1+2mu` |

---

## F1. Centred radial disk (`h ≡ 0`)

**Model.** `E = closed disk of radius 1/2`, `N_theta` = the diameter of
direction `theta`. Then `p_theta = -e(theta)/2`, `q_theta = +e(theta)/2`,
`h ≡ 0`, `A = B = 1/2`, `delta ≡ 0`, `rho ≡ 1/2`.

**Calculation.** `Cap2 = (1/2) ∫_{S^1} (1/2)^2 dphi = pi/4`; `L*(E) = pi/4`.
Lemma 2 gives `A^2 + B^2 = 1/2` exactly, so Theorem 3's inequality
`rho(phi)^2 + rho(phi+pi)^2 >= 1/2` is an equality everywhere.

**Verdict.** Not a fatality: it certifies that `pi/4` in Theorem 3 is sharp and
that `A^2+B^2 >= 1/2` (Lemma 2 (iv)) cannot be improved.

**Trap it sets.** It is tempting to read F1 as "chords are essentially
diameters when `h` is small". F3 shows this is false: the reachable value drops
by a factor `2.76` while `sup h → 0`.

---

## F2. Sliding ladder / astroid: atomic endpoint marginals

**Model.** For `sigma ∈ (0, pi/2)` take the unit segment from `(cos sigma, 0)`
to `(0, sin sigma)`; reflect into the four quadrants to cover all directions.
`E` = star hull about `0` of this family = the astroid region
`x^{2/3} + y^{2/3} <= 1`.

**Calculation.** Radial function
`rho(phi) = max_sigma [ cos phi/cos sigma + sin phi/sin sigma ]^{-1}
          = ( cos^{2/3}phi + sin^{2/3}phi )^{-3/2}` on the first quadrant;
`rho(pi/4) = 1/2`, `rho(0) = 1`. Area `= 3 pi/8`.

Reconstruction (`RESULTS.json → adversary_astroid`, `6000 x 6000` grid):

```text
normalised capacity  = 0.37498542      (exact value 3/8 = 0.375)
rho_min = 0.50000077,  rho_max = 0.98007
```

**The kill.** Every endpoint of every retained chord has argument in
`{0, pi/2, pi, 3pi/2}`: **exactly four atoms**. Therefore

```text
| { arg p_theta : theta } ∪ { arg q_theta : theta } |  =  0 ,
```

and any functional built from the *distribution of endpoint arguments* — in
particular any endpoint-marginal or endpoint-difference-set functional, and the
"endpoint image expands" branch of §4 — evaluates to `0` while the true capacity
is `0.375`. The entire capacity is carried by chord interiors.

**Which lemma dies.** Endpoint marginals and difference sets discard pairing and
discard the interior; on F2 they are identically zero. This is fatal control 2,
realised concretely.

**SURVIVES.** Theorem A never mentions endpoints. Here `m(theta) = dist(0,
Gamma)` is the distance from the origin to the ladder and can reach `1/2`, so
the strict class-scoped Corollary A1 with a fixed `r0<1/2` does not apply
verbatim.  The underlying level-set inequality is nevertheless comfortably
satisfied directly: since `rho >= 1/2` everywhere, at `r=1/4` the Theorem-A
bound is `pi/3` while the actual angular level-set measure is `pi`.

---

## F3. The certified high-frequency finite-cell construction

**Model.** The manuscript's rational-seven set `E_n` (odd `n`), rebuilt here
from the profile displays only:

```text
a(t) = (1-2t) sqrt2/4 + (1/5) t(1-t) A(2t-1),   A(v) = -7/80 v + 1/9 v^3 - 1/160 v^5
s(t) = t(1-t) (2+sqrt2)/4 (1 + B(2t-1)/5),      B(v) = 1/68 - 41/120 v^2 + v^4 - 20/27 v^6
c_0(t) = a(t) u(t) + (pi s(t)/n) nu(t),         H = 1/2 + a .
```

**Independent reconstruction** (`RESULTS.json`; no production module imported):

```text
six-piece identity          int_0^1 R(y)^2 dy = 0.0904778111246790
monotone bracket (N=51200)  [0.0904709089, 0.0904847186]
production strict upper                        0.090477812
manuscript reported decimal                    0.0904778111246769545
difference (six-piece - reported)              +2.0e-15
active branch pattern                          e s e s e s   (5 switches, as printed)
```

Literal finite-cell radial reconstruction (pure chord geometry, no branch
classification used):

| `n` | normalised area (sampled lower bound) | `sup h` |
|---|---|---|
| `51` | `0.090569` | `1.318e-2` |
| `101` | `0.090509` | `6.657e-3` |
| `201` | `0.090494` | `3.345e-3` |
| `401` | `0.090490` | `1.677e-3` |
| `801` | `0.090489` | `8.394e-4` |

**The kill.**

```text
sup_theta h(theta)  →  0        and       sup_theta delta(theta)  →  0
but   Cap2/pi  →  0.09047781    <<    1/4 .
```

So the map `sup h ↦ Cap2` has no continuity at `0` compatible with the `h = 0`
value `pi/4`: the ratio is `0.36194`, i.e. a **factor `2.7627` collapse at
arbitrarily small height** (fatal control 1, restated in the paired-chord
language of Lemma 2).

Moreover the leading-endpoint argument map obeys
`|arg q_theta - theta| = arcsin(h/B) <= 2h → 0` *uniformly*, and the selector of
`E_n` is real analytic in `theta`. Hence:

* **no modulus-of-continuity hypothesis on the selector helps** (fatal control 3);
* the compression is a **derivative** phenomenon: the pushforward Jacobian of
  the endpoint map is `J/H^2` and

```text
min_zeta J(zeta)/H(zeta)^2 = 0.0069530
```

  while the displacement itself is `O(1/n)`.

**Dyadic endpoint expansion of the near-extremizer** (`RESULTS.json → spectra`):

| `m` | 1 | 2 | 3 | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|---|
| `lambda_m` | `0.14394` | `0.05941` | `0.02311` | `0.01003` | `0.007162` | `0.006969` | `0.006956` | `0.006953` |

**Far-endpoint image collision.** The leading far endpoints (`H > 1/2`) occupy
`[0, 0.0719681]` of the fundamental sector and the trailing far endpoints
occupy the reflected `[0, 0.9280319]`; the images **overlap on `0.0719681`**,
i.e. the leading-far image is contained in the trailing-far image. A paired
endpoint functional double counts exactly this mass.

**Which lemma dies.** (a) any `Cap2 >= pi F(sup h)`/`F(sup delta)` with
`F(0)=1/4` continuous at `0`; (b) any selector-regularity route; (c) any
single-scale Hall test (see MUT-3).

**SURVIVES.** Theorem A gives `|{rho > r}| >= pi(1-2r)/(1+2r)`; at `r = 1/4`
this is `0.3333 pi` versus the actual `0.45 pi`, at `r = 0.4` it is `0.1111 pi`
versus `0.25 pi`, at `r = 0.1` it is `0.6667 pi` versus `pi`. Corollary A1 with
`r0 = sup h → 0` yields `0.0284264 pi <= 0.0904778 pi`: consistent, with a
margin factor `3.18`.

---

## F4. The endpoint-collapse family (the decisive kill)

**Model.** In the same odd-cell machinery take

```text
a(t) = kappa (1-2t)/2 ,     s(t) = ((1+kappa)/2) t(1-t) ,     kappa ∈ [0,1] .
```

Reflection identities `a(1-t) = -a(t)`, `s(1-t) = s(t)`, `s(0) = s(1) = 0` hold,
so the assembled odd-cell set `E_n^{(kappa)}` is compact, star-shaped about `0`
and carries a continuous turning needle: it is a **legal admissible star-shaped
Kakeya set** for every odd `n` and every `kappa ∈ [0,1]`.

**Closed forms** (`RESULTS.json → adversary_endpoint_collapse`):

```text
endpoint capacity  = int_0^1 J dzeta  =  1/4 - kappa/6 - kappa^2/12
interior capacity  = int R_sta^2 dy   =  2 gamma^2 (tau*^2/2 - tau*^3/3),  tau* = sqrt2 - 1
```

| `kappa` | endpoint capacity | vs published `0.020960` |
|---|---|---|
| `0` | `0.250000` | `11.9x` |
| `0.25` | `0.203125` | `9.7x` |
| `1/sqrt2` | `0.0904822` | `4.32x` (this is the classical baseline; it reproduces the rational-seven value `0.0904778` to `5e-6`) |
| `0.85` | `0.0481250` | `2.30x` |
| `0.95` | `0.0164583` | **`0.785x` — already below** |
| `0.99` | `0.0033250` | `0.159x` |
| `1` | `0.0000000` | `0` |

**The kill, exactly.** At `kappa = 1`: `H(t) = 1-t`, `s(t) = t(1-t)`, and

```text
J = H^2 - s'H + s H' = (1-t)[(1-t) - (1-2t) - t] ≡ 0 ,
y_endpoint(zeta) = zeta - s(zeta)/H(zeta) = zeta - zeta ≡ 0 .
```

The leading-endpoint argument map sends **the entire projective direction circle
onto a single output angle per cell**. Therefore the Hall neighbourhood of *any*
set of direction tiles is a single tile:

```text
|N^{endpoint}_{k,m}(S)| / |S|  =  0     for every S, every k, every m .
```

The `(Expansion)` branch of the §4 candidate is **vacuous**, and the `(Payment)`
branch cannot be triggered by "compression of a small set" because the
compressed set is the *whole* direction circle at *every* scale.

Meanwhile the set is not small:

```text
interior capacity at kappa = 1                     0.124194
literal finite-cell reconstruction, kappa = 0.99, n = 101:
    full-chord capacity                            0.123122
    endpoints-only capacity                        0.004593   ( < 0.020960 )
```

**Which lemmas die.**

1. **Hall–Carleson endpoint alternative (§4)** — dead, Theorem NG-1.
2. **Every endpoint-only capacity functional** — value `0` on a legal family.

The **uniform radial floor** `rho >= c` is *not* killed here: along this family
`min_y R(y) = max((1-kappa)/2, gamma(3 - 2 sqrt2)) → 0.171573 > 0`. It is killed
instead by F5-OC below (`rho ≡ 0` on a half circle). Its ceiling on the certified
near-extremizer is `c^2 = 0.021498`, only `+2.6%` over the published constant
even if it were true.

**SURVIVES.** Theorem A: the level sets of the collapse family still obey the
sliver bound, and the measured capacity `0.1231 pi` exceeds the guaranteed
`0.0284 pi` by a factor `4.33`.

---

## F5. Far needles and origin crossings

**Model FN.** The needle of direction `theta` is centred at
`T e(theta) + eta nu(theta)` with `T` large and `eta` tiny. Then
`h = eta`, `A = |T - 1/2|`-ish, `B ≈ T + 1/2`, `m = A`, `M = B`.

**Naive reading and why it is wrong.** All far endpoints can be crowded into a
thin cone (for `|z| = 10` a full `174.3` degrees of projective directions admit
`z` as their *far* endpoint, since `|z - e(theta)| < |z|` whenever
`e(theta)·z > 1/2`). Reading the capacity off far endpoints alone therefore
suggests `Cap2 ≈ 0`. The truth is the opposite: the triangles
`conv(0, Gamma_theta)` are long thin cones and their union sweeps the whole
circle.

**Calculation** (`RESULTS.json → adversary_far_needles`, Proposition A3 with
`G(lam) = [2x - x^2/2 - 2 log(1+x)]_lam^1`):

| `T` | `m` | `M` | `lam = m/M` | payment `M^2 G(lam)` per unit direction mass |
|---|---|---|---|---|
| `1` | `0.5000` | `1.5000` | `0.33333` | `0.17541` |
| `2` | `1.5000` | `2.5000` | `0.60000` | `0.21071` |
| `10` | `9.5000` | `10.5000` | `0.90476` | `0.24177` |
| `100` | `99.500` | `100.500` | `0.99005` | `0.24917` |

So the payment **increases** towards `1/4` per unit direction mass as the
needles recede. Far needles are the most expensive configuration, not the
cheapest.

**The one configuration that does defeat the sliver branch alone.** The
*perpendicular* far needle: the foot is at an endpoint, `h = m`, `M^2 = m^2 + 1`.
Then `1 - lam = 1 - m/sqrt(m^2+1) ≈ 1/(2m^2)` and `M^2 G(lam) ≈ 1/(16 m^2) → 0`.
This defeats the sliver branch by itself, but the elementary
triangle bound `Cap2 >= h(theta)/2 = m/2 → ∞` (Proposition A3, second clause).
The earlier draft treated their combination as losing a factor `2`; the
pairwise-disjoint radial-ledger assembly in
`UNIVERSAL-ONE-FIFTEENTH.md` supersedes that conclusion and proves the
intermediate unconditional bound `L*(E) >= 1/15`; parameter optimization in
`UNIVERSAL-OPTIMIZED.md` strengthens it to the intermediate bound
`L*(E) >= 1717/25000`; the first finite shared schedule in
`UNIVERSAL-SEVEN-HUNDREDTHS.md` gives the intermediate `7/100`, and the
32-segment schedule in `UNIVERSAL-141-OVER-2000.md` certifies `141/2000`;
optimising over all finite schedules defines the exact headline `C_FS` in
`FINITE-SCHEDULE-VARIATIONAL.md`.

**Model OC (origin crossing, `h = 0` with the origin outside the segment).**
`Gamma_theta = [ (T) e(theta), (T+1) e(theta) ]` with `T > 0`. Then `h = 0`,
`delta = pi`, `A = T`, `B = T+1`, `B - A = 1` and Lemma 2 (i) reads
`(B-A)^2 = 1`. Both endpoints have the **same** argument `theta`; nothing sits
at `theta + pi`. Theorem 3 does **not** apply (its hypothesis is `0 ∈ N_theta`,
not `h = 0`), and indeed `rho(theta + pi) = 0` for every `theta`. The degenerate
branch of Theorem A's proof still applies: `h = 0`, `m = T`, `M = T+1`, and the
point of radius `T+1` has argument exactly `theta`, so `W_theta = {theta}` and
`{rho > r} ⊇ [0,pi)` for every `r < T+1`. Hence `|{rho > r}| >= pi` on the whole
range and `Cap2 >= pi (T+1)^2 / 2` (which is the exact value: the star hull is
the closed half disk of radius `T+1`).

**Which lemmas die.**

1. Any statement of the form "`h ≡ 0` implies `Cap2 >= pi/4`" without the
   hypothesis `0 ∈ N_theta`. `THEORY.md` Theorem 3 states the hypothesis
   correctly.
2. **The uniform radial floor** `rho >= c` for a universal `c > 0`. Taking
   `Gamma_theta = [T e(theta), (T+1) e(theta)]` for every `theta ∈ [0,pi)`
   gives a legal star-shaped Kakeya selection (star hull = closed half disk of
   radius `T+1`) whose radial function vanishes identically on the half circle
   `[pi, 2pi)`. So `min_phi rho(phi) = 0` on a set of measure `pi`, and the
   floor route is false however small `c` is chosen. Its ceiling on the
   certified near-extremizer is only `0.021498`, i.e. `+2.6%` over the published
   constant, so the route was never worth much anyway.
3. **The pointwise/a.e./essential-inf antipodal pair floor**
   `rho(phi)^2 + rho(phi+pi)^2 >= c` for a universal `c > 0`.  Model OC does
   not kill it, but the far common-centre variant does: take every direction's
   unit chord centred at `P_R=(R,0)` and then its radial hull.  The needle union
   is `B(P_R,1/2)`, whose angular support from the origin is the cone
   `|phi|<=asin(1/(2R))`.  On the complementary positive-measure projective
   interval both antipodal radial values are zero.  As `R->infinity` the nonzero
   support shrinks to zero, also killing fixed quantiles and fixed local
   averages.  See `ANTIPODAL-FLOOR-NO-GO.md`.

---

## F6. Discontinuous and multiscale-nested selectors

**Model D (two-centre selector).** Let `E` contain, for every direction, needles
from two distinct admissible support lines with a common small height (two
tangential centres `c_0 ≠ c_1`). Select the `c_0` needle at rational chart
directions and the `c_1` needle at irrational ones. This is a legal Kakeya
selection. Its support centre, its trace endpoints and in general its first
arc are discontinuous at every point, and for a target arc `Gamma` separating
the two trace configurations, the pullback `J_Gamma` is a dense non-closed set.

**Which lemma dies.** Any argument that (i) asserts continuity of
`theta ↦ N_theta`, (ii) asserts closedness of a pullback of the chosen family,
or (iii) takes an extremum of the *chosen* family. (This reproduces the
already-recorded verdict of `materials/.../02-audit/ENDPOINT-FATALITY.md` in the
capacity language; it is not new here, and it is not used by anything in
`THEORY.md`.)

**Model N (multiscale nesting).** Overlay two frequencies: use the cell profile
of F3 at frequency `n` on a set `S` of directions and at frequency `n^2` on the
complement, choosing `S` non-measurable (a Bernstein set). Endpoint images at
scale `2^{-m}` then behave like frequency `n` for `m << log n` and like
frequency `n^2` for `m >> log n`; no single scale sees both.

**The kill, measured on the certified near-extremizer**
(`RESULTS.json → mutations → MUT-3`):

```text
Hall expansion at the coarse scale m = 1   :  lambda = 0.143936     (verdict: expands)
Hall expansion at the fine scale   m = 12  :  lambda = 0.0069533    (verdict: compressed)
ratio                                      :  20.66
```

A Hall alternative certified at any fixed scale is therefore *not* valid at
finer scales, even on a real analytic single-frequency selector. With genuine
multiscale nesting the gap can be made arbitrarily large.

**SURVIVES.** Theorem A is applied at each radial level independently and its
covering lemma is scale free (its hypothesis is the ratio `dist/length`), so no
scale selection is ever made and non-measurability of `S` is absorbed by outer
measures.

---

## F7. Null-fibre a.e. relaxation

**Model.** Replace the pointwise constraint "`rho(arg x) >= |x|` for every chord
point `x`" by its a.e.-in-`phi` relaxation, as any continuum LP over the output
angle would.

**The kill.** In the `h ≡ 0` class, every chord meets every circle
`|x| = r <= 1/2` in exactly two points, so the constraint set attached to a
single direction is a **two-point, hence null, fibre** of the output-angle
variable. Discarding null sets makes the whole constraint family vacuous and

```text
relaxed infimum  =  0        while    true value  >=  1/4    (Theorem 3).
```

More generally on the rational-seven near-extremizer the relaxed value is `0`
against a true `0.09047781`. This is fatal control 4, realised.

**Which lemma dies.** Every LP/continuum-relaxation route that imposes its
constraints a.e. in the output angle. Note also the reporting rule this
enforces: *a finite-grid LP value is never a continuum lower bound* unless the
grid cells are enclosed outward in both the direction and the state variable.
Nothing in `THEORY.md` uses an LP.

**SURVIVES.** Theorem 1 is an identity between outer measures, and Theorem A
uses only outer measures and Carathéodory splitting; no fibre is ever discarded,
and the degenerate `h = 0` fibre is exactly the singleton branch of Lemma 7.

---

## F8. Raw `L^2` overlap energy

**Model.** The classical route bounds `L*(E)` from below by
`( ∫ |Delta_theta| dtheta )^2 / ∫∫ |Delta_theta ∩ Delta_theta'| dtheta dtheta'`.

**The kill, two ways.**

1. *Córdoba logarithm.* For the near-extremizer the triangles have height
   `h ≈ pi s/n` and are essentially the cones over the chords; the overlap of
   two such cones at angular separation `psi` behaves like
   `min(h, h^2/psi) x O(1)`, so
   `∫∫ |Delta ∩ Delta'| ~ h^2 log(1/h)` while `(∫|Delta|)^2 ~ h^2`. The bound
   therefore degrades by `1/log(1/h)` and tends to `0` as `n → ∞`, whereas the
   truth is constant `0.0904778 pi`.
2. *Degenerating triangles.* Any family with `h → 0` has
   `∫ |Delta_theta| dtheta = pi h/2 → 0`, so the numerator vanishes while the
   capacity does not. Concretely on `E_801`: `∫|Delta| dtheta <= pi ·
   8.394e-4/2 = 1.32e-3`, against a capacity of `0.2843`, a factor `215`.

**Which lemma dies.** Any bound whose numerator is the *sum of triangle areas*.
This is fatal control 5.

**SURVIVES.** Theorem A never sums triangle areas; the sliver of a chord at
radial level `r` has angular length `arcsin(h/r) - arcsin(h/R)`, which is
proportional to `h` — but so is the covering interval `[theta - d, theta + d]`,
and Lemma 7 only sees their *ratio*. This is precisely why the argument is
insensitive to `h → 0`.

---

## F8b. Foot-at-endpoint family: two-sided covering collapses to one-sided

For every projective direction `theta`, choose a physical unit chord

```text
N_theta = { s h n_theta + t eps e_theta : 0 <= t <= 1 },
```

with `0 <= h < r < R <= sqrt(h^2+1)` and freely chosen signs.  The
perpendicular foot is the endpoint at radius `h<r`; hence its radial-window
side is empty.  The other endpoint has radius `sqrt(h^2+1)>=R` and produces
exactly one rigid sliver

```text
theta - sigma [asin(h/R), asin(h/r)]
```

with either sign `sigma`.  Thus every one-sided sliver family, including its
sharp periodic microstructures, embeds into the full unit-chord class even
when the formulation nominally retains both sides.

**The kill.** Any universal two-sided covering constant is at least the
one-sided sharp constant `1+2mu`.  In particular constants `1` and
`(1+2mu)/(1+mu)` are false without an additional uniform hypothesis excluding
side vanishing.  The former candidate `0.056852*pi` and the later
`0.037902*pi` calculation are therefore not lower bounds from this mechanism.
See `TWO-SIDED-NO-GO.md` and `two_sided_sliver_adversary.py`.

---

## F9. Mutation ledger (each mutation must visibly change or reject a check)

From `RESULTS.json → mutations`. Gate is the published constant `0.020960`
unless stated.

| mutation | quantity | before | after | verdict flips? |
|---|---|---|---|---|
| **MUT-1 remove pairing** — replace `A^2+B^2 >= 1/2` by the unpaired marginal `max(A,B) >= 1/2` | sharp constant of the `h ≡ 0` class | `0.250000` | `0.125000` | **yes**, factor `2`. Secondary witness: dropping the trailing endpoint family of `E_101` moves the pair floor `0.104459 → 0.103946` (the near-extremizer is pairing-symmetric, so it is a weak witness); decisive witness is the astroid (F2), where the endpoint-only value is `0` against `0.375`. |
| **MUT-2 remove interior contacts** — keep only the two chord endpoints | capacity of the legal collapse family `kappa = 0.99`, `n = 101` | `0.123122` (full chord) | `0.004593` (endpoints only) | **yes**, verdict `pass → fail`. Closed form: endpoint branch `→ 0` at `kappa = 1`, interior branch `= 0.124194`. |
| **MUT-3 coarsen one scale** — evaluate the Hall expansion at `m = 1` instead of `m = 12` | `lambda_m` on the certified near-extremizer, gate `lambda > 0.1` | `0.0069533` (fine, fails) | `0.143936` (coarse, passes) | **yes**, ratio `20.66` |
| **MUT-4 null-fibre a.e. constraints** — impose the fibre constraint a.e. in `phi` | value of the relaxation | `0.0904778` (exact) / `0.25` (`h ≡ 0`) | `0.000000` | **yes**, total collapse |

---

## F10. What is left standing

Four mechanisms survive every model above:

1. **Paired endpoints, but only when `delta ≡ 0`** — Theorem 3, sharp `pi/4`,
   killed by any positive height (F3).
2. **Interior chord contacts organised by a scale-free covering argument** —
   Lemma 7 + Theorem A, with the stronger class-scoped constant
   `(3/8 - (log 2)/2) pi = 0.0284264 pi`.
3. **Disjoint radial ledgers across closest-radius classes** — the intermediate
   assemblies in `UNIVERSAL-ONE-FIFTEENTH.md` and `UNIVERSAL-OPTIMIZED.md`,
   reaching `1717/25000` for arbitrary selectors.
4. **Finite shared low-radius schedules plus disjoint high ledgers** — the exact
   variational supremum `C_FS` in `FINITE-SCHEDULE-VARIATIONAL.md`, with
   certified witness `C_FS >= 141/2000`.

The endpoint-paired Hall–Carleson programme as originally posed is **dead**
(F4), but the interior-contact radial-sliver replacement is now universal.
The stronger `0.0284264 pi` constant still requires every selected needle to
meet `B(O,r0)` with `r0` sufficiently small; the unconditional schedule theorem
does not inherit that stronger constant.
