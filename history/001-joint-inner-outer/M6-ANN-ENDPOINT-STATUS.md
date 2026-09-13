# M6 — annular endpoint package and confined exit: branch status

Worktree `star-kakeya-wt-joint-lower` (MAIN research worktree), baseline HEAD
`0f88d45` ("refactor(lower): parameterize endpoint contact geometry"), which
already carries the reviewed numeric kernel (`AnnularKernel`), the reviewed
radial integral certificate (`AnnularCaseIIntegral`) and the generic endpoint
refactor (`Figure5EndpointDomain` / `EndpointConfinedExit`).

**Nothing is committed**; this report describes the working tree, which is left
uncommitted for independent review. No sibling worktree was touched.

**Result: green.** `lake build` (production root) and
`lake build StarKakeyaLowerAudit` both succeed with no errors and no warnings
attributable to the new module. Every new `#print axioms` receipt is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` anywhere.

---

## 0. Scope executed / not executed

Executed, exactly the requested M6 endpoint/confined closure:

1. `annFigure5Domain : Figure5EndpointDomain` at `(annA, annR₀, annR₁, annPaperG)`.
2. Dominations (A) `strongInteriorRatio ≤ annPaperG` and (B)
   `strongLargeAngleRatio ≤ annPaperG`, definitionally + `le_max_*`.
3. The single deep gate `ann_base_ray_gap`, stated verbatim as the
   `base_ray_gap` package field.
4. `annFigure5AnalyticPackage` via `Figure5EndpointAnalyticPackage.of_dominations`.
5. `annular_confined_lower_bound`, unconditional on the geometry and
   conditional only on the no-high-needle branch.

**Not executed, deliberately:** M7 final mass assembly (the greedy/exterior
side, the Carathéodory split, and the `π · annTarget` statement). No exterior
gate, no mass split and no `annTarget` inequality is touched here, and
`annTarget` was **not** weakened. `base_ray_gap` was **not** assumed anywhere.

---

## 1. The new module

`StarKakeyaLower/AnnularEndpoint.lean` (new, 428 lines).

```lean
import StarKakeyaLower.AnnularCaseIIntegral   -- ⊃ AnnularKernel ⊃ Mathlib
import StarKakeyaLower.EndpointConfinedExit
```

### 1.1 Import closure is CLEAN

Mechanical DFS over all 53 modules of the library:

| module | transitive `StarKakeyaLower.*` deps | `StrongerKernel` / `Figure5FrozenPackage` / `CaseIEndpoint*Analytic` |
|---|---|---|
| `AnnularEndpoint` | 26 | **none** |
| `EndpointConfinedExit` | 23 | none |
| `AnnularCaseIIntegral` | 1 | none |
| `AnnularKernel` | 0 | none |
| `Figure5EndpointDomain` | 0 | none |

Full closure of `AnnularEndpoint`: `AnnularCaseI`, `AnnularCaseIIntegral`,
`AnnularKernel`, `CaseIIGeometry`, `CaseIISelection`, `CaseIRadialCore`,
`CircleDilation`, `EndpointConfinedExit`, `Figure5EndpointDomain`,
`Figure5EndpointEnvelopeCore`, `Figure5LocalContactCore`, `GreedyResidual`,
`LiGeometry`, `LiNeedleAdapter`, `ParametricCaseII`, `PolarOuterMeasure`,
`PolarProjectiveOuter`, `QuotientCircle`, `StarKakeyaSet`,
`SupportFirstArcSelector`, `SupportReflection`, `TriangleArea`, `Trichotomy`,
`UniversalEndpointClosureCore`, `UniversalFirstArc`, `UniversalNeedleAdapter`.

In particular **`base_ray_frozen_analytic` is not reachable** from
`AnnularEndpoint`: it lives in `CaseIEndpointR1Analytic`, which is not in the
closure. The only textual occurrences of that name in the new/edited files are
prose warnings. Its `t = 7/100` polynomial split is false at `annA`, and no
frozen facade is used to smuggle it in. Import-cycle scan: none.

### 1.2 Domination (A) and (B) — definitional

`strongInteriorRatio r = (1+2r)/(1-2r) = annInteriorRatio r` and
`strongLargeAngleRatio r = π/(π/2 - arctan 2r) = annLargeAngleRatio r` are the
*same functions* (`ann_strongInteriorRatio_eq`, `ann_strongLargeAngleRatio_eq`
are both `rfl`). Since

```
annPaperG r = max (annInteriorRatio r) (max annFrozenRatio (annLargeAngleRatio r))
```

the two dominations are `le_max_left` and `le_max_of_le_right (le_max_right _ _)`.
They hold on **all** of `ℝ`, not merely on `Icc annA annR₀`; the package's
membership hypothesis is discarded. `one_lt_g` is free via `of_dominations`.

---

## 2. The base-ray certificate — exact rational sub-gates and margins

### 2.1 The cut

```
k = annBaseK = 25000/14773 = 1.692276450280918…
l = annBaseL = 10227/14773 = 0.692276450280918…      (l = k − 1, exactly)
2k − 1 = 35227/14773 = annFrozenRatio                (exactly; `annFrozenRatio_eq`)
```

so proving the *scalar* statement `α < k t` yields

```
2α − t < 2kt − t = (2k−1) t = annFrozenRatio · t ≤ annPaperG r · t
```

with the last step `ann_frozen_le_annPaperG` (the middle entry of the `max`)
and `t > 0`. No frozen ratio leaks into the package statement, which concludes
against `annPaperG r` directly.

### 2.2 The contradiction skeleton (`ann_alpha_lt_annBaseK_mul`)

Assume `k t ≤ α`. Since `l = k − 1`, this gives `l t ≤ α − t`. From `α ≤ π/2`
we get `0 ≤ k t ≤ π/2`, and from `t > 0` also `0 ≤ l t ≤ α − t ≤ π/2`. Hence
`sin` is monotone at both places:

```
sin (k t) ≤ sin α          sin (l t) ≤ sin (α − t)
```

Three exact rational branches then contradict the hypotheses. The branches
cover `(0, ∞)` with no gap: `t ≤ 3/25`, `3/25 ≤ t ≤ 1/2`, `1/2 < t`.

### 2.3 Branch 1 — small, `0 < t ≤ 3/25`

Contradicts the `R₁`-norm hypothesis `sin α ≤ annR₁ sin t`.
Since `sin t < t` and `annR₁ < annR₁Upper` (reviewed kernel `ann_r₁_upper`),

```
sin (k t) ≤ sin α < annR₁Upper · t ,   annR₁Upper = 1675763482/1000000000
```

The gate `ann_baseRay_small` proves the reverse, `annR₁Upper · t < sin (k t)`.

*Sine input:* `Real.sin_bound` (Taylor with the `5/96 · x⁴` remainder),
legal because `k · 3/25 = 3000/14773 = 0.20307317…  ≤ 1`:

```
x − x³/6 − (5/96) x⁴ ≤ sin x            (`ann_sin_taylor_lower`)
```

*Exact rational sub-gate* (after dividing by `t > 0` and freezing
`t² ≤ (3/25)²`, `t³ ≤ (3/25)³`):

```
annR₁Upper  <  k − k³(3/25)²/6 − (5/96) k⁴(3/25)³
margin = 98679221579629554018819 / 23814682490128920500000000
       = 0.004143629528570522…                    (> 0)
```

Note the whole branch is only possible because `k − annR₁Upper =
0.016512968280917…  > 0`; that headroom is what the `t²`/`t³` terms consume.
The plain Mathlib bound `Real.sin_gt_sub_cube` (`x − x³/4`) is **not** strong
enough at `t = 3/25` (it only reaches `t ≤ 0.11627…`), which is why
`Real.sin_bound` is used here.

### 2.4 Branch 2 — mid, `3/25 ≤ t ≤ 1/2`

Contradicts the one-chord height hypothesis
`sin α · sin(α − t) ≤ annA · sin t ≤ annA · t`, via

```
annA · t  <  sin (k t) · sin (l t)  ≤  sin α · sin(α − t)      (`ann_baseRay_mid`)
```

*Sine input:* `Real.sin_gt_sub_cube`, legal because
`k/2 = 12500/14773 = 0.846138225…  ≤ 1` and `l/2 = 10227/29546 = 0.346138225… ≤ 1`.
Both lower bounds `x − x³/4` are positive there (`x³ ≤ x` on `(0,1]`).

*Exact rational sub-gate* (`ann_baseRay_mid_poly`, after dividing the degree-6
polynomial gate by `t² > 0`):

```
annA  <  t · (k − k³t²/4) · (l − l³t²/4)
```

The right side is increasing through the leading `t` and decreasing through
`t²`, so one cut at `t = 1/5` suffices; each half freezes `t` at its lower end
and `t²` at its upper end.

| sub-interval | frozen `t` | frozen `t²` | certified inequality | margin |
|---|---|---|---|---|
| `[3/25, 1/5]` | `3/25` | `1/25` | `annA < (3/25)(k − k³/100)(l − l³/100)` | `4295428382634059701321479647 / 1039470543859052603407888900000 = 0.004132323333268499…` |
| `[1/5, 1/2]` | `1/5` | `1/4` | `annA < (1/5)(k − k³/16)(l − l³/16)` | `56999449968200192702223729647 / 1039470543859052603407888900000 = 0.054835079555586766…` |

The naive single interval `[3/25, 1/2]` (freeze `t = 3/25`, `t² = 1/4`) gives
`0.111963… < annA = 0.13177` and **fails**; the `1/5` split is therefore
load-bearing, exactly as suggested.

### 2.5 Branch 3 — large, `1/2 < t`

Also contradicts the height hypothesis. Jordan `2x/π ≤ sin x` on `[0, π/2]`
(`Real.mul_le_sin`) is weakened to `x/2 < sin x` using `π < 4`
(`ann_half_lt_sin`; `π < 4` is taken from the kernel's own
`ann_pi_lt_upper`, not from a fresh `π` numeral). Applying it at `α > 0` and
`α − t > 0`, both `≤ π/2`:

```
k l t²/4 = (kt/2)(lt/2) ≤ (α/2)((α−t)/2) < sin α · sin(α − t) ≤ annA · sin t ≤ annA · t
```

*Exact rational sub-gate* (`ann_baseRay_large_poly`, freezing `t = 1/2`):

```
annA  <  k l /8
margin = 320168872367 / 21824152900000 = 0.014670391736808258…
```

### 2.6 Unused package hypotheses — honest note

`ann_base_ray_gap` is stated **verbatim** as the package field, but four of its
hypotheses are not consumed by the scalar certificate and are bound as `_hr`,
`_htop`, `_hhalf`, `_hsint`:

* `_hr : r ∈ Icc annA annR₀` — the conclusion is reached through
  `annFrozenRatio ≤ annPaperG r`, which holds at every real `r`.
* `_htop : t < π/2 − arctan (2r)` — not needed; the cut works for all `t > 0`.
* `_hhalf : t/2 ≤ α` — subsumed by the assumed `k t ≤ α` in the contradiction.
* `_hsint : 0 ≤ sin t` — re-derived where needed from `Real.sin_le`/`Real.sin_lt`.

The package **signature is not dropped or weakened**; the gate is simply
stronger than the interface requires. Only `0 < t`, `α ≤ π/2`, `hR1` and
`hheight` are actually used. No numeric constant beyond `annBaseK`, `annBaseL`
and the reviewed kernel/integral constants is introduced.

---

## 3. Package and confined exit

```lean
def annFigure5Domain : Figure5EndpointDomain where
  a := annA;  r0 := annR₀;  R1 := annR₁;  g := annPaperG
  a_pos := annA_pos                    -- 0 < 13177/100000
  a_le_r0 := by norm_num [annA, annR₀] -- 13177/100000 ≤ 999/2000
  r0_lt_half := annR₀_lt_half
  R1_pos := annR₁_pos

theorem annFigure5AnalyticPackage : Figure5EndpointAnalyticPackage annFigure5Domain :=
  Figure5EndpointAnalyticPackage.of_dominations
    (fun {r} _ => ann_strongInteriorRatio_le_annPaperG r)
    (fun {r} _ => ann_strongLargeAngleRatio_le_annPaperG r)
    (fun {_ _ _} hr ht0 htop hhalf hαtop hsint hR1 hheight =>
      ann_base_ray_gap hr ht0 htop hhalf hαtop hsint hR1 hheight)
```

All four domain projections are `rfl` (`annFigure5Domain_a/_r0/_R1/_g`), so
`Icc annFigure5Domain.a annFigure5Domain.r0` is *definitionally*
`Icc annA annR₀` and the reviewed integral obligations plug in unchanged:

```lean
theorem annular_confined_lower_bound {E : Set Plane} (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction, annA ≤ (K.needleFamily theta).height K.center) :
    ENNReal.ofReal annILower * directionAngleOuter (K.A_in_radius annR₁) ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center annR₀) :=
  confined_lower_bound_of_endpointDomain K annFigure5Domain
    annFigure5AnalyticPackage hhigh ann_aemeasurable_ofReal_radial
    annILower_le_lintegral
```

Elaborated statement, as printed by `#check`:

```
∀ {E : Set Plane} (K : StarShapedKakeya E),
  (¬∃ theta, annA ≤ UnitNeedle.height K.center (K.needleFamily theta)) →
    ENNReal.ofReal annILower * directionAngleOuter (K.A_in_radius annR₁) ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center annR₀)
```

This is **unconditional on the geometry** — no `Figure5…` hypothesis, no
selection witness, no analytic side condition survives — and conditional only on
the confined branch `hhigh` of the height dichotomy, exactly as specified.

---

## 4. Verification performed

* **`lake build`** (production root, `defaultTargets = ["StarKakeyaLower"]`) —
  success, 8363 jobs; `StarKakeyaLower.AnnularEndpoint` builds in ~8 s with **no
  warnings**.
* **`lake build StarKakeyaLowerAudit`** — success, 8361 jobs.
* **Three old-API probes**, each importing exactly one historical module, all
  exit 0 and unchanged:
  `lake env lean probe/ProbeEnvelope.lean`,
  `probe/ProbeLocalContact.lean`, `probe/ProbeClosure.lean`.
* **`#print axioms`** — the 16 new receipts, all
  `[propext, Classical.choice, Quot.sound]`:
  `ann_annBaseL_eq`, `ann_two_annBaseK_sub_one`, `ann_frozen_le_annPaperG`,
  `ann_sin_taylor_lower`, `ann_baseRay_small`, `ann_baseRay_mid_poly`,
  `ann_baseRay_mid`, `ann_half_lt_sin`, `ann_baseRay_large_poly`,
  `ann_alpha_lt_annBaseK_mul`, `ann_base_ray_gap`, `annFigure5Domain`,
  `ann_strongInteriorRatio_le_annPaperG`,
  `ann_strongLargeAngleRatio_le_annPaperG`, `annFigure5AnalyticPackage`,
  `annular_confined_lower_bound`.
  No `sorryAx` in the whole audit output. All pre-existing receipts unchanged.
* **CLEAN closure scan** — see §1.1. No forbidden module in the closure of
  `AnnularEndpoint`; no import cycles anywhere.
* **Forbidden tokens** —
  `grep -rnE "\bsorry\b|\badmit\b|^axiom |native_decide|unsafe |partial def"`
  over `StarKakeyaLower/`, `StarKakeyaLower.lean`, `probe/` returns only three
  prose mentions of the string `native_decide` inside doc comments (in
  `AnnularKernel`, `AnnularAnalytic`, `AnnularEndpoint`), which assert its
  *absence*. No code occurrence.
* **`git status`** — three paths, nothing committed, nothing pushed:
  * `M  …/04-lean/StarKakeyaLower.lean` (one new import + doc paragraph)
  * `M  …/04-lean/StarKakeyaLower/Audit.lean` (one new import + 16 receipts)
  * `?? …/04-lean/StarKakeyaLower/AnnularEndpoint.lean` (new)
  * plus this report. No sibling worktree touched.
* **Numeric evidence** — every gate margin of §2 was first computed with exact
  Python `fractions.Fraction` arithmetic and then **certified in Lean** by
  `norm_num` / `nlinarith` on the same exact rationals. No floating-point
  value, interval oracle or `native_decide` enters any proof.

---

## 5. What is still open (M7 and beyond)

* The exterior/greedy side and the Carathéodory mass split.
* The final assembly `π · annTarget` and its dichotomy with the high branch.
* `annular_confined_lower_bound` is the *confined half only*; it is not yet
  combined with any high-needle branch and proves no unconditional lower bound
  by itself. It is imported into the production root purely so `lake build`
  keeps it compiling, and `universal_strong_lower_bound` is unchanged, with an
  unchanged receipt.

## 6. Blockers

None. The suggested rational cut (`k = 25000/14773`, `l = 10227/14773`, splits
at `3/25`, `1/5`, `1/2`) validated as given; the only correction needed was in
the *tooling* of the small branch — `Real.sin_gt_sub_cube` (`x − x³/4`) is too
weak at `t = 3/25` and was replaced by `Real.sin_bound`
(`x − x³/6 − (5/96)x⁴`), exactly as the task anticipated. No step of the
suggested argument turned out to be false, no fallback search was required, and
neither `annTarget` nor `base_ray_gap` was weakened or assumed.

## 7. Reproduce

```
cd materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean
lake build
lake build StarKakeyaLowerAudit
lake env lean probe/ProbeEnvelope.lean
lake env lean probe/ProbeLocalContact.lean
lake env lean probe/ProbeClosure.lean
```
