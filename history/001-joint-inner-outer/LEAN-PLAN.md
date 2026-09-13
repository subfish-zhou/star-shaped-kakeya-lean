# Lean formalisation plan for the joint inner/outer lower bound

**Status: every milestone M0--M7 is complete.** The route is closed in Lean; the
target theorem below is proved, not sketched. The document was originally
written before any Lean existed for this route ("plan only"), and the sketches
below are preserved as written except where a milestone has since been executed
and the *actual* proved statement differs. Executed milestones are marked
**[DONE]** and carry the real signature, not a sketch. See `LEAN-STATUS.md` §22
for the M7 build output and axiom receipts, and `M6-KERNEL-STATUS.md`,
`M6-INTEGRAL-STATUS.md`, `M6-ENDPOINT-STATUS.md`, `M6-ANN-ENDPOINT-STATUS.md`
for M6.

**How to read the Lean snippets below.** Every `theorem`/`def` block that is
still marked `-- SKETCH` is a proposed shape written to fix an interface, and
was not necessarily realised under that name. Names that *do* exist in the tree
are given with `file:line` and were read from the tree at the time of writing;
`file:line` references in the **[DONE]** subsections and in §3's M7 subsection
are current. Every name used by the M0--M7 modules has been checked by
compilation against the pinned Mathlib revision.

Target — **proved**:

```lean
-- StarKakeyaLower/AnnularAssembly.lean:228 / :233
def UniversalAnnularLowerBound : Prop :=
  ∀ (E : Set Plane), StarShapedKakeya E →
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E

theorem universal_annular_lower_bound : UniversalAnnularLowerBound
```

with `annTarget = 131 / 6250` (`AnnularKernel.lean:33`), together with the
normal-form restatement

```lean
-- StarKakeyaLower/AnnularAssembly.lean:243
theorem universal_annular_lower_bound_normalForm (E : Set Plane)
    (K : StarShapedKakeya E) :
    ENNReal.ofReal (131 * Real.pi / 6250) < volume.toOuterMeasure E
```

following `PROOF.md`. The existing `universal_strong_lower_bound`
(`100π/5599`, `UniversalAssembly.lean:184`) remains proved and untouched, with
its axiom receipt unchanged; the new route is a *sibling* witness, not a
replacement, and neither theorem is used in the proof of the other.

---

## 0. Build environment (verified)

Development root:
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean/`

| Item | Value | Source |
|---|---|---|
| toolchain | `leanprover/lean4:v4.30.0-rc2` | `lean-toolchain` |
| Mathlib | scope `leanprover-community`, rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6` | `lakefile.toml` |
| default target | `StarKakeyaLower` (audit target `StarKakeyaLowerAudit` separate) | `lakefile.toml` |
| `sorry` in `StarKakeyaLower/` | none found | `grep -rn "\bsorry\b"` |
| local `axiom` declarations | none found | `grep -rn "^axiom "` |
| modules | 54 namespace modules under `StarKakeyaLower/` totalling 25,255 lines, plus the 104-line root `StarKakeyaLower.lean`: 55 files, 25,359 lines (current tree; five permanent M7 receipts were added after the 25,354 count) | `wc -l` |

The pinned Mathlib dependency is installed under `.lake/`. M0--M7 and the full
root/Audit targets have been compiled; the receipts are recorded below and in
`LEAN-STATUS.md`.

---

## 1. Genericity: declaration bodies versus dependency closure

A module can be generic in its own declarations and still be unusable in a
clean context because it *imports* the frozen witness. The two properties must
be reported separately; conflating them was an error in the previous draft of
this plan.

Method: `body` counts occurrences of the frozen constants
(`strongA`, `strongR₀`, `strongRLambda`, `strongR₁`, `strongRho`, `strongP`,
`strongTarget`, `altA`, `altTarget`) in the module's own text; `tainted deps`
lists modules in the transitive `import StarKakeyaLower.*` closure whose body
count is nonzero.

| Module | body | tainted transitive deps | verdict |
|---|---:|---|---|
| `ArithmeticKernel` | 0 | — | **CLEAN** |
| `CaseIIGeometry` | 0 | — | **CLEAN** |
| `CaseIISelection` | 0 | — | **CLEAN** |
| `CircleDilation` | 0 | — | **CLEAN** |
| `GreedyResidual` | 0 | — | **CLEAN** |
| `LiGeometry` | 0 | — | **CLEAN** |
| `LiNeedleAdapter` | 0 | — | **CLEAN** |
| `ParametricCaseII` | 0 | — | **CLEAN** |
| `PolarOuterMeasure` | 0 | — | **CLEAN** |
| `PolarProjectiveOuter` | 0 | — | **CLEAN** |
| `QuotientCircle` | 0 | — | **CLEAN** |
| `StarKakeyaSet` | 0 | — | **CLEAN** |
| `TriangleArea` | 0 | — | **CLEAN** |
| `Trichotomy` | 0 | — | **CLEAN** |
| `AnalyticBranches` | 0 | `AnalyticKernel`, `NonIterativeKernel` | BODY-ONLY |
| `SupportReflection` | 0 | `CaseIAssemblyConditional`, `CaseIEndpointAnalytic`, `StrongerKernel` | BODY-ONLY |
| `CaseIRadialCore` | 0 | — | **CLEAN** (new in M5) |
| `AnnularCaseI` | 0 | — | **CLEAN** (new in M5) |
| `UniversalNeedleAdapter` | 0 | — | **CLEAN since M5** (was BODY-ONLY over `CaseIAssemblyConditional`, `StrongerKernel`; it now imports `CaseIRadialCore`) |
| `UniversalFirstArc` | 0 | `Figure5*`, `CaseIEndpoint*`, `CaseIAssemblyConditional`, `StrongerKernel` | BODY-ONLY |
| `CaseIAssemblyConditional` | 19 | `StrongerKernel` | FROZEN |
| `CaseIEndpointAnalytic` | 2 | `CaseIAssemblyConditional`, `StrongerKernel` | FROZEN |
| `Figure5LocalContact` | 42 | 5 modules | FROZEN |
| `UniversalEndpointClosure` | 50 | 6 modules | FROZEN |
| `CaseIEndpointMassIntegral` | 53 | 5 modules | FROZEN |
| `CaseIEndpointR1Analytic` | 70 | 3 modules | FROZEN |
| `CaseIStrongIntegral` | 76 | 5 modules | FROZEN |
| `CaseIIAnalytic` | 86 | `StrongerKernel` | FROZEN |
| `StrongLiLemma25` | 115 | 3 modules | FROZEN |
| `StrongerKernel` | 175 | — | FROZEN (the kernel itself) |
| `UniversalAssembly` | 54 | 14 modules | FROZEN |

Three consequences.

1. **The escaping side is genuinely clean.** `CaseIISelection`,
   `CaseIIGeometry`, `GreedyResidual`, `ParametricCaseII`, `PolarOuterMeasure`,
   `Trichotomy`, `TriangleArea`, `QuotientCircle`, `CircleDilation` are CLEAN
   in both senses. W2 can be built on them without importing any frozen module.
2. **The confined side was not.** `CaseIAssemblyConditional`, which held the
   one parametric theorem the confined branch needs, **imports
   `StrongerKernel`**. Reusing it therefore either dragged the frozen kernel into
   the new development, or required extracting the parametric core into a clean
   module. The plan took the extraction route, and **M5 executed it**: the
   parametric core now lives in `CaseIRadialCore`, whose closure is clean, and
   `CaseIAssemblyConditional` imports it. The table above records the state
   *after* that extraction.
3. **`UniversalFirstArc` was not "transferable unchanged".** Declaration
   bodies being constant-free does not make an import closure clean, and
   `UniversalFirstArc` sits directly on top of `Figure5LocalContact`. This
   corrects an explicit overclaim in an earlier draft. `UniversalNeedleAdapter`
   was in the same position until M5 repointed its import at `CaseIRadialCore`
   and moved the coordinate transport into it; it is now CLEAN, but the
   endpoint module `UniversalFirstArc` above it is not.

`StrongLiLemma25` (115 body occurrences, 839 lines) **leaves the critical
path** entirely: `PROOF.md` Remark 9.4 replaces the local-to-global conversion
by the exterior branch.

---

## 2. Obligation map

| `PROOF.md` | Lean status | Milestone |
|---|---|---|
| §1 definitions | exist verbatim (`StarKakeyaSet.lean`) | M0 |
| Lemma 3.1 escaping needles avoid `B(0,ρ)` | **exists**: `UnitNeedle.outsideBall_sub_one_of_not_triangleHull_subset_closedBall` (`CaseIIGeometry.lean:98`) | — |
| Lemma 7.1 Carathéodory split | **DONE**: `outerMeasure_split_closedBall` (`BallSplit.lean:23`) | **M1** |
| Lemma 7.2 countable ledger | **DONE**: `tsum_outerMeasure_inter_le` (`BallSplit.lean:52`) | **M1** |
| Cor 7.3 exterior ledger | **DONE**: finite in M3b and countable selected-union ledger in M4; M4 uses measurable restricted triangles directly, so Lemma 7.2 remains proved but unused | M3b/M4 |
| Prop 4.5 (weak form) exterior area | **DONE**: `UnitNeedle.volume_triangleHull_diff_closedBall_ge` (`AnnularGeometry.lean`) | **M2** |
| Lemma 5.1, 5.2, Prop 5.3 payment | **DONE**: `sin_chord_le`, `arcsin_mul_sin_le`, `UnitNeedle.annular_payment` | **M2** |
| Lemma 4.1–4.3 sharp `W_ρ` | **not formalised, deliberately** — §5 never uses it | M2 (dropped) |
| hull/interior bridge for the restricted triangle | **DONE**: `UnitNeedle.volume_triangleInterior_diff_closedBall` | **M2** (was M3) |
| Lemma 6.1/6.2 shadow cones | **exists**: `pairwise_disjoint_selected_triangleInterior` (`CaseIISelection.lean:411`) | M3 |
| §8.1–8.2 selection, (B1)–(B2) | **exists** (`CaseIISelection.lean`) | M3 |
| §8.5 (8.2)/(8.3b) finite exterior ledger | **DONE**: `FiniteFixedSelection.selected_exterior_sum_le_outerMeasure_finite`, `FiniteFixedSelection.geometric_exterior_outerMeasure_lower_finite` (`AnnularGreedy.lean`) | **M3a/M3b** |
| §8.4 (B5) annular fan | **DONE**: `euclideanPolarAnnulus_outerMeasure_ge`, `StarShapedKakeya.residualFan_annulus_outerMeasure_lower` (`AnnularGreedy.lean`) | **M3b** |
| §8.6 Prop 8.1, **finite selection only** | **DONE**: `annular_exterior_lower_bound_of_finiteSelection` (`AnnularGreedy.lean`) | **M3b** |
| §8.3 (B4), §8.6 `B=∞` via (8.3a) | new | **M4** |
| Lemma 8.3 2π cut adapter | **exists** in `CaseIIGeometry`; consumed by the completed M3b annular fan | — |
| Lemma 9.1 polar slicing | **exists**: `lintegral_le_outerMeasure_of_le_angleOuter` (`PolarOuterMeasure.lean:135`) | — |
| Prop 9.2/9.3 confined bound | **[DONE, conditional]** raw wrapper `universal_confined_lower_bound_of_trace_containment` (`AnnularCaseI.lean:115`) and endpoint-compatible positive wrapper (`:145`), from `outerMeasure_inner_ge_caseI_lintegral_of_raw` (`CaseIRadialCore.lean:408`), restricted transport (`UniversalNeedleAdapter.lean:497`) and variable-mass factorisation (`CaseIRadialCore.lean:512`) | **M5** |
| Hypothesis B/C kernel | **DONE**: `annularParameterDomain` (`AnnularKernel.lean:404`), gates `ann_gate_C1` (`AnnularAnalytic.lean:119`), `ann_gate_C3` (`:145`), `ann_gate_C4` (`:161`), `annTarget_lt_annILower` (`AnnularCaseIIntegral.lean:844`) | **M6** |
| Endpoint containment for the new tuple | **DONE**: parameterised into `Figure5EndpointDomain` / `Figure5EndpointAnalyticPackage` and instantiated by `annFigure5AnalyticPackage` (`AnnularEndpoint.lean:403`); confined exit `annular_confined_lower_bound` (`:417`) | **M6** |
| Thm 10.1 | **DONE**: `universal_annular_lower_bound` (`AnnularAssembly.lean:233`) | **M7** |

---

## 3. Milestones

### M0 — existing build reproduced

**[DONE].** Mathlib is present at the pinned revision;
`lake build StarKakeyaLower` and `lake build StarKakeyaLowerAudit` are green and
`universal_strong_lower_bound` compiles unchanged with receipt
`[propext, Classical.choice, Quot.sound]`. Exit criterion met.

### M1 — the closed-ball split and the countable ledger **[DONE]**

Clean module `StarKakeyaLower/BallSplit.lean`, importing only
`StarKakeyaLower.StarKakeyaSet` (which is `import Mathlib` only). Actual proved
statements (not sketches):

```lean
theorem outerMeasure_split_closedBall (E : Set Plane) (o : Plane) (r : ℝ) :
    volume.toOuterMeasure E =
      volume.toOuterMeasure (E ∩ Metric.closedBall o r) +
        volume.toOuterMeasure (E \ Metric.closedBall o r)

theorem outerMeasure_ge_add_of_inter_of_diff (E : Set Plane) (o : Plane) (r : ℝ)
    {a b : ENNReal}
    (ha : a ≤ volume.toOuterMeasure (E ∩ Metric.closedBall o r))
    (hb : b ≤ volume.toOuterMeasure (E \ Metric.closedBall o r)) :
    a + b ≤ volume.toOuterMeasure E

-- PROOF.md Lemma 7.2, the COUNTABLE ledger
theorem tsum_outerMeasure_inter_le {A : Set Plane} {M : ℕ → Set Plane}
    (hmeas : ∀ i, MeasurableSet (M i)) (hdisj : Pairwise (Disjoint on M)) :
    ∑' i, volume.toOuterMeasure (A ∩ M i) ≤ volume.toOuterMeasure A
```

`outerMeasure_split_closedBall` is `measure_inter_add_diff` plus
`Measure.toOuterMeasure_apply`, with `measurableSet_closedBall` as the side
condition, exactly as anticipated.

**Correction to the original sketch of Lemma 7.2.** The proposed route
("finite induction on Carathéodory splitting followed by
`ENNReal.tsum_eq_iSup_sum`") is unnecessary. The proved route replaces `A` by
its measurable hull `U = toMeasurable volume A`, uses monotonicity
`A ∩ M i ⊆ U ∩ M i`, and then applies Mathlib's
`tsum_meas_le_meas_iUnion_of_disjoint` (which is itself proved via
`ENNReal.tsum_eq_iSup_sum`), finishing with `measure_toMeasurable`. This adds
**no** measurability hypothesis on `A`: the hull is used only as an upper
bound, and the final equality `volume U = volume.toOuterMeasure A` is exactly
`measure_toMeasurable`. The index type is `ℕ`, so the conclusion is a genuine
infinite series, not a finite sum.

**Exit criterion (met):** all three compile, `lake build
StarKakeyaLower.BallSplit` is green, and the transitive
`import StarKakeyaLower.*` closure is `{StarKakeyaSet}`, containing no FROZEN
module. **M1 was not complete until the countable ledger compiled**: the
two-set split alone does not discharge `PROOF.md` Lemma 7.2, which is what the
§8.5 ledger and the `B = ∞` branch of §8.6 consume.

**Why first:** it is the one step with no geometric risk, it types the whole
assembly, and it lets M3/M5 be developed against a fixed target shape.

### M2 — the fatal geometry gate (weak form only) **[DONE]**

Module `StarKakeyaLower/AnnularGeometry.lean`, importing `CaseIIGeometry` only
(which transitively supplies `TriangleArea` and `PolarOuterMeasure`; all CLEAN).
The gate is closed: see "What M2 actually proved" at the end of this subsection
for the real signatures and for the two interface corrections that were forced
by the pinned source.

**The first gate is the weaker, sufficient statement.** `PROOF.md` §5 uses only
`A(s) ≤ arcsin(δ/ρ)`; the sharp `W_ρ` of Lemma 4.3 is proved in the note but
**not used**. Formalising `W_ρ` first would spend the hardest effort on the
part of the argument the certificate does not need. So:

```lean
-- SKETCH  (PROOF.md Prop. 4.5, weak form -- THE GATE)
theorem UnitNeedle.volume_triangle_diff_closedBall_ge_weak
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (n.height o / 2 - r0 ^ 2 / 2 * Real.arcsin (n.height o / rho)) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0)
```

Supporting sketches:

```lean
-- SKETCH  (PROOF.md Lemma 4.1 + 4.2, stated via a REAL-ANGLE sector so that
-- no `Direction`-valued object is compared with a `Set ℝ`)
theorem UnitNeedle.triangleHull_inter_closedBall_subset_polarSector
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ∃ theta : ℝ,
      n.triangleHull o ∩ Metric.closedBall o r0 ⊆
        euclideanPolarSector o r0
          (Set.Icc theta (theta + Real.arcsin (n.height o / rho)))

-- SKETCH  (the missing MEASURABLE-ARC sector upper bound)
theorem volume_euclideanPolarSector_Icc_le (o : Plane) {rho lo hi : ℝ}
    (hrho : 0 ≤ rho) (hle : lo ≤ hi) :
    volume (euclideanPolarSector o rho (Set.Icc lo hi)) ≤
      ENNReal.ofReal (rho ^ 2 / 2 * (hi - lo))

-- SKETCH  (PROOF.md Lemma 5.1)
theorem sin_div_antitoneOn :
    AntitoneOn (fun u => Real.sin u / u) (Set.Ioc 0 (Real.pi / 2))

-- SKETCH  (PROOF.md Lemma 5.2)
theorem arcsin_mul_sin_le {m u : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ Real.pi / 2) :
    Real.arcsin (m * Real.sin u) ≤ m * u

-- SKETCH  (PROOF.md (2.3) and Prop. 5.3)
def annularCExt (a r0 rho m : ℝ) : ℝ :=
  a / (2 * Real.arcsin (a / (m * rho))) - m * r0 ^ 2 / 2

theorem UnitNeedle.annular_payment
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle}
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hheight : n.height o ≤ a) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0)
```

Interface notes.

* **The previous draft's interface was ill-typed and is withdrawn.** It read
  `rayDirection o p ∈ Set.Icc theta (theta + W)`, but
  `rayDirection : Plane → Plane → Direction` (`StarKakeyaSet.lean:103`) is
  valued in `Direction = AddCircle Real.pi`, which is not `ℝ`, so it cannot
  be a member of a `Set ℝ`. Two correctly typed replacements exist: state the
  containment as a subset of `euclideanPolarSector o r0 Θ` with `Θ : Set ℝ`
  (used above, and it is what the area bound consumes), or, if a
  direction-side statement is really wanted, quantify over the quotient image
  `directionQuotient '' Set.Icc theta (theta + W)` using
  `directionQuotient` (`CaseIIGeometry.lean:629`). The sector form is
  preferred because it avoids the quotient entirely.
* **The sector upper bound must be stated for a measurable arc.** The existing
  `euclideanPolarSector_outerMeasure_ge` (`PolarOuterMeasure.lean:298`) is a
  *lower* bound and is deliberately valid for an **arbitrary, possibly
  non-measurable** `Θ`. The upper bound is not: no claim is made here that a
  sector over an arbitrary angle set is measurable. The sketch above is
  restricted to `Θ = Set.Icc lo hi`, a measurable real interval, which is all
  Prop 4.5 needs since `Θ(Δ)` is a closed interval by construction. Note also
  that `euclideanPolarSector` already intersects with `Ioo (-π) π`
  (`PolarOuterMeasure.lean:270`), so the 2π cut of `PROOF.md` Lemma 8.3 is
  built into the definition.
* Reusable inputs: `exists_base_openSegment_on_ray_of_mem_triangleInterior`
  (`CaseIIGeometry.lean:417`) is the core of Lemma 4.2;
  `norm_openSegmentPoint_gt_of_outside` (`CaseIIGeometry.lean:370`) gives the
  strict `|y| > ρ`; `mem_triangleHull_iff_barycentric`
  (`CaseIIGeometry.lean:385`) is the barycentric handle;
  `triangleInterior_measurable` (`CaseIIGeometry.lean:113`).
* `n.footOfPerpendicular` **does not exist**; state Lemma 4.1 through
  `normalCoord` (`StarKakeyaSet.lean:73`) and `OnSupportLine`
  (`CaseIIGeometry.lean:183`) rather than adding a new projection.

**Exit criterion for M2 (met):** `UnitNeedle.annular_payment` compiles with
`annularCExt` as a free real parameter. **If M2 cannot be closed, the route is
dead and the remaining milestones are wasted work** — hence its position
immediately after the cheap M1.

Deferred (explicitly optional, not on the certified path): `annularWidth`,
Lemma 4.3's monotonicity, and Remark 4.6's sharpness identity. These are
**dropped**, not postponed: nothing downstream consumes `W_ρ`.

#### What M2 actually proved, and where the sketches were wrong

Real signatures (compiled, not sketches):

```lean
theorem UnitNeedle.volume_triangleHull_diff_closedBall_ge
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (n.height o / 2 - r0 ^ 2 / 2 * Real.arcsin (n.height o / rho)) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0)

def annularCExt (a r0 rho m : ℝ) : ℝ :=
  a / (2 * Real.arcsin (a / (m * rho))) - m * r0 ^ 2 / 2

theorem UnitNeedle.annular_payment
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle}
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hheight : n.height o ≤ a) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0)

-- hull/interior bridge, moved here from M3 (see below)
theorem UnitNeedle.volume_triangleInterior_diff_closedBall
    (o : Plane) (n : UnitNeedle) (r0 : ℝ) :
    volume (n.triangleInterior o \ Metric.closedBall o r0) =
      volume (n.triangleHull o \ Metric.closedBall o r0)

theorem UnitNeedle.annular_payment_triangleInterior
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle} ... :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleInterior o \ Metric.closedBall o r0)
```

**Correction 1 — the sector must not carry the standard cut.** The sketch
`volume_euclideanPolarSector_Icc_le` above is unusable as the *covering* set:
`euclideanPolarSector` intersects the angle set with `Ioo (-π) π`
(`PolarOuterMeasure.lean:270`), which is correct for the existing *lower*
bounds but silently discards the part of a triangle whose angular arc straddles
the cut. The proved module therefore introduces a **cut-free** compact sector

```lean
def arcSector (o : Plane) (r0 a b : ℝ) : Set Plane :=
  {z | ∃ r ∈ Icc (0 : ℝ) r0, ∃ θ ∈ Icc a b, z = o + r • angleVector θ}

theorem volume_arcSector_le (o : Plane) {r0 a b : ℝ} (hr0 : 0 ≤ r0)
    (hlen : b - a ≤ Real.pi) :
    volume (arcSector o r0 a b) ≤ ENNReal.ofReal (r0 ^ 2 / 2 * (b - a))
```

and reintroduces the cut only *inside* the proof, after an explicit
determinant-one rotation `rotLinear` has moved the arc into `Ioo (-π) π`; the
bound is then obtained by complementation inside the disc against the existing
`euclideanPolarSector_outerMeasure_ge`. The `b - a ≤ π` hypothesis is free at
the use site (`b - a = arcsin(·) ≤ π/2`) but the lemma says nothing for wider
arcs. The plan's warning against mixing `Direction` with `Set ℝ` was correct
and was respected: `arcSector` consumes a real `Set.Icc` and the quotient is
never involved.

**Correction 2 — one-sidedness is proved for the whole segment.** `PROOF.md`
Lemma 4.1 was formalised through the pair of Euclidean coordinates

```lean
def supportCoord (t : ℝ) (x : Plane) : ℝ := x 0 * Real.cos t + x 1 * Real.sin t
theorem supportCoord_sq_add_normalCoord_sq (t : ℝ) (x : Plane) :
    supportCoord t x ^ 2 + normalCoord t x ^ 2 = ‖x‖ ^ 2
```

`OutsideBall` gives `ρ ≤ ‖K - o‖` at **every** `K` of the closed segment, and
`|normalCoord| = height < ρ`, so `supportCoord` never vanishes on the segment;
being affine in the segment parameter with slope one, it therefore has constant
sign, and the negative case is handled by the opposite lift `t + π`. No
endpoint-only avoidance argument is used, and no rotation/reflection
normalisation of the needle was needed, so **risk R2 did not materialise**.

**Bridge relocation.** The hull/interior boundary-zero lemma that M3 point 1
below made M3 responsible for is single-needle geometry, so it was proved here
instead (`UnitNeedle.volume_triangleInterior_diff_closedBall`, from
`UnitNeedle.volume_frontier_triangleHull`). M3a inherits it as a finished
input. It converts **volumes only**; closed hulls are still not claimed
pairwise disjoint anywhere.

### M3 — finite restricted exterior assembly (split into M3a and M3b) **[DONE]**

New module `StarKakeyaLower/AnnularGreedy.lean`.

**Interface correction (executed): the import list above was wrong.** The
module imports `StarKakeyaLower.AnnularGeometry` and
`StarKakeyaLower.CaseIISelection` **only**. `GreedyResidual` arrives
transitively through `CaseIIGeometry`; `BallSplit` is *not* imported, because in
the finite case `PROOF.md` Corollary 7.3 is the two-set Carathéodory separation
`outerMeasure_add_le_of_disjoint_measurable` (`CaseIIGeometry.lean:1418`)
together with `measure_iUnion` over `Fin F.N`. M1's genuinely countable ledger
`tsum_outerMeasure_inter_le` is first needed by the unconditional cone-only
inequality (8.3a), which is M4.

**The previous single-milestone form contained a dependency inversion and is
withdrawn.** As written, M3's only displayed theorem (and hence its exit
criterion) already carried the residual-fan term
`ofReal ((ρ² - r₀²)/2) * directionAngleOuter F.residual`, which cannot be
produced without `euclideanPolarAnnulus_outerMeasure_ge` — a theorem that the
old text scheduled in **M4**. M3 therefore could not have been closed before
M4, contradicting its own ordering. The repair is to split M3 in two and to
**move `euclideanPolarAnnulus_outerMeasure_ge` out of M4 and into M3b**, before
the first theorem that consumes it. M4 keeps only the infinite / summable / `⊤`
material.

**Finite first.** The existing development already separates the finite
selection (`FiniteFixedSelection`, `CaseIISelection.lean:175`) from the
infinite one (`infiniteGreedyData`, `:277`), and the finite case needs no
residual-vanishing argument.

#### M3a — selected restricted interiors (no fan term) **[DONE]**

Self-contained: it mentions only the selected triangles, so it depends on M2
and `CaseIISelection` and on **nothing** from M3b or M4.

```lean
-- SKETCH
theorem selected_exterior_sum_le_outerMeasure_finite
    (F : FiniteFixedSelection height H m A) {r0 rho : ℝ} ...
    (hCext : 0 < annularCExt a r0 rho m) :
    ENNReal.ofReal (annularCExt a r0 rho m) *
        ∑ i : Fin F.N, ENNReal.ofReal (H (F.selected i)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

Ingredients, in order:

1. `UnitNeedle.annular_payment_triangleInterior` (M2) for each selected index —
   already stated on the **open** restricted triangle, so no boundary work is
   left here;
2. `pairwise_disjoint_triangleInterior_of_outside` (`CaseIIGeometry.lean:1067`)
   plus `Disjoint.mono` for the deletion: `S \ C` and `S' \ C` are disjoint
   whenever `S`, `S'` are;
3. `measure_iUnion` over `Fin F.N` on the restricted *interiors*, exactly as
   `volume_selectedTriangleUnion` (`CaseIISelection.lean:862`) does today;
4. `measure_mono` into `E \ Metric.closedBall K.center r0`.

**`hCext` is an explicit hypothesis, not a side remark.** It is needed twice:
once to pull the coefficient out of the sum via
`ENNReal.ofReal_mul (le_of_lt hCext)` — `ENNReal.ofReal` is *not* multiplicative
without a nonnegativity side condition — and once so that the coefficient
extraction is not vacuous (if `annularCExt ≤ 0` the left-hand side collapses to
`0` and the theorem, while true, carries no information). It is a scalar
inequality between explicit reals and is discharged in M6, not here; M3a takes
it as a parameter.

**Exit criterion for M3a (met):** the displayed inequality compiles from M2 and
`CaseIISelection` only, with **no** residual-fan term and no reference to any
M3b or M4 statement.

**What M3a actually proved.** Real signature (compiled, not a sketch):

```lean
theorem FiniteFixedSelection.selected_exterior_sum_le_outerMeasure_finite
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (ha : 0 < a) (harho : a < m * rho) (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho m) *
        ∑ i : Fin F.N, ENNReal.ofReal (H (F.selected i)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

**Correction A — the sketch above omitted the geometric hypotheses.**
`FiniteFixedSelection` (`CaseIISelection.lean:175`) stores no relation between
its deletion radius `H` and `arcsin(δ/(mρ))`: `H` is an arbitrary
`Direction → ℝ`. The relation, the height/needle identification, positivity and
the escaping hypothesis must therefore be threaded explicitly, exactly as
`pairwise_disjoint_triangles` (`:763`) and `geometric_outerMeasure_lower`
(`:876`) already do. This completes the sketch; it does not weaken it.

**Correction B — the disjointness input.** The plan's ingredient (2) named
`pairwise_disjoint_triangleInterior_of_outside` (`CaseIIGeometry.lean:1067`).
The theorem actually used is the selection-level
`FiniteFixedSelection.pairwise_disjoint_triangles` (`CaseIISelection.lean:763`),
which already discharges the (B2) angular separation from the greedy data. The
restriction step is then the one-line `Disjoint.mono diff_subset diff_subset`
that the plan anticipated. Closed hulls are still never claimed disjoint: the
union, the sum and every disjointness statement live on
`triangleInterior · \ closedBall ·`.

#### M3b — the annular residual fan, then the full finite theorem **[DONE]**

First the fan lower bound, moved here from M4 (`PROOF.md` (B5)):

```lean
-- SKETCH  (annular analogue of euclideanPolarSector_outerMeasure_ge,
--          PolarOuterMeasure.lean:298; Θ may be non-measurable here,
--          because this is a LOWER bound)
theorem euclideanPolarAnnulus_outerMeasure_ge (o : Plane) {r0 rho : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure
        (euclideanPolarSector o rho Θ \ Metric.closedBall o r0)
```

The oriented-lift bookkeeping of `PROOF.md` Lemma 8.3 already exists as
`directionQuotient_lipschitzWith` (`CaseIIGeometry.lean:637`),
`directionAngleOuter_image_directionQuotient_le` (`:646`) and
`directionAngleOuter_image_Icc_half` (`:699`); the cut point itself is absorbed
by the `Ioo (-π) π` in `euclideanPolarSector`.

Only then the finite theorem that needs both halves. Its exterior ledger is the
finite two-set Carathéodory separation already available in
`CaseIIGeometry`, plus `measure_iUnion` over `Fin F.N`; it does not consume
M1's countable Lemma 7.2, which is first needed in M4:

```lean
-- SKETCH  (exterior analogue of geometric_outerMeasure_lower,
--          CaseIISelection.lean:876, restricted to the exterior)
theorem geometric_exterior_outerMeasure_lower_finite
    (F : FiniteFixedSelection height H m A) {r0 rho : ℝ} ...
    (hCext : 0 < annularCExt a r0 rho m) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter F.residual +
      ∑ i : Fin F.N, volume
        ((K.needleFamily (F.selected i)).triangleInterior K.center \
          Metric.closedBall K.center r0) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

Note the statement is on `triangleInterior`, not `triangleHull`: the disjoint
sum lives on the open triangles, and M2's
`UnitNeedle.volume_triangleInterior_diff_closedBall` is the only licensed way
back to the hull. `disjoint_residualFan_selectedTriangleUnion`
(`CaseIISelection.lean:812`) keeps the fan term and the sum apart.

**Exit criterion for M3b (met):** the finite exterior bound compiles with a
`min` coefficient and no `κ`, using only M2, M3a and the fan lemma above — and,
in particular, **nothing from M4**. (M1 turned out not to be needed in the
finite case; see the import correction above.)

**What M3b actually proved.** Real signatures (compiled, not sketches):

```lean
theorem euclideanPolarAnnulus_outerMeasure_ge (o : Plane) {r0 rho : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure
        (euclideanPolarSector o rho Θ \ Metric.closedBall o r0)

theorem StarShapedKakeya.residualFan_annulus_outerMeasure_lower
    {E : Set Plane} (K : StarShapedKakeya E)
    {r0 rho : ℝ} (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (R : Set Direction)
    (hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter R ≤
      volume.toOuterMeasure (residualFan K R \ Metric.closedBall K.center r0)

theorem FiniteFixedSelection.geometric_exterior_outerMeasure_lower_finite
    (F : FiniteFixedSelection height H m A) … :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter F.residual +
        ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

theorem annular_exterior_lower_bound_of_finiteSelection
    {height H : Direction → ℝ} {m a r0 rho : ℝ} {A : Set Direction}
    {E : Set Plane} (K : StarShapedKakeya E)
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hH : ∀ θ, H θ = Real.arcsin (height θ / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (hlow : ∀ θ ∈ A, (K.needleFamily θ).height K.center < a) :
    ENNReal.ofReal (min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter A ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

**Correction C — the transfer lemmas of `PolarOuterMeasure` are `private`.**
`planeCoordinates` (`PolarOuterMeasure.lean:244`), its measure-preserving
witness (`:247`) and `outerMeasure_preimage_le_of_measurePreserving` (`:252`)
cannot be referenced from another module, so `AnnularGreedy.lean` carries a
local, verbatim copy (`planeCoords`, `:342`). This duplicates a definition and a
proof; it introduces no assumption. `UniversalNeedleAdapter.planeCoordinateEquiv`
(`:19`) is public but sits in a non-CLEAN import closure and is unusable here.

**Correction D — the annular section bound must cut the radius `r₀`.** At
`r = r₀` the angular section of `sector \ closedBall o r₀` is empty, so the
constant-section form of Lemma 9.1 is false at the left endpoint of `Icc r₀ ρ`.
`PROOF.md` §8.4 avoids this by integrating over `[r₁, ρ]` and letting
`r₁ ↓ r₀`. The Lean proof instead integrates
`fun r => ENNReal.ofReal r * (if r₀ < r then angleSetOuter Θ else 0)` and drops
the single null radius by `lintegral_congr_ae`; no limit is taken. The
statement is unchanged. The subtractive alternative
(`sector(ρ) = sector(r₀) ⊔ annulus` via M1's split) is **not** available: it
would need an *upper* bound on `sector(r₀)`, which does not exist for a
nonmeasurable `Θ`.

**Correction E — M3b's exit theorem is stated for a given finite selection.**
The M4 sketch `annular_exterior_greedy_lower_bound` quantifies over `K` and `A`
only; producing that shape requires `fixedSelectionOutcome` and hence the
infinite branch, i.e. M4. M3b therefore takes
`F : FiniteFixedSelection height H m A` as a parameter, with `height` and `H`
abstract plus their defining equations — the strongest form the finite API
`annular_exterior_lower_bound_of_finiteSelection_paperWeight` (M3b)
instantiates both equations by `rfl`. It is a canonical specialization once
`F : FiniteFixedSelection ...` is supplied; it does **not** prove that the
finite outcome occurs. Existence/case exhaustion belongs to M4.

Reused unchanged (all verified present, all in CLEAN modules):
`fixedDeletionBall` (`:19`), `directionAngleOuter_fixedDeletionBall_le` (`:26`),
`chooseAbove`/`chooseAbove_dominates` (`:81`, `:158`), `FiniteFixedSelection`
(`:175`), `future_distance_ge_two_H` (`:713`),
`triangle_shadow_sum_lt_distance` (`:731`), `pairwise_disjoint_triangles`
(`:763`), `disjoint_residualFan_selectedTriangleUnion` (`:812`),
`initial_directionAngleOuter_le_residual_add_cost` (`:930`),
`volume_selectedTriangleUnion` (`:862`), `residualFan` and
`residualFan_reaches_radius` (`CaseIIGeometry.lean:582`, `:602`).

Two substantive differences from the existing Case-II proof:

1. Every triangle volume is replaced by its exterior restriction
   `... \ Metric.closedBall K.center r0`. Disjointness survives because
   `S \ C` and `S' \ C` are disjoint whenever `S`, `S'` are; the finite sum
   uses `measure_iUnion` exactly as `volume_selectedTriangleUnion` does today.
   The existing pairwise-disjoint theorem is stated for `triangleInterior`,
   whereas Prop 4.5 is naturally stated for `triangleHull`. The required
   boundary-zero lemma is **no longer owed by M3**: it was proved in M2 as
   `UnitNeedle.volume_triangleInterior_diff_closedBall`, together with the
   ready-made open-triangle payment
   `UnitNeedle.annular_payment_triangleInterior`. The finite summation must
   still be performed on the restricted *interiors* and transferred to hulls
   only through that lemma; closed hulls are not claimed pairwise disjoint.
2. The coefficient elimination is a **`min`**, not the comparison
   `caseIIC a rho * caseIIKappa eps / 4 ≤ rho ^ 2 / 2` of
   `caseII_coefficient_elimination` (`ParametricCaseII.lean:361`). So the
   hypotheses `hrhoHalf : 1/2 < rho` and `hrhoOne : rho ≤ 1` of
   `caseII_fixed_greedy_lower_bound` (`CaseIISelection.lean:1124`) are **not**
   needed (`PROOF.md` Remark 8.2), and the elimination lemma must be re-proved
   rather than reused. There is also **no `caseIIKappa` factor** anywhere in
   the new branch, so `caseII_paperWeight_paid_by_height`
   (`ParametricCaseII.lean:303`) is replaced by
   `UnitNeedle.annular_payment_triangleInterior` from M2.

(The exit criteria are the two stated under M3a and M3b above; there is no
separate combined M3 criterion.)

### M4 — infinite, summable and `⊤` branches only **[DONE]**

**Interface correction (executed): the module placement and two of the three
listed ingredients were wrong.**  The material lives in a clean sibling
`StarKakeyaLower/AnnularGreedyInfinite.lean` (539 lines, importing
`StarKakeyaLower.AnnularGreedy` only), not inside `AnnularGreedy.lean`, which
would otherwise have passed 1050 lines; keeping M3 in its own compilation unit
also makes "M4 uses M3a/M3b as black boxes" checkable by import.  The two
ingredient corrections are recorded immediately after the original list.

The original plan text read:

* the unconditional cone-only inequality `PROOF.md` (8.3a), which needs
  `tsum_outerMeasure_inter_le` from M1 and gives the `B = ∞` branch **without**
  (B4) and without the residual fan;
* (B4) via `residual_height_zero_of_summable_cost` (`CaseIISelection.lean:636`)
  and `residual_height_zero_of_finite_stop` (`:654`), together with
  `GreedyResidual.residual_height_eq_zero_of_tendsto` (`GreedyResidual.lean:39`)
  and `summable_of_cost_tsum_ne_top` (`:970`);
* the passage from M3b's finite bound to the infinite selection.

**Correction F — `residual_height_zero_of_summable_cost` cannot be used.**
`FixedDeletionGreedyData.residual_height_zero_of_summable_cost`
(`CaseIISelection.lean:636`) requires
`hheight_le_H : ∀ n, height (G.selected n) ≤ H (G.selected n)`.  In
`caseII_fixed_greedy_lower_bound` that is discharged
(`CaseIISelection.lean:1255--1277`) via `δ = m ρ sin H ≤ m ρ H ≤ H`, whose last
step needs `m ρ ≤ 1`, i.e. the hypothesis `hrhoOne : rho ≤ 1`.  The annular
route deliberately has no `rho ≤ 1` (`PROOF.md` Remark 8.2), so reusing that
lemma would have smuggled `rho ≤ 1` back into the exit theorem.  M4 instead
follows `PROOF.md` §8.3 literally, which needs no comparison of `δ_n` with
`H_n`: summability gives `H_n → 0`, and the *exact* identity
`height_eq_multiplier_rho_sin_paperWeight` (`CaseIISelection.lean:987`) gives
`δ_n = m ρ sin H_n → 0` by continuity.  The order core is unchanged
(`GreedyResidual.residual_height_eq_zero_of_tendsto`), with `G.dominates` as its
`greedy_bound`.  New adapters:
`FixedDeletionGreedyData.selected_height_tendsto_zero_of_summable` and
`FixedDeletionGreedyData.residual_height_zero_of_summable_paperWeight`.

**Correction G — (8.3a) does not need M1's `tsum_outerMeasure_inter_le`.**
`PROOF.md` §8.5 routes the cone-only inequality through the shadow cones
`S(θ_j, δ_j)` only because `P_j` is merely *contained* in `A^ext ∩ S_j` with
`A^ext` nonmeasurable.  In Lean each restricted triangle
`triangleInterior · \ closedBall ·` is itself measurable (open minus closed)
**and** itself contained in `E \ closedBall`, so `measure_iUnion` over `ℕ` plus
`measure_mono` gives the ledger directly
(`FixedDeletionGreedyData.tsum_volume_restrictedTriangle_le_outerMeasure`).  The
shadow cones are never constructed.  This assumes strictly less than the plan
proposed.  Consequence: **M1's countable ledger `tsum_outerMeasure_inter_le` is
still unused downstream** as of M4; it remains proved and available, and the
honest statement is that nothing in M1--M4 consumes it.

**Correction H — the `infinite` constructor does not supply the deletion
cost.**  `fixedSelectionOutcome`'s `infinite` alternative yields only
`hpositive`; `infiniteGreedyData` additionally demands the `deleted_cost` field,
discharged by `directionAngleOuter_fixedDeletionBall_le`
(`CaseIISelection.lean:26`) applied to `Real.arcsin_nonneg`.  Also
`G.multiplier` is only *definitionally* `1 - eps`, so every `G`-level lemma must
be re-expressed through `hmult : G.multiplier = m := rfl`.  Bookkeeping, not
mathematics.

**M4 contains no new geometry.** The annular fan (B5),
`euclideanPolarAnnulus_outerMeasure_ge`, has been **moved to M3b**, where it is
proved before the first theorem that uses it; the oriented-lift bookkeeping of
`PROOF.md` Lemma 8.3 moves with it. What remains in M4 is exactly the
infinite / summable / `⊤` case analysis.

Then the combined statement:

```lean
-- SKETCH
theorem annular_exterior_greedy_lower_bound
    {E : Set Plane} (K : StarShapedKakeya E) (A : Set Direction)
    {eps a r0 rho : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1) (ha : 0 < a)
    (hr0 : 0 < r0) (hlt : r0 < rho) (harhoScaled : a < (1 - eps) * rho)
    (hCext : 0 < annularCExt a r0 rho (1 - eps))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (hlow : ∀ θ ∈ A, (K.needleFamily θ).height K.center < a) :
    ENNReal.ofReal
        (min (annularCExt a r0 rho (1 - eps) / 4) ((rho ^ 2 - r0 ^ 2) / 2))
      * directionAngleOuter A ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

plus the `A_out_radius` specialisation mirroring
`caseII_A_out_fixed_greedy_lower_bound` (`CaseIISelection.lean:1292`). Note
`hCext : 0 < annularCExt a r0 rho (1 - eps)` is threaded unchanged from M3a: it
is what licenses `ENNReal.ofReal_mul` in the coefficient extraction, at every
level.

**Exit criterion (met):** the exterior branch is unconditional in the deletion
budget, covering the finite, summable and `B = ∞` cases, using M3a/M3b as black
boxes.

**What M4 actually proved.**  The sketch above is, for once, the real signature:
`annular_exterior_greedy_lower_bound` compiles verbatim as displayed, with `A`
an arbitrary `Set Direction` and no selection input.  Two additions:

```lean
-- non-vacuity of the coefficient under exactly the exit hypotheses
theorem annular_exterior_coefficient_pos {a r0 rho m : ℝ}
    (hr0 : 0 < r0) (hlt : r0 < rho) (hCext : 0 < annularCExt a r0 rho m) :
    0 < min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)

-- the A_out specialisation the plan asked for
theorem annular_exterior_A_out_greedy_lower_bound
    {E : Set Plane} (K : StarShapedKakeya E) {eps a r0 R₁ : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1) (ha : 0 < a)
    (hr0 : 0 < r0) (hlt : r0 < R₁ - 1)
    (harhoScaled : a < (1 - eps) * (R₁ - 1))
    (hCext : 0 < annularCExt a r0 (R₁ - 1) (1 - eps))
    (hhigh : ¬ ∃ theta : Direction,
      a ≤ (K.needleFamily theta).height K.center) :
    ENNReal.ofReal
        (min (annularCExt a r0 (R₁ - 1) (1 - eps) / 4)
          (((R₁ - 1) ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter (K.A_out_radius R₁) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

The `A_out` version needs `0 ≤ R₁`, obtained from `0 < r0 < R₁ - 1` by
`linarith`; `A_out_radius` lives in the CLEAN `Trichotomy`, so no numeric
constant and no frozen module enters.

### M5 — restricted transport and variable interior mass **[DONE]**

Two genuinely missing pieces, both on the confined side. **Neither is a numeral
change.**

**Executed.** The sketches in (a)-(c) below are preserved as written; the
*actual* proved statements, the exact moved-declaration ranges, the builds, the
axiom receipts and the scans are in `LEAN-STATUS.md` §20. Three interface
corrections were discovered while executing, and are recorded inline below. The
exit criterion is unchanged and was met: `AnnularCaseI.lean:115` proves

```lean
theorem universal_confined_lower_bound_of_trace_containment
    {E : Set Plane} (K : StarShapedKakeya E)
    {a r₀ : ℝ} {g : ℝ → ℝ} {A : ℝ → Set ProjectiveDirection}
    {L_in I_lower : ℝ≥0∞} (ha : 0 ≤ a) (hr₀ : 0 ≤ r₀)
    (htrace : ∀ r ∈ Icc a r₀, ∀ d,
      FirstArcData (universalDirectionNeedle K d).triangle r)
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r))
    (hcritical : ∀ r (hr : r ∈ Icc a r₀),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw (universalDirectionNeedle K) (htrace r hr))
        (A r) (g r))
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀)))
    (hI : I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r)) :
    I_lower * L_in ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r₀)
```

For the generic wrapper `htrace`, `hcritical`, `hg`, `hmass`, `hmeas` and `hI`
remain hypotheses. For the intended constant inner class, M5's
`directionAngleOuter_le_directionOuterMass_const` closes `hmass`; M6 therefore
owes the other five inputs, not the mass normalization.

**Second pass (downstream contract).** The first pass stated the wrapper only
for the *signed* family `universalDirectionNeedle K`, while the existing
endpoint chain produces the *positively oriented* `universalPositiveNeedle K` —
a contract mismatch that would have blocked M6. It is fixed generically: one
theorem `confined_lower_bound_of_raw_of_restricted_containment` takes an
arbitrary raw family together with a supplied restricted containment, and both
`universal_confined_lower_bound_of_trace_containment` (signed, unchanged public
signature) and the new
`universal_positive_confined_lower_bound_of_trace_containment` (positive) are
corollaries of it. Nothing is duplicated. To make the positive family reachable
without frozen imports, `DirectionNeedle.orientPositive` and its four lemmas
were moved out of `UniversalFirstArc`, the `universalPositiveNeedle` block out
of `UniversalEndpointClosure`, and the three orientation-reversal identities
they rest on out of `SupportReflection`, all into the CLEAN
`UniversalNeedleAdapter`, preserving every public name and statement verbatim.
The direction-mass normalization bridge `directionOuterMass_eq_directionAngleOuter`
was added in `CaseIRadialCore`. See `LEAN-STATUS.md` §20.6.

**(a) Restricted coordinate transport.** The existing transport
`outerMeasure_centeredCoordinate_image` (`UniversalAssembly.lean:48` before M5;
now `UniversalNeedleAdapter.lean:433`) is *unrestricted*:

```lean
volume.toOuterMeasure (centeredCoordinate K '' E) = volume.toOuterMeasure E
```

The current chain gets away with this because
`strong_caseI_of_endpoint_certificate` (`UniversalAssembly.lean:137` before M5;
now `:101`) ends with
`measure_mono (universalPositiveTriangleUnion_subset K)` into the *whole* set.
The new route cannot: `outerMeasure_inner_ge_caseI_lintegral_of_raw`
(`CaseIAssemblyConditional.lean:405` before M5; now `CaseIRadialCore.lean:408`)
concludes about
`directionTriangleUnion N Set.univ ∩ originClosedDisk r₀` in `CoordinatePlane`,
whereas M1 needs a bound on `E ∩ Metric.closedBall K.center r0` in `Plane`.
The missing lemma is the *restricted* transport:

```lean
-- SKETCH
theorem centeredCoordinate_image_closedBall
    {E : Set Plane} (K : StarShapedKakeya E) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    centeredCoordinate K '' Metric.closedBall K.center r0 =
      originClosedDisk r0

theorem outerMeasure_centeredCoordinate_image_inter_closedBall
    {E : Set Plane} (K : StarShapedKakeya E) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    volume.toOuterMeasure ((centeredCoordinate K '' E) ∩ originClosedDisk r0) =
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r0)

theorem universalDirectionTriangleUnion_inter_originClosedDisk_subset
    {E : Set Plane} (K : StarShapedKakeya E) {r0 : ℝ} :
    directionTriangleUnion (universalDirectionNeedle K) Set.univ ∩
        originClosedDisk r0 ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r0
```

The nonnegativity hypothesis is load-bearing: for negative `r0` the metric
closed ball is empty while the squared-radius definition of
`originClosedDisk r0` need not be. It requires proving that `centeredCoordinate K` maps
`Metric.closedBall K.center r0` onto `originClosedDisk r0`
(`CaseIAssemblyConditional.lean:301` before M5, now `CaseIRadialCore.lean:304`,
defines the latter by `z.1 ^ 2 + z.2 ^ 2 ≤ r₀ ^ 2`), then reusing the
measure-preserving equivalence.
`outerMeasure_inter_originOpenDisk_eq_closedDisk`
(`CaseIAssemblyConditional.lean:353` before M5; now `CaseIRadialCore.lean:356`)
shows the open/closed distinction is already handled on the coordinate side.

**Interface correction 1 (executed).** All three sketches were proved with the
sketched statements. Two supporting declarations were needed and are new public
names in `UniversalNeedleAdapter`: `centeredCoordinate_injective` (`:441`), so
that `Set.image_inter` applies, and `dist_le_iff_sq_add_sq_le` (`:452`), the
`EuclideanSpace` computation turning `dist x K.center ≤ r0` into the
squared-radius inequality. Also, the old `outerMeasure_centeredCoordinate_image`
is stated only for `K`'s own `E`, which is too weak for the restricted version;
its proof body was moved to a set-generic
`outerMeasure_centeredCoordinate_image_of_set` (`:403`) and the old name kept as
a one-line corollary, so no client changed and there is no second semantic
track.

**(b) Variable interior mass.** The current mass plumbing hardwires the split:

```lean
def strongCaseIQ (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi * strongP / strongPaperG r)   -- CaseIEndpointMassIntegral.lean:22
```

and both `strongCaseI_aggregateMass_of_directionOuterMass` (`:32`, now `:26`)
and `strongCaseI_lintegral_ge_of_integral_ge` (`:51`, now `:45`) are stated in
terms of the literal `Real.pi * strongP`. **These are not reusable as-is**: `PROOF.md` §9
uses the *actual* confined mass `L_in`, which is a variable, and the new route
has no `p` at all. The replacements:

```lean
-- SKETCH
def annularCaseIQ (L_in : ℝ≥0∞) (g : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  L_in / ENNReal.ofReal (g r)

-- SKETCH: aggregate mass at variable L_in
theorem annular_aggregateMass_of_directionOuterMass
    {r : ℝ} {A : Set ProjectiveDirection} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : 1 ≤ g r) (hmass : L_in ≤ directionOuterMass A) :
    FirstArcAggregateMass A (g r) (annularCaseIQ L_in g r)

-- SKETCH: the mass factors out of the radial integral
theorem lintegral_annularCaseIQ_eq_mul
    {a r0 : ℝ} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (ha : 0 ≤ a) (hg : ∀ r ∈ Icc a r0, 1 ≤ g r)
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r0))) :
    (∫⁻ r in Icc a r0, ENNReal.ofReal r * annularCaseIQ L_in g r) =
      L_in * ∫⁻ r in Icc a r0, ENNReal.ofReal (r / g r)
```

`hg` gives a positive denominator; the separate `hmeas` hypothesis licenses
`lintegral_const_mul`. Positivity does not imply this measurability fact.

**Interface correction 2 (executed).** The sketched `ha : 0 ≤ a` on
`lintegral_annularCaseIQ_eq_mul` is **not needed** and was not kept:
`ENNReal.ofReal` truncates at negative reals, so the pointwise identity
`ofReal r * annularCaseIQ L_in g r = L_in * ofReal (r / g r)` reads `0 = 0` for
`r < 0` too. `0 ≤ a` is still load-bearing one level up, where the raw radial
theorem consumes it, and it is a hypothesis of the M5 exit theorem. The
factorisation uses `lintegral_const_mul''` (the `AEMeasurable` form), which is
what keeps the statement sound at `L_in = ⊤`. Otherwise both sketches were
proved as written; the pointwise identity was named
`ofReal_mul_annularCaseIQ` (`CaseIRadialCore.lean:492`) and the aggregate-mass
predicate `FirstArcAggregateMass` had to be moved out of the FROZEN
`CaseIEndpointMassIntegral` into `CaseIRadialCore` (`:466`) so that the clean
statement could use it rather than duplicate it.

The factorisation is the step that lets `PROOF.md` Theorem 10.1 conclude with
`I * L_in + C_out * L_out ≥ min(I, C_out) * (L_in + L_out) ≥ min(...) * π`.
All of it must stay in `ℝ≥0∞`; `L_in ≤ π < ⊤` is available but should not be
used to drop into `ℝ`.

**(c) Extraction.** Because `CaseIAssemblyConditional` is FROZEN by import
(§1), M5 must move `outerMeasure_inner_ge_caseI_lintegral_of_raw` and its
prerequisites into a CLEAN module (say `CaseIRadialCore.lean`) that does not
import `StrongerKernel`.

**Interface correction 3 (executed).** The extraction boundary turned out to be
exactly `CaseIAssemblyConditional.lean` lines 25--449 (33 declarations, ending
with `outerMeasure_ge_caseI_lintegral`): that whole block is free of frozen
constants, and everything after it is genuinely Li-specific. `CaseIRadialCore`
needs only `PolarProjectiveOuter` and `LiNeedleAdapter`. The physical wrapper
went into a small sibling `AnnularCaseI.lean` rather than into the core, since
it mentions `StarShapedKakeya`. No cycle appeared, and no frozen import had to
be reintroduced anywhere. The boundary also includes the literal adapter and
transport currently trapped behind `UniversalNeedleAdapter` and
`UniversalAssembly`: `centeredCoordinate`, `universalDirectionNeedle`, the
triangle-union containment, and the measure-preserving coordinate equivalence
must become reachable from a CLEAN closure. The old frozen modules then import
and reuse these declarations, preserving the existing public names and the
`100π/5599` proof. Duplicating definitions under new names would create two
semantic tracks and is not acceptable. This is a mechanical but non-trivial
refactor and a prerequisite for M7 being import-clean.

**Exit criterion:** conditional on a supplied endpoint-containment hypothesis
and a supplied scalar integral lower bound `I_lower`, the confined interface
proves
`I_lower * L_in ≤ volume.toOuterMeasure (E ∩ Metric.closedBall K.center r0)`
for a *variable* `L_in`, with no `strongP` anywhere. M5 does not certify those
two supplied hypotheses; they are discharged only in M6.

**Met**, unchanged, by `universal_confined_lower_bound_of_trace_containment`
above. `universal_strong_lower_bound` still compiles with the same axiom
receipt.

### M6 — parameterised endpoint machinery and the new kernel **[DONE]**

*The plan text of this subsection is preserved as written, before M6 was
executed. It is accurate as a description of the problem, but its
forward-looking wording ("must", "owes", "still open") is **superseded**: M6 is
closed. The realised modules are `AnnularKernel` (Hypothesis B / the parameter
tuple), `AnnularAnalytic` (the arcsine enclosure and gates C1/C3/C4),
`AnnularCaseIIntegral` (the two-active-segment radial certificate, `hg`,
`hmeas`, `hI` and gate C2), the parameterised endpoint layer
`Figure5EndpointDomain` / `Figure5EndpointEnvelopeCore` /
`Figure5LocalContactCore` / `UniversalEndpointClosureCore` /
`EndpointConfinedExit`, and `AnnularEndpoint` (the production-tuple instance and
the confined exit `annular_confined_lower_bound`). Full evidence is in
`M6-KERNEL-STATUS.md`, `M6-INTEGRAL-STATUS.md`, `M6-ENDPOINT-STATUS.md` and
`M6-ANN-ENDPOINT-STATUS.md`.*

**This milestone is not numeral replacement.** The endpoint containment
`FirstArcPointwiseHybridCriticalContainment` is currently produced by
`caseIEndpointPointwiseTheorem_proof` (`UniversalAssembly.lean:208`) through
`universalArcData` / `universal_hybrid_containment`
(`UniversalEndpointClosure.lean`, 50 body occurrences, transitively tainted by
6 modules) sitting on `Figure5LocalContact.lean` (1480 lines, 42 body
occurrences). These two modules encode the local endpoint-contact estimate of
paper Lemma 5.1, and the frozen constants appear inside geometric case
distinctions, not only in final numeric comparisons. **Deep parameterisation
is required**: the honest first task is to attempt

```lean
variable (a rLambda r0 R₁ : ℝ)
```

generalisation of `Figure5EndpointEnvelope` → `Figure5LocalContact` →
`UniversalEndpointClosure`, discover which steps actually need tuple-specific
numeric facts, and only then decide between generalisation and duplication.
Until that experiment is run, the cost of M6 is genuinely unknown, and no
estimate is offered here.

New kernel `StarKakeyaLower/AnnularKernel.lean` (sibling of `StrongerKernel`,
which is **not** modified):

```lean
-- SKETCH
def annTarget   : ℝ := 131 / 6250
def annA        : ℝ := 13177 / 100000
def annRLambda  : ℝ := 10227 / 50000
def annR₀       : ℝ := 999 / 2000
def annEps      : ℝ := 1 / 10 ^ 10
def annLambda   : ℝ := 29496 / 36773
def annRadicand : ℝ := 4 * annRLambda ^ 2 * (1 + annA ^ 2) - annA ^ 2
def annD        : ℝ := annA * (1 - Real.sqrt annRadicand) / (2 * (1 + annA ^ 2))
def annR₁       : ℝ :=
  Real.sqrt (1 + 4 * annD ^ 2) / (1 - 2 * Real.sqrt (annRLambda ^ 2 - annD ^ 2))
def annRho      : ℝ := annR₁ - 1
structure AnnularParameterDomain where ...        -- PROOF.md Hypothesis B
```

modelled on `strongParameterDomain` (`StrongerKernel.lean:355`). There is **no
`annP`**: the new route needs no mass split, so the relevant existing input is
`univ_subset_A_in_radius_union_A_out_radius_of_no_high` (`Trichotomy.lean:82`)
plus subadditivity, **not** `direction_radius_trichotomy` (`Trichotomy.lean:145`).
This removes `ParametricCaseII.caseII_minimax` (`:400`) from the critical path.

Analytic gates (`AnnularAnalytic.lean`), mirroring `CaseIIAnalytic`:
rational enclosures for the three radicals, an upper enclosure for
`Real.arcsin (annA / ((1 - annEps) * annRho))`, and the four gate comparisons
of `PROOF.md` Hypothesis C. `strongPiUpper` (`StrongerKernel.lean:59`) is not
tuple-specific and can be reused if the import is acceptable.

Integral certificate (`AnnularCaseIIntegral.lean`): `CaseIStrongIntegral.lean`
uses a **three**-piece cut at `9/40` and `2353/10000`. For the new tuple the
frozen branch `(1+2rλ)/(1-2rλ) = 35227/14773 = 2.38455…` is dominated on all of
`[annA, annR₀]` by the increasing large-angle branch (value `2.392472…` at
`r = annA`), so there is exactly **one** switch, at `r = 0.2352988169…`. The
new certificate is a two-piece cut; `strongSwitchLeft`/`strongSwitchRight` must
**not** be ported, and no Lean lemma that assumes the frozen branch is active
somewhere on `[a, r₀]` may be reused.

**The M5 input contract, explicitly.** M5 is closed, so the shape M6 must hit
is now fixed rather than guessed. The confined branch is entered through

```lean
universal_positive_confined_lower_bound_of_trace_containment
    (K : StarShapedKakeya E) (ha : 0 ≤ a) (hr₀ : 0 ≤ r₀)
    (htrace     : ∀ r ∈ Icc a r₀, ∀ d,
                    FirstArcData (universalPositiveNeedle K d).triangle r)
    (hg         : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmass      : ∀ r ∈ Icc a r₀, L_in ≤ directionOuterMass (A r))
    (hcritical  : ∀ r (hr : r ∈ Icc a r₀),
                    FirstArcPointwiseHybridCriticalContainment
                      (directionNeedleFamilyOfRaw (universalPositiveNeedle K)
                        (htrace r hr)) (A r) (g r))
    (hmeas      : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
                    (volume.restrict (Icc a r₀)))
    (hI         : I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r))
```

The full instantiation contract has six items. Items 1--3 are already closed by
M5; M6 owes items 4--6, corresponding to the five wrapper inputs
`htrace`, `hcritical`, `hg`, `hmeas`, `hI`:

1. **[CLOSED in M5] the positive family, not the signed one.** The wrapper is stated for
   `universalPositiveNeedle K`, which is what `universalArcData` and
   `universal_hybrid_containment` already produce. (There is a second corollary
   `universal_confined_lower_bound_of_trace_containment` for the signed
   `universalDirectionNeedle K`; both are corollaries of one generic theorem
   `confined_lower_bound_of_raw_of_restricted_containment`. M6 should use the
   positive one.)
2. **[CLOSED in M5] a constant direction class.** Take `A r = K.A_in_radius R₁` for every `r`;
   the class does not vary with the radius on the confined branch.
3. **[CLOSED in M5] the mass normalization.** Take
   `L_in = directionAngleOuter (K.A_in_radius R₁)`. Then `hmass` is discharged
   outright by `directionAngleOuter_le_directionOuterMass_const`
   (`AnnularCaseI.lean`), which is `directionOuterMass_eq_directionAngleOuter`
   (`CaseIRadialCore.lean`) at a constant class. This is also the form the
   exterior branch (M4) speaks in, so M7 can add the two masses without a
   further bridge.
4. **[M6] `htrace` and `hcritical` for the new tuple** — the deep parameterisation
   described above. This is the only genuinely open geometric item.
5. **[M6] a concrete `g` with `hg` and `hmeas`.** `hg : 1 ≤ g r` on the interval is
   the analogue of `one_le_strongPaperG`; `hmeas` is an `AEMeasurable`
   obligation on `fun r => ENNReal.ofReal (r / g r)` restricted to `Icc a r₀`,
   and it does **not** follow from positivity. Continuity of `g` on the interval
   with a nonvanishing denominator is the expected route.
6. **[M6] `hI` in `ℝ≥0∞`, not in `ℝ`.** The integral certificate must end at
   `I_lower ≤ ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r)`, a *lower Lebesgue*
   integral. A Bochner/`∫` statement of the same bound is not directly usable;
   the conversion is part of item 3 of the exit criterion.

**Exit criterion:** all of the following compile together:

1. `annularParameterDomain` and the four Hypothesis-C comparisons;
2. the parameterised endpoint-containment theorem required by the conditional
   M5 interface — concretely, items 4 above, i.e. `htrace` and `hcritical` at
   the new tuple for `universalPositiveNeedle`;
3. the two-piece integral certificate and its scalar lower-bound theorem, in the
   `∫⁻` form of item 6, together with the concrete `g`, `hg` and `hmeas` of
   item 5.

Merely compiling the numeric domain and four final comparisons would not have
been enough: without items 2--3, M7 would have lacked the geometric and analytic
inputs of the confined branch. All three exit items were delivered, so M7 had
every input it needed.

**Import-clean warning — resolved.** `strongPiUpper` lives in `StrongerKernel`.
M6 avoided the dependency entirely rather than extracting it: `ann_gate_C1`
(`AnnularAnalytic.lean:119`) uses `Real.pi_lt_d20` directly, and the M7 high
branch multiplies that gate by `π > 0` instead of routing through a rational
upper bound for `π`. `StrongerKernel` is not in the M7 import closure.

This warning **no longer applies to `SupportReflection`**: the three orientation
identities the confined branch actually needs (`supportPoint_add_pi_neg`,
`supportNeedleTriangle_add_pi_neg`, `projectiveDirection_add_pi`) were moved by
M5 into the CLEAN `UniversalNeedleAdapter`, together with
`DirectionNeedle.orientPositive` and the whole `universalPositiveNeedle` block.
`SupportReflection` itself is still BODY-ONLY over a tainted chain, but nothing
on the confined path has to import it.

### M7 — assembly and audit **[DONE]**

New module `StarKakeyaLower/AnnularAssembly.lean` (251 lines, four imports:
`BallSplit`, `AnnularGreedyInfinite`, `AnnularAnalytic`, `AnnularEndpoint`).
The statements below are **compiled signatures copied from source**, not
sketches.

```lean
-- AnnularAssembly.lean:228
def UniversalAnnularLowerBound : Prop :=
  ∀ (E : Set Plane), StarShapedKakeya E →
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E

-- AnnularAssembly.lean:233
theorem universal_annular_lower_bound : UniversalAnnularLowerBound
```

The parameterised theorem behind the `Prop` wrapper, matching the project
convention of `strong_lower_bound_of_caseI` / `universal_strong_lower_bound`:

```lean
-- AnnularAssembly.lean:194
theorem annular_lower_bound {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E
```

Supporting declarations, in proof order:

```lean
-- AnnularAssembly.lean:77, :89 — the two coefficients and their minimum
def annCExt : ℝ :=
  min (annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) / 4)
    (((annR₁ - 1) ^ 2 - annR₀ ^ 2) / 2)
def annJointCoefficient : ℝ := min annILower annCExt

-- AnnularAssembly.lean:104 — interior gate (C2) and exterior gates (C3)/(C4)
theorem annTarget_lt_annJointCoefficient : annTarget < annJointCoefficient

-- AnnularAssembly.lean:117, :126 — direction mass, outer measure only
theorem directionAngleOuter_le_pi (A : Set Direction) :
    directionAngleOuter A ≤ ENNReal.ofReal Real.pi
theorem pi_le_directionAngleOuter_add_compl (A : Set Direction) :
    ENNReal.ofReal Real.pi ≤ directionAngleOuter A + directionAngleOuter Aᶜ

-- AnnularAssembly.lean:150 — high branch, from gate (C1)
theorem ann_target_lt_high_threshold :
    ENNReal.ofReal (Real.pi * annTarget) < ENNReal.ofReal (annA / 2)

-- AnnularAssembly.lean:165 — the M1 glue of the M6 and M4 ledgers
theorem annular_joint_ledger (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      annA ≤ (K.needleFamily theta).height K.center) :
    ENNReal.ofReal annJointCoefficient *
        (directionAngleOuter (K.A_in_radius annR₁) +
          directionAngleOuter (K.A_out_radius annR₁)) ≤
      volume.toOuterMeasure E

-- AnnularAssembly.lean:239, :243 — constant in normal form
theorem pi_mul_annTarget_eq : Real.pi * annTarget = 131 * Real.pi / 6250
theorem universal_annular_lower_bound_normalForm (E : Set Plane)
    (K : StarShapedKakeya E) :
    ENNReal.ofReal (131 * Real.pi / 6250) < volume.toOuterMeasure E
```

**Realised proof architecture.** `by_cases hhigh : ∃ θ, annA ≤ height θ`.

* High branch: `ann_target_lt_high_threshold` (gate C1
  `annTarget < annA / (2π)` multiplied by `π > 0`, then
  `ENNReal.ofReal_lt_ofReal_iff`) chained into
  `StarShapedKakeya.high_branch_outerMeasure` (`Trichotomy.lean:188`).
* Confined branch: `annular_confined_lower_bound K hhigh`
  (`AnnularEndpoint.lean:417`) supplies
  `ofReal annILower * L_in ≤ μ*(E ∩ closedBall K.center annR₀)`;
  `annular_exterior_A_out_greedy_lower_bound`
  (`AnnularGreedyInfinite.lean:516`), instantiated at
  `eps = annEps, a = annA, r0 = annR₀, R₁ = annR₁` through
  `ann_m4_exterior_domain` (`AnnularAnalytic.lean:196`) and the same `hhigh`,
  supplies `ofReal annCExt * L_out ≤ μ*(E \ closedBall K.center annR₀)`. Both
  coefficients are lowered to `annJointCoefficient` by
  `ENNReal.ofReal_le_ofReal` and `mul_le_mul_left`, and the two ledgers are
  added by `outerMeasure_ge_add_of_inter_of_diff` (`BallSplit.lean:34`) after
  `mul_add`.
* Direction mass: `ofReal π ≤ L_in + L_out` from circle coverage plus
  `measure_union_le`, transported by
  `directionOuterMeasure_eq_directionAngleOuter` (`CaseIIGeometry.lean:722`)
  and `StarShapedKakeya.directionOuterMeasure_univ` (`Trichotomy.lean:63`).
* Strictness: `ofReal (π · annTarget) = ofReal annTarget * ofReal π` via
  `ENNReal.ofReal_mul` and `annTarget_pos`, then `mul_le_mul_right` against the
  mass bound, then `ENNReal.mul_lt_mul_left hS0 hStop` with
  `hS0 : L_in + L_out ≠ 0` (from `π ≤ L_in + L_out`) and
  `hStop : L_in + L_out ≠ ⊤` (from `L_in, L_out ≤ ofReal π`).

**Measurability discipline.** `A_in_radius annR₁` and `A_out_radius annR₁` are
*not* assumed measurable, so the identity `L_in + L_out = π` is never used —
only the inequality obtained from coverage and outer-measure subadditivity, plus
the complementary `≤ ofReal π` bound needed for the finiteness side condition.
No `ℝ≥0∞` cancellation law appears anywhere in the module.

`StarKakeyaLowerAudit` was extended with seventeen `#print axioms` receipts for
all declarations of `AnnularAssembly` (`Audit.lean:554-570`), and its `AnnularEndpoint` import was
replaced by `AnnularAssembly`, which re-exports it.

**Exit criterion — met.** `lake build StarKakeyaLower StarKakeyaLowerAudit`
completes successfully (8369 jobs); all 477 audit receipts, including
`universal_annular_lower_bound` and the unchanged `universal_strong_lower_bound`,
are exactly `[propext, Classical.choice, Quot.sound]`; the new module compiles
with **zero** warnings.

---

## 4. Dependency graph of the proposed modules

```
CLEAN existing: StarKakeyaSet, TriangleArea, QuotientCircle, CircleDilation,
                GreedyResidual, ParametricCaseII, Trichotomy, LiGeometry,
                PolarOuterMeasure, PolarProjectiveOuter, CaseIIGeometry,
                CaseIISelection, LiNeedleAdapter, ArithmeticKernel
        │
        ├── BallSplit           (new, M1)   -- DONE; StarKakeyaSet only
        ├── AnnularGeometry     (new, M2)   -- DONE; CaseIIGeometry only
        │                                      (TriangleArea, PolarOuterMeasure
        │                                       come in transitively)
        ├── AnnularGreedy       (new, M3a/M3b; DONE)
        │                                      -- AnnularGeometry, CaseIISelection
        ├── AnnularGreedyInfinite (new, M4; DONE)
        │                                      -- imports AnnularGreedy only;
        │                                         does not consume BallSplit
        ├── CaseIRadialCore     (new, M5; DONE)
        │                                   -- extraction of the parametric core
        │                                      of CaseIAssemblyConditional,
        │                                      WITHOUT importing StrongerKernel
        ├── AnnularCaseI        (new, M5; DONE)
        │                                   -- imports UniversalNeedleAdapter,
        │                                      which M5 repointed at
        │                                      CaseIRadialCore and which now
        │                                      carries the coordinate transport,
        │                                      the orientation normalization and
        │                                      the positive universal family
        ├── AnnularKernel,      (new, M6; DONE) -- Mathlib only
        │   AnnularAnalytic,    (new, M6; DONE) -- AnnularKernel, AnnularGeometry
        │   AnnularCaseIIntegral (new, M6; DONE) -- AnnularKernel only
        ├── Figure5*Core / UniversalEndpointClosureCore / EndpointConfinedExit
        │                       (M6; DONE) -- the parameterised endpoint layer
        ├── AnnularEndpoint     (new, M6; DONE)
        │                                   -- AnnularCaseIIntegral,
        │                                      EndpointConfinedExit; the
        │                                      production-tuple instance
        └── AnnularAssembly     (new, M7; DONE)
                                            -- BallSplit, AnnularGreedyInfinite,
                                               AnnularAnalytic, AnnularEndpoint

Untouched and still proving their own results:
    StrongerKernel, StrongLiLemma25, UniversalAssembly, NonIterativeKernel
```

**Verified closure (post-M7).** The transitive import closure of
`AnnularAssembly` is 32 modules and contains **zero** occurrences of the frozen
witness constants `strongA`, `strongR₀`, `strongR₁`, `strongTarget`,
`strongPaperG`, `strongP`, `strongILower`, `strongPiUpper` or the literal
`5599` in declaration bodies, and does not reach `StrongerKernel`,
`Figure5FrozenPackage`, `UniversalAssembly`, `CaseIAssemblyConditional` or
`StrongLiLemma25`. The import graph over `StarKakeyaLower/` is acyclic.

---

## 5. Risk register

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | ~~M2 has no precedent: nothing in the tree measures a triangle minus a ball, and the *upper* sector bound does not exist~~ | **CLOSED** | M2 is done; the upper bound exists as `volume_arcSector_le` over a cut-free `arcSector`, proved by complementation inside the disc |
| R2 | ~~Lemma 4.1 may need an explicit rotation/reflection normalisation~~ | **CLOSED** | done via `supportCoord`/`normalCoord` and the opposite lift `t + π`; `SupportReflection` was not needed, and the only rotation used is inside the sector area bound |
| R3 | ~~M6 endpoint parameterisation depth is unknown; constants sit inside geometric case splits~~ | **CLOSED** | M6 done: the chain was parameterised into `Figure5EndpointEnvelopeCore` / `Figure5LocalContactCore` / `UniversalEndpointClosureCore` behind `Figure5EndpointDomain` + `Figure5EndpointAnalyticPackage`, and instantiated at the production tuple by `annFigure5AnalyticPackage`; the historical `100π/5599` facades keep the pre-M6 API unchanged |
| R4 | ~~`CaseIAssemblyConditional`, `UniversalNeedleAdapter`, and `UniversalAssembly` trap the confined core, literal adapter, and transport behind frozen imports~~ | **CLOSED** | M5(c) done: 33 declarations moved into `CaseIRadialCore`, the transport moved into a now-CLEAN `UniversalNeedleAdapter`; the old modules import and reuse them, with every public name and the `100π/5599` receipt preserved |
| R5 | New integral cut has one switch, not two | medium | recompute cut points and log tail; do not port `strongSwitch*` |
| R6 | Margins are small: C1 and C2 clear the target by `1.18e-5` and `1.07e-5` | medium | keep Lean rational enclosures two orders tighter than the margin; the Arb run shows enclosure width `1.75e-6` at 2^16 cells |
| R7 | A copy-paste from `CaseIIAnalytic` could reintroduce `κ` | low | the new payment lemma has a different name and no `caseIIKappa` argument |
| R8 | Full triangle area accidentally added to the interior contribution | low | every exterior statement mentions `\ Metric.closedBall`, so the types prevent it |
| R9 | M3's exit criterion depended on an M4 theorem (dependency inversion), so M3 could never have closed in order | medium | **fixed in this revision**: M3 split into M3a (no fan) and M3b (fan first, then finite theorem); `euclideanPolarAnnulus_outerMeasure_ge` moved M4 → M3b |
| R10 | ~~`ENNReal.ofReal` is not multiplicative, so coefficient extraction silently fails or weakens without a positivity side condition~~ | **CLOSED** | `hCext : 0 < annularCExt ...` stayed an explicit hypothesis of the M3a/M3b/M4 statements and is discharged by `ann_m4_cExt_pos`; M7 additionally converts `ofReal (π · annTarget)` to `ofReal annTarget * ofReal π` under `annTarget_pos` and does the strict step with `ENNReal.mul_lt_mul_left` plus explicit `≠ 0` / `≠ ⊤` side conditions |
| R11 | M7 could silently rely on an invalid `ℝ≥0∞` strict-multiplication cancellation, or on measurability of the direction classes | medium | **CLOSED**: the only strict multiplicative step is `ENNReal.mul_lt_mul_left` (monotone direction, not cancellation), with `L_in + L_out ≠ 0` and `≠ ⊤` proved from `ofReal π ≤ L_in + L_out ≤ 2 · ofReal π`; the mass bound uses coverage and `measure_union_le` only, never an additivity identity |

---

## 6. Explicit non-claims

*This section has been rewritten now that M7 is closed. The pre-M7 wording,
which stated that no joint constant followed and that `100π/5599` was the only
unconditional lower bound in the tree, is **superseded** and is retained only in
the historical status sections of `LEAN-STATUS.md`.*

* No estimate of person-effort or calendar time is given, for any milestone.
* **The route is closed in Lean.** `universal_annular_lower_bound`
  (`AnnularAssembly.lean:233`) is unconditional, has no `sorry`/`admit`/local
  `axiom`/`native_decide` anywhere in its closure, and its `#print axioms`
  receipt is exactly `[propext, Classical.choice, Quot.sound]`.
* `100π/5599` is **not** retracted and **not** rewritten:
  `universal_strong_lower_bound` still compiles with an unchanged statement and
  an unchanged receipt. It is, however, no longer the *only* Lean-proved lower
  bound in this development, and it is no longer the *best* one:
  `131/6250 = 0.02096` exceeds `100/5599 ≈ 0.017 86`. Neither theorem is used in
  the proof of the other.
* No claim is made about the paper-level `PROOF.md` argument beyond what Lean
  now checks. `PROOF.md` remains "not self-contained" in the sense of its own
  evidence-boundary table: it quotes results of
  `paper/star_shaped_kakeya_bounds.tex` verbatim. The Lean development does not
  quote them — it reproves what it needs — so the Lean theorem does not inherit
  that caveat, but neither does it validate the parts of `PROOF.md` it did not
  need.
* `certify.py` / `certificate.json` and `test_annular_geometry.py` remain
  **evidence only**, at the evidence level stated in `README.md`. They are an
  Arb interval certificate and a falsification test; they are not proofs, they
  are not inputs to any Lean proof, and no Lean statement depends on them. The
  Lean gates were reproved from scratch by exact rational and squared-rational
  arithmetic in `AnnularKernel`, `AnnularAnalytic` and `AnnularCaseIIntegral`.
* Every Lean snippet still marked `-- SKETCH` is a proposed shape that was
  written before the corresponding module existed; it has not been type-checked
  and its names need not exist. Snippets in the **[DONE]** M1, M2, M3a, M3b, M4,
  M5 and M7 subsections, and the M5 input contract quoted in the M6 section, are
  *not* sketches: they are compiled signatures, copied from source.
* Every Mathlib name occurring in the M1--M7 modules has been compiled against
  the pinned revision. Names appearing only inside `-- SKETCH` blocks have not.
* The `file:line` references in the **[DONE]** subsections and in §4 were read
  from the tree in the M7 pass and are accurate for that snapshot. Older
  references elsewhere in this document may have drifted.
* **Scope of each branch is unchanged by M7.** M4 still closes the exterior
  branch only and M5 still closes the confined *interface* only; what M6 added
  was the numeric domain, the analytic gates, the radial integral certificate
  and the endpoint parameterisation, and what M7 added was the glue. M7
  introduces no new geometric, analytic or numeric assumption: it consumes only
  `annular_confined_lower_bound`, `annular_exterior_A_out_greedy_lower_bound`,
  `ann_m4_exterior_domain`, `ann_gate_C1`, `ann_m4_coefficient_gt_target`,
  `annTarget_lt_annILower`, `high_branch_outerMeasure`,
  `outerMeasure_ge_add_of_inter_of_diff` and generic Mathlib.
