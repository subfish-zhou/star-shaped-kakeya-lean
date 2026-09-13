# Lean status — spike 001, milestones M1--M7 (route closed)

> **Reading order.** This file grew one *pass* at a time. §1--§21 are the
> historical records of the first five passes (M1, M2, M3a/M3b, M4, M5) and are
> preserved verbatim. Wherever those sections say that M6 or M7 is missing,
> unstarted, owed or "not done", they are describing the state of the tree at
> the time of that pass and are **superseded** by §22. M6 has its own four
> status files (`M6-KERNEL-STATUS.md`, `M6-INTEGRAL-STATUS.md`,
> `M6-ENDPOINT-STATUS.md`, `M6-ANN-ENDPOINT-STATUS.md`); §22 records M7.

**Current status: M0--M7 are all complete. The joint inner/outer route is closed
in Lean.**

```lean
-- StarKakeyaLower/AnnularAssembly.lean:233
theorem universal_annular_lower_bound : UniversalAnnularLowerBound
```

i.e. `ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E` with
`annTarget = 131 / 6250`, for every star-shaped Kakeya set `E`. Receipt:
`[propext, Classical.choice, Quot.sound]`. `universal_strong_lower_bound`
(`100π/5599`) is untouched and still compiles with the same receipt; neither
theorem is used in the proof of the other. See **§22**.

**Scope (historical, by pass).** Milestones **M1** (`BallSplit`: split +
countable ledger), **M2**
(`AnnularGeometry`: weak Prop 4.5 + payment + hull/interior bridge), **M3a** and
**M3b** (`AnnularGreedy`: selected restricted interiors; annular fan; finite
full exterior theorem; finite coefficient elimination with a `min`), and — added
by the fourth pass — **M4** (`AnnularGreedyInfinite`: the countable ledger, the
`B = ⊤` branch, the summable branch, and the outcome wrapper that removes the
`FiniteFixedSelection` input), and — added by the fifth pass — **M5**
(`CaseIRadialCore` + the clean transport layer in `UniversalNeedleAdapter` +
`AnnularCaseI`: the import-clean extraction, the restricted coordinate
transport, and the confined bound at a *variable* interior mass).
*At the time the fifth pass was written, M6–M7 had not been started; that
sentence is now superseded — M6 was closed by four later passes and M7 by the
pass recorded in §22.*
The earlier M1--M4 passes are committed locally; the M5 pass described here and
the M7 pass of §22 are uncommitted, and nothing was pushed. `paper/` was not
touched. All work is in the worktree

```
/home/argustest/research/star-kakeya-wt-joint-lower
```

Lean root:
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`
(toolchain `leanprover/lean4:v4.30.0-rc2`, Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, unchanged).

**Result (fifth pass): M5 is closed, conditionally as specified.** See §20,
including §20.6 for the second-pass fix of the downstream contract (the
confined wrapper now exists for the *positively oriented* family the endpoint
chain actually produces, and the direction-mass normalization bridge to the
exterior branch is proved).
The confined core no longer sits behind the frozen kernel: the 33 generic
declarations at the front of `CaseIAssemblyConditional.lean` were *moved* into
the new `CaseIRadialCore.lean`, whose whole import closure (14 modules) contains
zero frozen witness constants. On top of it, `UniversalNeedleAdapter` now
carries the coordinate transport (moved out of `UniversalAssembly`) plus the new
**restricted** transport, and the new sibling `AnnularCaseI.lean` proves

```
I_lower * L_in ≤ volume.toOuterMeasure (E ∩ Metric.closedBall K.center r₀)
```

for a variable `L_in : ℝ≥0∞`. The generic wrapper takes trace, critical
containment, `hg`, mass, measurability and scalar radial lower-bound inputs. For
the intended constant inner class, M5 closes the mass input via
`directionAngleOuter_le_directionOuterMass_const`; M6 still owes
`htrace`, `hcritical`, `hg`, `hmeas` and `hI`, together with the numeric domain.
No `strongP`, no mass split, no numeric constant.

**Result (fourth pass): M4 is closed.** See §13–§17. `PROOF.md`
Proposition 8.1 (the exterior greedy budget) is now a Lean theorem
`annular_exterior_greedy_lower_bound`, quantified over `K` and an **arbitrary**
`A : Set Direction` with **no** selection supplied by the caller. It is
*unconditional in the deletion budget*: finite stop, summable infinite
selection, and `B = ⊤` are all discharged.

**Result (third pass): M3a and M3b are closed.** See §8–§11. What M3 proved is
the *finite-selection* exterior bound; the caller still had to supply a
`FiniteFixedSelection`. M4 removes that input.

**Result (earlier passes): both of M1 and M2 are closed.** M1 counts as closed only because the
**countable** ledger `tsum_outerMeasure_inter_le` (`PROOF.md` Lemma 7.2)
compiles, not merely the two-set split; before that theorem existed, M1 was
incomplete and is recorded as such in `LEAN-PLAN.md`. No `sorry`, `admit`,
local `axiom`, or `native_decide` occurs in the new source; the `#print axioms`
receipts below are the standard three.

**Revision note.** This file was first written after the initial M1/M2 pass and
has been updated after a review pass which (a) added the countable ledger, (b)
added the hull/interior bridge that M3 previously owed, (c) removed unused
hypotheses from six helper lemmas, and (d) restructured `LEAN-PLAN.md`
(M3 → M3a/M3b, dependency inversion removed). Both new modules now compile with
**zero** warnings.

---

## 1. Files

| File | Lines | Status |
|---|---:|---|
| `StarKakeyaLower/BallSplit.lean` | 77 | M1, green, warning-free |
| `StarKakeyaLower/AnnularGeometry.lean` | 776 | M2, green, warning-free |
| `StarKakeyaLower/AnnularGreedy.lean` | 635 | M3a + M3b, green, warning-free |
| `StarKakeyaLower/AnnularGreedyInfinite.lean` | 539 | M4, green, warning-free |
| `StarKakeyaLower/CaseIRadialCore.lean` | 554 | **M5, new**, green; 5 warnings, all inherited verbatim with the moved proofs |
| `StarKakeyaLower/AnnularCaseI.lean` | 189 | **M5, new**, green, warning-free |
| `StarKakeyaLower/UniversalNeedleAdapter.lean` | 666 | M5, green; 4 inherited `ring` warnings from moved orientation proofs; import changed; transport, orientation normalization and the positive universal family moved in |
| `StarKakeyaLower/SupportReflection.lean` | 240 (−23) | M5, green; three orientation identities moved out, now imports the clean adapter |
| `StarKakeyaLower/UniversalFirstArc.lean` | 428 (−43) | M5, green; `orientPositive` block moved out |
| `StarKakeyaLower/UniversalEndpointClosure.lean` | 468 (−44) | M5, green; positive-family block moved out, strong-tuple material kept |
| `StarKakeyaLower/CaseIAssemblyConditional.lean` | 1282 (−426, +8) | M5, green; front section moved out, Li-specific part kept |
| `StarKakeyaLower/UniversalAssembly.lean` | 189 (−36) | M5, green; two transport theorems moved out |
| `StarKakeyaLower/CaseIEndpointMassIntegral.lean` | 131 (−6) | M5, green; `FirstArcAggregateMass` moved out |
| `StarKakeyaLower.lean` | +5 / −3 (fourth pass), +3 / −3 (fifth pass), +1 import / docstring rewritten (M7 pass) | import list + docstring only |
| `StarKakeyaLower/AnnularAssembly.lean` | 251 | **M7, new**, green, warning-free |
| `StarKakeyaLower/Audit.lean` | +36 / −4 (M7 pass) | one import swapped, all seventeen M7 receipts added |

*Table rows above the last three are as of the fifth pass; the M6 file
inventory is in the four `M6-*-STATUS.md` files.  **Current tree (superseding
the 25 354 figure recorded immediately after M7):** 54 namespace modules under
`StarKakeyaLower/` totalling 25 255 lines, plus the 104-line aggregation root
`StarKakeyaLower.lean`, i.e. 55 files and 25 359 lines in all.  The counting
convention is `wc -l` over `StarKakeyaLower/*.lean` for the namespace figure and
over those files together with `StarKakeyaLower.lean` for the total; `.lake/`
and the `probe/` directory are excluded.  The five-line increase over 25 354
comes from the five permanent Audit receipts added after the first M7 count.*

No pre-existing theorem statement was modified, weakened or deleted.
`universal_strong_lower_bound` is untouched and still compiles with the same
axiom receipt.  Every declaration moved in the fifth pass kept its exact
namespace, name, statement and proof; nothing was copied, renamed or aliased,
and the duplicate-declaration scan is byte-identical to the one at `407b346`.

---

## 2. M1 — `StarKakeyaLower.BallSplit`

Imports: `StarKakeyaLower.StarKakeyaSet` only (which is `import Mathlib` only).

```lean
-- :24   PROOF.md Lemma 7.1
theorem outerMeasure_split_closedBall (E : Set Plane) (o : Plane) (r : ℝ) :
    volume.toOuterMeasure E =
      volume.toOuterMeasure (E ∩ Metric.closedBall o r) +
        volume.toOuterMeasure (E \ Metric.closedBall o r)

-- :34   use site
theorem outerMeasure_ge_add_of_inter_of_diff (E : Set Plane) (o : Plane) (r : ℝ)
    {a b : ENNReal}
    (ha : a ≤ volume.toOuterMeasure (E ∩ Metric.closedBall o r))
    (hb : b ≤ volume.toOuterMeasure (E \ Metric.closedBall o r)) :
    a + b ≤ volume.toOuterMeasure E

-- :53   PROOF.md Lemma 7.2, the COUNTABLE ledger
theorem tsum_outerMeasure_inter_le {A : Set Plane} {M : ℕ → Set Plane}
    (hmeas : ∀ i, MeasurableSet (M i)) (hdisj : Pairwise (Disjoint on M)) :
    ∑' i, volume.toOuterMeasure (A ∩ M i) ≤ volume.toOuterMeasure A
```

The first two are proved from `MeasureTheory.measure_inter_add_diff`,
`MeasureTheory.Measure.toOuterMeasure_apply` and `measurableSet_closedBall`,
exactly as `LEAN-PLAN.md` §M1 anticipated. `E` is arbitrary; no measurability
is assumed.

**The countable ledger.** `tsum_outerMeasure_inter_le` is genuinely countable:
the index type is `ℕ` and the conclusion is a `tsum`, i.e. an infinite series,
not a `Finset.sum`. The plan proposed "finite induction on Carathéodory
splitting followed by `ENNReal.tsum_eq_iSup_sum`"; that is unnecessary. The
proved route is

1. replace `A` by its measurable hull `U = toMeasurable volume A`;
2. `A ∩ M i ⊆ U ∩ M i`, so `volume.toOuterMeasure (A ∩ M i) ≤ volume (U ∩ M i)`
   termwise, via `ENNReal.tsum_le_tsum`;
3. `tsum_meas_le_meas_iUnion_of_disjoint` (Mathlib, itself proved through
   `ENNReal.tsum_eq_iSup_sum`) gives `∑' i, volume (U ∩ M i) ≤ volume (⋃ i, U ∩ M i)`;
4. `measure_mono` into `U`, then `measure_toMeasurable` returns
   `volume.toOuterMeasure A`.

**No measurability of `A` is added.** The hull appears only as an upper bound;
step 4 is an equality of *measures of the hull* with the *outer measure of `A`*,
which is exactly what `measure_toMeasurable` states. `hdisj` is transported to
`fun i => U ∩ M i` by `Disjoint.mono inter_subset_right inter_subset_right`.

---

## 3. M2 — `StarKakeyaLower.AnnularGeometry`

Imports: `StarKakeyaLower.CaseIIGeometry` only.

### 3.1 Sector machinery (layer 3)

```lean
def arcSector (o : Plane) (r0 a b : ℝ) : Set Plane :=
  {z | ∃ r ∈ Icc (0 : ℝ) r0, ∃ θ ∈ Icc a b, z = o + r • angleVector θ}

theorem volume_arcSector_le (o : Plane) {r0 a b : ℝ} (hr0 : 0 ≤ r0)
    (hlen : b - a ≤ Real.pi) :
    volume (arcSector o r0 a b) ≤ ENNReal.ofReal (r0 ^ 2 / 2 * (b - a))
```

**Interface correction (recorded deliberately).** `LEAN-PLAN.md` §M2 sketched
this bound for `euclideanPolarSector o r0 (Set.Icc lo hi)`
(`PolarOuterMeasure.lean:270`). That definition *intersects the angle set with
the standard cut* `Ioo (-π) π`. That is correct for the existing **lower**
bounds, but it cannot be used as the covering set here: a needle's angular arc
can straddle the cut, and then the cut version does not contain the triangle.
`arcSector` therefore carries **no** cut and is a genuinely compact set. The
cut is reintroduced only inside the proof, after an explicit rotation
(`rotLinear`, `LinearMap.det = 1`, `Measure.addHaar_image_linearMap`) has moved
the arc into `Ioo (-π) π`; the bound is then obtained by complementation inside
the disc against the existing
`euclideanPolarSector_outerMeasure_ge` (`PolarOuterMeasure.lean:298`), using
`EuclideanSpace.volume_closedBall` and Carathéodory splitting along the
(compact, hence measurable) sector. The angle set `Set ℝ` and the quotient type
`Direction` are never mixed.

### 3.2 One-sidedness and the arc (layers 1 and 2)

```lean
def supportCoord (t : ℝ) (x : Plane) : ℝ := x 0 * Real.cos t + x 1 * Real.sin t

theorem supportCoord_sq_add_normalCoord_sq (t : ℝ) (x : Plane) :
    supportCoord t x ^ 2 + normalCoord t x ^ 2 = ‖x‖ ^ 2

theorem UnitNeedle.exists_arcSector_of_outside
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hrho : 0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ∃ a : ℝ, n.triangleHull o ∩ Metric.closedBall o r0 ⊆
      arcSector o r0 a (a + Real.arcsin (n.height o / rho))
```

One-sidedness is proved for the **entire closed unit segment**, not for the
endpoints:

* `supportCoord t (K - o) ≠ 0` for every `K ∈ n.carrier`, because
  `supportCoord² + normalCoord² = ‖K - o‖²`, `|normalCoord| = height < rho` and
  `rho ≤ ‖K - o‖` (this is `OutsideBall`, used at every point of the segment);
* `supportCoord` is **affine** in the segment parameter with slope `1` in the
  oriented lift `t = vectorAngle (right - left)`, so a nonvanishing affine
  function on `[0,1]` has constant sign; the negative case is handled by the
  opposite lift `t + π` (`angleVector_add_pi`, `supportCoord_add_pi`), which is
  a legitimate direction lift with scalar `-1`.

The arc itself is produced by `eq_smul_angleVector_arcsin`: whenever the
tangential coordinate is positive,
`x = ‖x‖ • angleVector (t + Real.arcsin (normalCoord t x / ‖x‖))`. The normal
coordinate is constant along the needle (`UnitNeedle.normalCoord_carrier_eq`)
and has absolute value `height` (`UnitNeedle.abs_normalCoord_left_eq_height`),
so all rays land in one real `Set.Icc` of length at most `arcsin (height / rho)`
with a fixed sign, giving `[t, t+A]` or `[t-A, t]`.

### 3.3 Triangle area and the exterior theorem (layers 4 and 5)

```lean
theorem UnitNeedle.volume_triangleHull_eq (o : Plane) (n : UnitNeedle) :
    volume (n.triangleHull o) = ENNReal.ofReal (n.height o / 2)

theorem UnitNeedle.volume_triangleHull_diff_closedBall_ge
    {rho r0 : ℝ} {o : Plane} {n : UnitNeedle}
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hdelta : n.height o < rho) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (n.height o / 2 - r0 ^ 2 / 2 * Real.arcsin (n.height o / rho)) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0)
```

This is `PROOF.md` Proposition 4.5 in its weak form, as instructed.

Hull/interior and boundary conventions are explicit:
`UnitNeedle.volume_triangleHull_eq` is derived from the existing public
`UnitNeedle.volume_triangleInterior` (`TriangleArea.lean:280`) together with
`UnitNeedle.volume_frontier_triangleHull` (`:296`) via
`closure_eq_interior_union_frontier`; the private `volume_triangleHull` of
`TriangleArea.lean` was *not* touched or unsealed. Deleted set is the **closed**
ball, matching `PROOF.md` §1. The `height = 0` case needs no separate treatment:
the arc degenerates to a point and both sides are `0`.

### 3.4 Calculus and the payment corollary (layer 6)

Both calculus inputs are instances of `strictConcaveOn_sin_Icc`; no derivative
argument is repeated.

```lean
theorem sin_chord_le {u u0 : ℝ} (hu0 : 0 < u0) (hu0pi : u0 ≤ Real.pi)
    (hu : 0 ≤ u) (huu0 : u ≤ u0) : u / u0 * Real.sin u0 ≤ Real.sin u   -- Lemma 5.1

theorem arcsin_mul_sin_le {m u : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ Real.pi / 2) :
    Real.arcsin (m * Real.sin u) ≤ m * u                                -- Lemma 5.2

def annularCExt (a r0 rho m : ℝ) : ℝ :=
  a / (2 * Real.arcsin (a / (m * rho))) - m * r0 ^ 2 / 2                -- (2.3)

theorem UnitNeedle.annular_payment
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle}
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hheight : n.height o ≤ a) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleHull o \ Metric.closedBall o r0)                -- Prop. 5.3
```

`annularCExt` is a free real parameter combination; **no positivity of
`annularCExt` is assumed or claimed** (the certificate gate `C_ext_positive` is
not a Lean statement). `n.height o = 0` is handled by a separate branch inside
the proof, where `arcsin (0 / (m*rho)) = 0` makes the left-hand side `0`; the
division `a / (2 * arcsin (a / (m*rho)))` is never evaluated at a zero
denominator on the used branch, because `ha : 0 < a` and `harho : a < m*rho`
force `0 < arcsin (a / (m*rho))`.

### 3.5 Hull / interior bridge (M3 prerequisite, delivered in M2)

```lean
-- AnnularGeometry.lean:741
theorem UnitNeedle.volume_triangleInterior_diff_closedBall
    (o : Plane) (n : UnitNeedle) (r0 : ℝ) :
    volume (n.triangleInterior o \ Metric.closedBall o r0) =
      volume (n.triangleHull o \ Metric.closedBall o r0)

-- AnnularGeometry.lean:763
theorem UnitNeedle.annular_payment_triangleInterior
    {a r0 rho m : ℝ} {o : Plane} {n : UnitNeedle}
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hheight : n.height o ≤ a) (hout : n.OutsideBall rho o) :
    ENNReal.ofReal
        (annularCExt a r0 rho m * Real.arcsin (n.height o / (m * rho))) ≤
      volume (n.triangleInterior o \ Metric.closedBall o r0)
```

`LEAN-PLAN.md` originally made **M3** responsible for "an explicit boundary-zero
lemma showing that deleting the closed ball does not change the equality of hull
and interior volumes". That lemma is single-needle geometry, so it is proved
here instead, and `LEAN-PLAN.md` has been revised accordingly.

Proof: `≤` is `measure_mono` on `interior ⊆ hull`; `≥` uses
`hull \ ball ⊆ (interior \ ball) ∪ frontier hull` (a point of the hull is
either interior or, being in the closure, in the frontier), then
`measure_union_le` and `UnitNeedle.volume_frontier_triangleHull = 0`
(`TriangleArea.lean:296`, itself `Convex.addHaar_frontier`). The deleted set is
the **closed** ball on both sides, matching `PROOF.md` §1.

**This is a volume identity only.** It does **not** assert that closed hulls are
pairwise disjoint, and nothing in either new module makes that claim. The
downstream finite sum must still be taken over the open `triangleInterior`
family, where `pairwise_disjoint_triangleInterior_of_outside`
(`CaseIIGeometry.lean:1067`) applies;
`UnitNeedle.annular_payment_triangleInterior` is provided so that M3a never has
to touch a hull at all.

### 3.6 Hypothesis hygiene

Five helper lemmas carried hypotheses their proofs did not use. They were
removed and the call sites updated, so both modules now compile with **zero**
warnings:

| Lemma | removed |
|---|---|
| `arcSector_subset_closedBall` | `hr0 : 0 ≤ r0` (and `r0` made explicit) |
| `volume_arcSector_le_of_mem_cut` (private) | `hab : a ≤ b` |
| `volume_arcSector_le` | `hab : a ≤ b` (propagated) |
| `UnitNeedle.normalCoord_carrier_eq` | `hc : \|c\| = 1` |
| `UnitNeedle.triangleHull_inter_closedBall_subset_arcSector_of_pos` | `hr0`, `hdelta` |
| `UnitNeedle.exists_arcSector_of_outside` | `hr0 : 0 ≤ r0` (propagated) |

Every removal makes the lemma strictly more general, so no downstream use is
weakened. **The hypotheses of the two public annular theorems
(`UnitNeedle.volume_triangleHull_diff_closedBall_ge` and
`UnitNeedle.annular_payment`) are unchanged.** One style-linter `show` was
replaced by `change` (definitional, `carrier` unfolds to `segment` by `rfl`).

---

## 4. Exact build output

Baseline before the pass (unchanged behaviour afterwards):

```
$ ulimit -n 65535; lake build StarKakeyaLower
Build completed successfully (8346 jobs).
```

After the review pass, with both new files `touch`ed so they are genuinely
recompiled rather than replayed:

```
$ ulimit -n 65535; lake build StarKakeyaLower.BallSplit
Build completed successfully (8314 jobs).

$ ulimit -n 65535; lake build StarKakeyaLower.AnnularGeometry
Build completed successfully (8323 jobs).

$ ulimit -n 65535; lake build StarKakeyaLower
✔ [8347/8348] Built StarKakeyaLower (3.6s)
Build completed successfully (8348 jobs).

$ ulimit -n 65535; lake build StarKakeyaLowerAudit
info: StarKakeyaLower/Audit.lean:385:0: 'StarKakeyaLower.universal_strong_lower_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8348 jobs).
```

**The two new files now emit no warnings at all**; the only diagnostics printed
during these builds come from pre-existing modules (`StarKakeyaSet.lean`,
`UniversalAssembly.lean`), which were not modified.

Forbidden-token scan of the two new files:

```
$ grep -nE "\bsorry\b|\badmit\b|^axiom |\baxiom \b|native_decide" \
    StarKakeyaLower/AnnularGeometry.lean StarKakeyaLower/BallSplit.lean
(no matches)

$ git diff --check
(no output)
```

## 5. Axiom receipts

Obtained with `#print axioms` from a throw-away module (removed afterwards):

```
'StarKakeyaLower.outerMeasure_split_closedBall'                       [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.outerMeasure_ge_add_of_inter_of_diff'                [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.tsum_outerMeasure_inter_le'                          [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.volume_arcSector_le'                                 [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.UnitNeedle.exists_arcSector_of_outside'              [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.UnitNeedle.volume_triangleHull_diff_closedBall_ge'   [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.UnitNeedle.annular_payment'                          [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.UnitNeedle.volume_triangleInterior_diff_closedBall'  [propext, Classical.choice, Quot.sound]
'StarKakeyaLower.UnitNeedle.annular_payment_triangleInterior'         [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, and no local axiom of this development. The temporary audit module
was deleted after the receipts were taken; it is not part of either build
target.

## 6. Transitive frozen dependencies

Computed from the `import StarKakeyaLower.*` closure of each new module, against
the FROZEN list of `LEAN-PLAN.md` §1.

| Module | transitive `StarKakeyaLower` imports | FROZEN in closure |
|---|---|---|
| `BallSplit` | `StarKakeyaSet` | **none** |
| `AnnularGeometry` | `CaseIIGeometry`, `CircleDilation`, `GreedyResidual`, `LiGeometry`, `ParametricCaseII`, `PolarOuterMeasure`, `QuotientCircle`, `StarKakeyaSet`, `TriangleArea`, `Trichotomy` | **none** |

Every module in both closures is CLEAN in the `LEAN-PLAN.md` §1 sense (zero
occurrences of `strongA`, `strongR₀`, `strongRLambda`, `strongR₁`, `strongRho`,
`strongP`, `strongTarget`, `altA`, `altTarget` in its own text), so the two new
modules are usable in a clean context, not merely constant-free in their bodies.

Both modules are now imported by the production root `StarKakeyaLower.lean`.
This introduces no cycle (nothing imports the root) and no frozen dependency;
`universal_strong_lower_bound` does not depend on either module.

---

## 7. Historical M2 status (superseded by the third pass where noted)

1. **Weak form only.** The sharp one-sided width `W_ρ` (`PROOF.md` Lemma 4.3),
   `annularWidth`, and Remark 4.6's sharpness identity are **not** formalised.
   Only `A(s) ≤ arcsin(δ/ρ)` is proved, which is what `PROOF.md` §5 uses. If a
   later milestone needs the sharp constant, it is new work.
2. **`volume_arcSector_le` carries `b - a ≤ π`.** This is not a restriction at
   the use site (`b - a = arcsin(·) ≤ π/2`), but the theorem as stated says
   nothing for wider arcs.
3. ~~Unused hypotheses kept for interface uniformity.~~ **Resolved**: all six
   unused hypotheses listed in §3.6 were removed and the call sites updated.
   The two public annular theorems keep their original hypotheses.
4. **At the end of M2, nothing about the joint bound was proved.** Those two
   modules contained the
   generic countable ledger of Lemma 7.2, but no exterior-ledger assembly, no
   greedy selection and no numeric constant. This item is superseded by the
   finite-selection M3 results in §§8--12; the unconditional proposition still
   remains M4.
   In particular M2 alone did not establish that
   `ENNReal.ofReal (Real.pi * (131 / 6250)) < volume.toOuterMeasure E` is closer
   to being a Lean theorem than before, beyond the fact that M1 and M2 no longer
   block it.
5. **M1--M2 were committed** on `research/joint-lower-bound-spike` in
   `3b296a2`; the M3 changes described below are the current uncommitted pass.
6. **`tsum_outerMeasure_inter_le` is Lemma 7.2 only, not Corollary 7.3.** The
   *finite exterior ledger* of `PROOF.md` Cor 7.3 is now implemented in M3b.
   The countable/infinite consumption of Lemma 7.2 remains M4.
7. **`LEAN-PLAN.md` was revised in the same pass**, not only annotated: M1's
   exit criterion now requires the countable ledger, M3 is split into M3a
   (selected restricted interiors, no fan) and M3b (fan first, then the finite
   theorem), `euclideanPolarAnnulus_outerMeasure_ge` moved from M4 to M3b to
   remove the dependency inversion, `hCext : 0 < annularCExt ...` is now an
   explicit hypothesis wherever a coefficient is pulled through
   `ENNReal.ofReal_mul`, and M4 is restricted to the infinite / summable / `⊤`
   branches. Risks R1 and R2 are recorded as closed; R9 and R10 were added.

---

# Third pass — M3a and M3b (`StarKakeyaLower/AnnularGreedy.lean`)

## 8. M3a — selected restricted interiors, no fan

New module `StarKakeyaLower/AnnularGreedy.lean` (634 lines).
Imports: `StarKakeyaLower.AnnularGeometry` and `StarKakeyaLower.CaseIISelection`
only. **`BallSplit` is *not* imported** — see §11, correction (6).

All declarations below live in `namespace StarKakeyaLower.FiniteFixedSelection`
with section variables `{height H : Direction → ℝ} {m a : ℝ} {A : Set Direction}`.
Line numbers are of `AnnularGreedy.lean` as committed to the worktree.

```lean
-- :50   the object every exterior sum runs over: an OPEN triangle minus a ball
def restrictedTriangle (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) (i : Fin F.N) : Set Plane :=
  (K.needleFamily (F.selected i)).triangleInterior K.center \
    Metric.closedBall K.center r0

-- :62
def restrictedSelectedUnion (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ) : Set Plane :=
  ⋃ i : Fin F.N, F.restrictedTriangle K r0 i

-- :89   disjointness by MONOTONICITY from the existing pairwise theorem
theorem pairwise_disjoint_restrictedTriangle
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (r0 : ℝ) :
    Pairwise (fun i j : Fin F.N => Disjoint
      (F.restrictedTriangle K r0 i) (F.restrictedTriangle K r0 j))

-- :108  finite union / sum volume IDENTITY on the restricted interiors
theorem volume_restrictedSelectedUnion (F : FiniteFixedSelection height H m A)
    {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ)
    (hpair : Pairwise (fun i j : Fin F.N => Disjoint
      (F.restrictedTriangle K r0 i) (F.restrictedTriangle K r0 j))) :
    volume (F.restrictedSelectedUnion K r0) =
      ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i)

-- :120
theorem sum_volume_restrictedTriangle_le_outerMeasure
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (r0 : ℝ) :
    ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

-- :141  PROOF.md (8.2), the payment; hCext is what licenses ENNReal.ofReal_mul
theorem cost_le_sum_volume_restrictedTriangle
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (ha : 0 < a) (harho : a < m * rho) (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho m) *
        ∑ i : Fin F.N, ENNReal.ofReal (H (F.selected i)) ≤
      ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i)

-- :169  ***M3a EXIT THEOREM***  — no residual-fan term, no M3b/M4 dependency
theorem selected_exterior_sum_le_outerMeasure_finite
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

-- :192, :215, :234  deletion-budget (`C_ext/4` against `Σ 4 H_i`) restatements
theorem quarter_cost_eq_cost ...
theorem quarter_cost_le_sum_volume_restrictedTriangle ...
theorem quarter_cost_le_outerMeasure_finite
    ... :
    ENNReal.ofReal (annularCExt a r0 rho m / 4) *
        ∑ i : Fin F.N, ENNReal.ofReal (4 * H (F.selected i)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

Facts about M3a that matter for the audit.

* **Closed hulls are never summed.** Every disjointness statement, every sum
  and the union `restrictedSelectedUnion` are on `triangleInterior · \ closedBall`.
  The single passage to the hull is inside M2's
  `UnitNeedle.annular_payment_triangleInterior`, which is a *volume* identity
  (`volume_triangleInterior_diff_closedBall`), not a disjointness claim.
* **Disjointness is obtained by monotonicity only.** The proof of
  `pairwise_disjoint_restrictedTriangle` is one line:
  `(F.pairwise_disjoint_triangles … hij).mono diff_subset diff_subset`.
* **`hCext` is used exactly where the plan said it would be**, in
  `cost_le_sum_volume_restrictedTriangle` (`← ENNReal.ofReal_mul hCext.le`) and
  in `quarter_cost_eq_cost`. Nonnegativity of `H (F.selected i)` is *derived*
  (`Real.arcsin_nonneg` applied to `hpos`/`hH`), not assumed.
* **The exit theorem mentions no fan.** `residualFan`, `residualAngles`,
  `angleSetOuter` and `euclideanPolarAnnulus_outerMeasure_ge` all occur strictly
  after line 254, i.e. after `end FiniteFixedSelection` closes the M3a block.

## 9. M3b — the annular fan, then the finite full exterior theorem

### 9.1 The fan bound, proved before its first use

```lean
-- :336  polar description of the exterior of a sector
def euclideanAnnulusSector (o : Plane) (r0 rho : ℝ) (Θ : Set ℝ) : Set Plane :=
  {z | ∃ r ∈ Ioc r0 rho, ∃ θ ∈ Θ ∩ Ioo (-Real.pi) Real.pi, z = o + r • angleVector θ}

-- :407  ***PROOF.md (B5)***  Θ is ARBITRARY: no measurability is assumed
theorem euclideanPolarAnnulus_outerMeasure_ge (o : Plane) {r0 rho : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (Θ : Set ℝ) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * angleSetOuter Θ ≤
      volume.toOuterMeasure
        (euclideanPolarSector o rho Θ \ Metric.closedBall o r0)

-- :432  exterior analogue of residualFan_outerMeasure_lower
theorem StarShapedKakeya.residualFan_annulus_outerMeasure_lower
    {E : Set Plane} (K : StarShapedKakeya E)
    {r0 rho : ℝ} (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (R : Set Direction)
    (hzero : ∀ theta ∈ R, (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ R, (K.needleFamily theta).OutsideBall rho K.center) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter R ≤
      volume.toOuterMeasure
        (residualFan K R \ Metric.closedBall K.center r0)
```

`euclideanPolarAnnulus_outerMeasure_ge` is at line 407 and its first consumer
(`residualFan_annulus_outerMeasure_lower`) at line 432, so the plan's
dependency inversion is genuinely removed.

How it is proved, and the two things the plan did not foresee.

1. **Outer measure is used correctly.** The whole chain goes through
   `outerMeasure_ge_lintegral_of_angleOuter_ge` (`PolarOuterMeasure.lean:158`),
   whose whole point is that `Θ`, the sector and the annulus may all be
   nonmeasurable; only a *measurable radial minorant* is supplied. No measurable
   hull of `Θ` and no upper bound on any sector is used, which is essential —
   the subtractive route (`sector(ρ) = sector(r₀) ⊔ annulus`) would need an
   upper bound on `sector(r₀)` and is **false** as a route for nonmeasurable `Θ`.
2. **The integrand must be cut at `r₀`.** At `r = r₀` the angular section of
   `sector \ closedBall o r₀` is *empty*, so a constant section bound on the
   closed interval `Icc r₀ ρ` is false at its left endpoint. `PROOF.md` §8.4
   handles this by integrating on `[r₁, ρ]` and letting `r₁ ↓ r₀`; the Lean
   proof instead integrates the cut integrand
   `fun r => ENNReal.ofReal r * (if r₀ < r then angleSetOuter Θ else 0)` over
   `Icc r₀ ρ`, and removes the single null radius by
   `lintegral_congr_ae` (`AnnularGreedy.lean:273`,
   `lintegral_annulus_radius_mul_const`). No limit is needed.
3. **The oriented-lift / projective-quotient bookkeeping is reused unchanged.**
   `directionAngleOuter_le_residualAngles` (`CaseIIGeometry.lean:866`) and
   `residualAngles_outerMeasure_le_angleSetOuter` (`:914`) are exactly Lemma 8.3
   of `PROOF.md`, cut point included; `polarSector_residualAngles_subset_residualFan`
   (`:878`) transfers to the fan and survives `diff_subset_diff_left`.

### 9.2 The finite full exterior theorem and the coefficient elimination

```lean
-- :465
theorem FiniteFixedSelection.disjoint_restrictedResidualFan_restrictedSelectedUnion
    (F : FiniteFixedSelection height H m A) … (r0 : ℝ) :
    Disjoint (residualFan K F.residual \ Metric.closedBall K.center r0)
      (F.restrictedSelectedUnion K r0)

-- :488  ***PROOF.md (8.3b)***  the sum is over the OPEN restricted interiors
theorem FiniteFixedSelection.geometric_exterior_outerMeasure_lower_finite
    (F : FiniteFixedSelection height H m A)
    (hm0 : 0 < m) (hm1 : m < 1) (hbound : ∀ θ ∈ A, height θ ≤ a)
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (hzero : ∀ theta ∈ F.residual,
      (K.needleFamily theta).height K.center = 0)
    (hheight : ∀ θ, height θ = (K.needleFamily θ).height K.center)
    (hpos : ∀ i, 0 < height (F.selected i))
    (hscaled : ∀ i, height (F.selected i) < m * rho)
    (hH : ∀ i, H (F.selected i) =
      Real.arcsin (height (F.selected i) / (m * rho)))
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) * directionAngleOuter F.residual +
        ∑ i : Fin F.N, volume (F.restrictedTriangle K r0 i) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

-- :538  min-coefficient minimax; no κ, no comparison with ρ²/2
theorem round2_min_initial_angle_lower_bound
    {q p s L R B b M : ENNReal}
    (hqs : q ≤ s) (hqp : q ≤ p) (hcover : L ≤ R + B)
    (hpayment : p * B ≤ b) (hgeom : s * R + b ≤ M) : q * L ≤ M

-- :555  ***M3b EXIT THEOREM***
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

-- :618  canonical (height, paper-weight) specialization for a supplied F
theorem annular_exterior_lower_bound_of_finiteSelection_paperWeight
    {E : Set Plane} (K : StarShapedKakeya E) {A : Set Direction} {a r0 rho m : ℝ}
    (F : FiniteFixedSelection (fun θ => (K.needleFamily θ).height K.center)
      (fun θ => Real.arcsin ((K.needleFamily θ).height K.center / (m * rho))) m A)
    (hm0 : 0 < m) (hm1 : m < 1) (ha : 0 < a) (harho : a < m * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho m)
    (hout : ∀ θ ∈ A, (K.needleFamily θ).OutsideBall rho K.center)
    (hlow : ∀ θ ∈ A, (K.needleFamily θ).height K.center < a) :
    ENNReal.ofReal (min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter A ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

Facts that matter for the audit.

* **Everything is finite.** `Fin F.N`-indexed `Finset.sum` throughout; the only
  `tsum` that appears is the one produced by the existing
  `initial_directionAngleOuter_le_residual_add_cost`, converted immediately by
  `tsum_fintype`. No `infiniteGreedyData`, no `Summable`, no
  `summable_of_cost_tsum_ne_top`, no `⊤` case analysis is used anywhere in the
  module (`grep -c "infiniteGreedyData\|Summable\|tsum_ne_top" = 0`).
* **The deletion coverage budget is the existing finite one.**
  `FiniteFixedSelection.initial_directionAngleOuter_le_residual_add_cost`
  (`CaseIISelection.lean:930`) is `PROOF.md` (B1); it is used as the `hcover`
  argument of the min-minimax.
* **No `κ` anywhere.** `caseIIKappa` and `caseIIC` do not occur in
  `AnnularGreedy.lean`; `caseII_paperWeight_paid_by_height` is replaced by
  `UnitNeedle.annular_payment_triangleInterior` as the plan required.
* **`hCext` remains explicit** in every theorem that pulls a coefficient through
  `ENNReal.ofReal`, up to and including the exit theorem.
* **`Θ`-side hypotheses were not strengthened.** `A` is an arbitrary
  `Set Direction`; `F.residual` is arbitrary; the only measurability used
  anywhere is of `triangleInterior` (open), of `Metric.closedBall`, and of the
  measurable hull inside the pre-existing `PolarOuterMeasure` machinery.

## 10. Build output, receipts and scans (third pass)

```
$ ulimit -n 65535; lake build StarKakeyaLower.AnnularGreedy
✔ [8325/8325] Built StarKakeyaLower.AnnularGreedy (5.4s)
Build completed successfully (8325 jobs).

$ ulimit -n 65535; lake build StarKakeyaLower
✔ [8348/8349] Built StarKakeyaLower (3.6s)
Build completed successfully (8349 jobs).

$ ulimit -n 65535; lake build StarKakeyaLowerAudit
info: StarKakeyaLower/Audit.lean:385:0:
  'StarKakeyaLower.universal_strong_lower_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8348 jobs).
```

`AnnularGreedy.lean` emits **zero** diagnostics of its own; every warning seen
during these builds comes from pre-existing, unmodified modules.

`#print axioms` receipts, taken from a throw-away module `TempAudit.lean` which
was deleted immediately afterwards (it is in neither Lake target):

```
'…FiniteFixedSelection.pairwise_disjoint_restrictedTriangle'                  [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.volume_restrictedSelectedUnion'                        [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.sum_volume_restrictedTriangle_le_outerMeasure'         [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.cost_le_sum_volume_restrictedTriangle'                 [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.selected_exterior_sum_le_outerMeasure_finite'          [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.quarter_cost_le_sum_volume_restrictedTriangle'         [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.quarter_cost_le_outerMeasure_finite'                   [propext, Classical.choice, Quot.sound]
'…euclideanPolarAnnulus_outerMeasure_ge'                                      [propext, Classical.choice, Quot.sound]
'…StarShapedKakeya.residualFan_annulus_outerMeasure_lower'                    [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.disjoint_restrictedResidualFan_restrictedSelectedUnion' [propext, Classical.choice, Quot.sound]
'…FiniteFixedSelection.geometric_exterior_outerMeasure_lower_finite'          [propext, Classical.choice, Quot.sound]
'…round2_min_initial_angle_lower_bound'                                       [propext, Classical.choice, Quot.sound]
'…annular_exterior_lower_bound_of_finiteSelection'                            [propext, Classical.choice, Quot.sound]
'…annular_exterior_lower_bound_of_finiteSelection_paperWeight'                [propext, Classical.choice, Quot.sound]
```

Scans:

```
$ grep -nE "\bsorry\b|\badmit\b|^axiom |\baxiom \b|native_decide|unsafe |partial def" \
    StarKakeyaLower/AnnularGreedy.lean
(no matches)

$ grep -rnE "\bsorry\b|\badmit\b|^axiom |native_decide" StarKakeyaLower/ StarKakeyaLower.lean
(no matches)

$ git status --short   # snapshot before updating this STATUS/PLAN text
 M …/04-lean/StarKakeyaLower.lean
?? …/04-lean/StarKakeyaLower/AnnularGreedy.lean

$ git --no-pager diff --stat
 …/04-lean/StarKakeyaLower.lean | 12 +++++++-----
 1 file changed, 7 insertions(+), 5 deletions(-)
```

At that build snapshot the only tracked Lean file modified was the production
root, and only its `import` list and docstring. Updating this report and the plan
also modifies the two tracked Markdown files. No existing theorem statement was
touched.

Frozen-dependency check of the new module, against the FROZEN list of
`LEAN-PLAN.md` §1:

| Module | transitive `StarKakeyaLower` imports | FROZEN in closure |
|---|---|---|
| `AnnularGreedy` | `AnnularGeometry`, `CaseIIGeometry`, `CaseIISelection`, `CircleDilation`, `GreedyResidual`, `LiGeometry`, `ParametricCaseII`, `PolarOuterMeasure`, `QuotientCircle`, `StarKakeyaSet`, `TriangleArea`, `Trichotomy` | **none** |

Every module in the closure has zero occurrences of `strongA`, `strongR₀`,
`strongRLambda`, `strongR₁`, `strongRho`, `strongP`, `strongTarget`, `altA`,
`altTarget` in its own text, so `AnnularGreedy` is CLEAN in both senses.

## 11. Interface corrections discovered while executing M3a/M3b

These are recorded here and, where they change an interface rather than a
result, mirrored into `LEAN-PLAN.md`. **No exit criterion was weakened.**

1. **`FiniteFixedSelection` imposes no relation between `H` and
   `arcsin(δ/(mρ))`.** The structure (`CaseIISelection.lean:175`) stores only
   `selected`, `residual`, `selected_eq`, `residual_eq`, `positive_before`,
   `stopped`; `H` is an arbitrary `Direction → ℝ` used solely as the deletion
   radius. Every downstream geometric theorem therefore threads the relation as
   an explicit hypothesis — `pairwise_disjoint_triangles` (`:763`) already does.
   The M3a sketch in `LEAN-PLAN.md` displayed only `(F …) (hCext …)`; the real
   theorem additionally carries `hm0 hm1 hbound hheight hpos hscaled hH hout`,
   exactly as `geometric_outerMeasure_lower` (`:876`) does. This is a
   *completion* of the sketch, not a weakening.
2. **The disjointness input is the selection-level theorem, not the raw
   geometry lemma.** The plan listed
   `pairwise_disjoint_triangleInterior_of_outside` (`CaseIIGeometry.lean:1067`).
   What M3a actually needs is `FiniteFixedSelection.pairwise_disjoint_triangles`
   (`CaseIISelection.lean:763`), which already discharges the (B2) shadow
   separation from the greedy data; the raw lemma would require re-deriving it.
3. **`PolarOuterMeasure`'s coordinate transfer is `private`.**
   `planeCoordinates` (`PolarOuterMeasure.lean:244`),
   `planeCoordinates_measurePreserving` (`:247`) and
   `outerMeasure_preimage_le_of_measurePreserving` (`:252`) are all `private`
   and therefore unusable from another module. `AnnularGreedy.lean` contains a
   local, identical copy (`planeCoords`, `:342`). This is duplicated *definition
   and proof*, not a new assumption. (`UniversalNeedleAdapter.planeCoordinateEquiv`
   is public but that module's import closure is not CLEAN, so it cannot be used.)
4. **The annulus section bound fails at `r = r₀`.** See §9.1, point 2. The plan's
   sketch of `euclideanPolarAnnulus_outerMeasure_ge` gave the statement, which is
   correct, but a constant section bound over the closed `Icc r₀ ρ` is not
   available; the null-radius cut is required. This is a proof-technique
   correction, not a statement change.
5. **The M3b exit theorem cannot be quantified over `A` alone.** The sketch
   `annular_exterior_greedy_lower_bound` in `LEAN-PLAN.md` §M4 takes only
   `K` and `A`; producing it requires `fixedSelectionOutcome` and hence the
   infinite branch, which is M4. M3b's exit theorem is therefore stated for a
   **given** `F : FiniteFixedSelection height H m A`, with `height` and `H`
   abstract plus their defining equations as hypotheses — the strongest form the
   finite API supports. The corollary
   `annular_exterior_lower_bound_of_finiteSelection_paperWeight` instantiates
   both by `rfl`. This proves canonical instantiability for a supplied finite
   selection, not existence of that selection; outcome case exhaustion is M4.
6. **M3a/M3b do not import `BallSplit`.** `LEAN-PLAN.md` §M3 listed `BallSplit`
   among the imports. In the *finite* case, `PROOF.md` Corollary 7.3 is the
   two-set Carathéodory separation, already available as
   `outerMeasure_add_le_of_disjoint_measurable` (`CaseIIGeometry.lean:1418`),
   plus finite additivity `measure_iUnion` over `Fin F.N`. M1's genuinely
   countable ledger `tsum_outerMeasure_inter_le` is first needed by the
   unconditional cone-only inequality `PROOF.md` (8.3a), which is M4. The import
   was therefore dropped rather than kept unused.

## 12. Historical end-of-M3 status (superseded by the fourth pass)

At the end of M3, nothing in the table below existed. Section 13 onward records
the completed M4 implementation and supersedes the M4 row.

| Milestone | What was missing at the end of M3 | Status now |
|---|---|---|
| **M4** | The unconditional exterior outcome wrapper and infinite branches. The implementation later found that neither M1's countable ledger nor `residual_height_zero_of_summable_cost` was needed; see corrections F–H. | **DONE in §§13–19** |
| **M5** | Restricted coordinate transport `outerMeasure_centeredCoordinate_image_inter_closedBall`, and variable interior mass (the current plumbing hardwires `strongCaseIQ`). Both on the confined side. | still missing |
| **M6** | Hypothesis B/C kernel and endpoint containment for the new parameter tuple, including `hCext : 0 < annularCExt a r0 rho (1 - eps)` as a *numeric* fact. | still missing |
| **M7** | Final assembly `universal_annular_lower_bound`. | still missing |

At that historical checkpoint only the finite-selection exterior case was
formalised. M4 now completes the exterior branch, but not the final joint
theorem. `universal_strong_lower_bound` (`100π/5599`) remains the only
unconditional lower bound in the tree, unchanged and with an unchanged axiom
receipt.

---

# Fourth pass — M4 (`StarKakeyaLower/AnnularGreedyInfinite.lean`)

## 13. Scope and module placement

New module `StarKakeyaLower/AnnularGreedyInfinite.lean` (539 lines), importing
`StarKakeyaLower.AnnularGreedy` only.  `LEAN-PLAN.md` §M4 said "add to
`AnnularGreedy.lean`"; the material was put in a **clean sibling** instead
(explicitly permitted). Two reasons: `AnnularGreedy.lean` would have grown past
1050 lines, and keeping M3 in a separate compilation unit makes the claim "M4
uses M3a/M3b as black boxes" checkable by import rather than by reading.

M4 adds **no new geometry**.  Every planar estimate it uses is M2's
`UnitNeedle.annular_payment_triangleInterior` or M3b's
`StarShapedKakeya.residualFan_annulus_outerMeasure_lower`.  What is new is the
countable ledger and the case analysis.

All declarations in §14–§15 live in
`namespace StarKakeyaLower.FixedDeletionGreedyData` with section variables
`{height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)`.  Line
numbers are of `AnnularGreedyInfinite.lean` as it stands in the worktree.

## 14. The countable ledger and the `B = ⊤` branch (`PROOF.md` (8.3a))

```lean
-- :46   ℕ-indexed restricted OPEN triangle
def restrictedTriangle {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ)
    (n : ℕ) : Set Plane :=
  (K.needleFamily (G.selected n)).triangleInterior K.center \
    Metric.closedBall K.center r0

-- :58
def restrictedSelectedUnion {E : Set Plane} (K : StarShapedKakeya E)
    (r0 : ℝ) : Set Plane := ⋃ n, G.restrictedTriangle K r0 n

-- :85   disjointness by MONOTONICITY from the existing countable theorem
theorem pairwise_disjoint_restrictedTriangle
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (r0 : ℝ) :
    Pairwise (fun i j => Disjoint (G.restrictedTriangle K r0 i)
      (G.restrictedTriangle K r0 j))

-- :106  countable exterior additivity
theorem volume_restrictedSelectedUnion {E : Set Plane}
    (K : StarShapedKakeya E) (r0 : ℝ)
    (hpair : Pairwise (fun i j => Disjoint (G.restrictedTriangle K r0 i)
      (G.restrictedTriangle K r0 j))) :
    volume (G.restrictedSelectedUnion K r0) =
      ∑' n, volume (G.restrictedTriangle K r0 n)

-- :117  THE COUNTABLE EXTERIOR LEDGER — selected cones only
theorem tsum_volume_restrictedTriangle_le_outerMeasure
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho) … :
    (∑' n, volume (G.restrictedTriangle K r0 n)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

-- :138  itemwise M2 payment, summed; hCext licenses ENNReal.ofReal_mul
theorem cost_le_tsum_volume_restrictedTriangle
    {E : Set Plane} (K : StarShapedKakeya E) {a rho r0 : ℝ}
    (ha : 0 < a) (harho : a < G.multiplier * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho G.multiplier) … :
    ENNReal.ofReal (annularCExt a r0 rho G.multiplier) *
        (∑' n, ENNReal.ofReal (H (G.selected n))) ≤
      ∑' n, volume (G.restrictedTriangle K r0 n)

-- :188  ***PROOF.md (8.3a)*** the unconditional cone-only inequality
theorem quarter_cost_le_outerMeasure_infinite … :
    ENNReal.ofReal (annularCExt a r0 rho G.multiplier / 4) *
        (∑' n, ENNReal.ofReal (4 * H (G.selected n))) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

-- :213  ***the B = ⊤ branch***
theorem outerMeasure_diff_eq_top_of_cost_eq_top …
    (hB : (∑' n, ENNReal.ofReal (4 * H (G.selected n))) = ⊤) :
    volume.toOuterMeasure (E \ Metric.closedBall K.center r0) = ⊤
```

**The `⊤` branch really is residual-free.**  Verified, not asserted: the twelve
declarations of the chain were dumped with `#print` (which does expose proof
terms) and the union of the `StarKakeyaLower.*` constants occurring in those
proof terms is exactly

```
Direction, Plane, FixedDeletionGreedyData, StarShapedKakeya, annularCExt,
UnitNeedle.{OutsideBall, height, triangleInterior, triangleInterior_measurable,
            triangleInterior_subset_triangleHull, annular_payment_triangleInterior},
StarShapedKakeya.{needleFamily_hasDirection, triangleHull_subset},
FixedDeletionGreedyData.{remaining_subset_initial,
                         pairwise_disjoint_selected_triangleInterior,
                         restrictedTriangle, measurableSet_restrictedTriangle,
                         restrictedSelectedUnion_eq,
                         measurableSet_restrictedSelectedUnion,
                         restrictedSelectedUnion_subset,
                         pairwise_disjoint_restrictedTriangle,
                         volume_restrictedSelectedUnion,
                         tsum_volume_restrictedTriangle_le_outerMeasure,
                         cost_le_tsum_volume_restrictedTriangle,
                         quarter_cost_eq_cost,
                         quarter_cost_le_outerMeasure_infinite,
                         outerMeasure_diff_eq_top_of_cost_eq_top}
```

with **no** occurrence of `residualFan`, `residualAngles`, `greedyResidual`,
`residual_height_*`, or `euclideanPolarAnnulus_outerMeasure_ge`.  So (B4) and
§8.4 are genuinely not invoked in this branch, exactly as `PROOF.md` §8.6
requires.

## 15. The summable branch (`PROOF.md` (B4) + (8.3b))

```lean
-- :249  δ_n → 0 from H_n → 0, via the EXACT relation δ = m ρ sin (H(δ))
theorem selected_height_tendsto_zero_of_summable {rho : ℝ} (hrho : 0 < rho)
    (hheight0 : ∀ theta, 0 ≤ height theta)
    (hselected_le : ∀ n, height (G.selected n) ≤ G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hcost : Summable fun n => H (G.selected n)) :
    Tendsto (fun n => height (G.selected n)) atTop (nhds 0)

-- :275  PROOF.md (B4) for the annular route
theorem residual_height_zero_of_summable_paperWeight {rho : ℝ} (hrho : 0 < rho)
    (hheight0 : ∀ theta, 0 ≤ height theta)
    (hselected_le : ∀ n, height (G.selected n) ≤ G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hcost : Summable fun n => H (G.selected n)) :
    ∀ theta ∈ greedyResidual G.remaining, height theta = 0

-- :292
theorem disjoint_restrictedResidualFan_restrictedSelectedUnion … (r0 : ℝ) :
    Disjoint
      (residualFan K (greedyResidual G.remaining) \
        Metric.closedBall K.center r0)
      (G.restrictedSelectedUnion K r0)

-- :315  PROOF.md (8.3b), countable version
theorem geometric_exterior_outerMeasure_lower_infinite
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0) … :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
          directionAngleOuter (greedyResidual G.remaining) +
        ∑' n, volume (G.restrictedTriangle K r0 n) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

-- :368  ***the B ≠ ⊤ branch***, same min coefficient as finite M3b
theorem annular_exterior_lower_bound_of_summable
    {E : Set Plane} (K : StarShapedKakeya E) {a rho r0 : ℝ}
    (ha : 0 < a) (harho : a < G.multiplier * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho G.multiplier)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hheight0 : ∀ theta, 0 ≤ height theta)
    (hbound : ∀ theta ∈ G.initial, height theta ≤ a)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hB : (∑' n, ENNReal.ofReal (4 * H (G.selected n))) ≠ ⊤) :
    ENNReal.ofReal
        (min (annularCExt a r0 rho G.multiplier / 4) ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter G.initial ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)
```

**Why the existing (B4) lemma could not be reused — the one real obstruction of
this pass.**  `FixedDeletionGreedyData.residual_height_zero_of_summable_cost`
(`CaseIISelection.lean:636`) requires
`hheight_le_H : ∀ n, height (G.selected n) ≤ H (G.selected n)`.  In
`caseII_fixed_greedy_lower_bound` that hypothesis is discharged
(`CaseIISelection.lean:1255–1277`) from `δ = m ρ sin H ≤ m ρ H ≤ H`, whose last
step needs `m ρ ≤ 1` and hence the hypothesis `hrhoOne : rho ≤ 1`.  The annular
route does **not** have `rho ≤ 1` (`PROOF.md` Remark 8.2), so that lemma is
unusable here and reusing it would have smuggled `rho ≤ 1` into the exit
theorem.

The replacement follows `PROOF.md` §8.3 literally and needs no comparison
between `δ_n` and `H_n` at all: `H_n → 0` (summability), then
`δ_n = m ρ sin H_n → m ρ · sin 0 = 0` by continuity, using the *existing exact*
identity `height_eq_multiplier_rho_sin_paperWeight` (`CaseIISelection.lean:987`).
The order core is the existing `residual_height_eq_zero_of_tendsto`
(`GreedyResidual.lean:39`), whose `greedy_bound` argument is `G.dominates`.
Machine check: `annular_exterior_lower_bound_of_summable` and both exit theorems
carry **no** dependency on `residual_height_zero_of_summable_cost`, `caseIIC`,
`caseIIKappa`, `caseIIPaperWeight`, `caseII_round2_initial_angle_lower_bound`
or `caseII_fixed_greedy_lower_bound` (grep of the printed proof terms).

## 16. The outcome wrapper — M4 exit theorems

```lean
-- :437  ***M4 EXIT THEOREM*** (PROOF.md Proposition 8.1, exterior branch)
theorem annular_exterior_greedy_lower_bound
    {E : Set Plane} (K : StarShapedKakeya E) (A : Set Direction)
    {eps a r0 rho : ℝ}
    (heps0 : 0 < eps) (heps1 : eps < 1) (ha : 0 < a)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (harhoScaled : a < (1 - eps) * rho)
    (hCext : 0 < annularCExt a r0 rho (1 - eps))
    (hout : ∀ theta ∈ A, (K.needleFamily theta).OutsideBall rho K.center)
    (hlow : ∀ theta ∈ A, (K.needleFamily theta).height K.center < a) :
    ENNReal.ofReal
        (min (annularCExt a r0 rho (1 - eps) / 4) ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter A ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0)

-- :504  non-vacuity: the coefficient is strictly positive
theorem annular_exterior_coefficient_pos {a r0 rho m : ℝ}
    (hr0 : 0 < r0) (hlt : r0 < rho) (hCext : 0 < annularCExt a r0 rho m) :
    0 < min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2)

-- :516  paper A_out specialisation
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

Facts that matter for the audit.

* **No selection is an input.**  The wrapper runs the actual
  `fixedSelectionOutcome height H m A hheight0 hbound` (`CaseIISelection.lean:194`)
  with `height θ = (K.needleFamily θ).height K.center`, `m = 1 - eps` and the
  **actual paper weight** `H θ = Real.arcsin (height θ / (m * rho))`, and
  exhausts both constructors.  `M3b`'s `FiniteFixedSelection` argument is gone
  from the public interface.
* **Three branches, no gaps.**  `finite F` → M3b
  `annular_exterior_lower_bound_of_finiteSelection` (the two defining equations
  are supplied by `rfl`, so the paper weight is used, not an abstract `H`);
  `infinite hpositive` → `infiniteGreedyData` (`CaseIISelection.lean:277`) and
  then `by_cases` on `(∑' n, ENNReal.ofReal (4 * H (G.selected n))) = ⊤`,
  handled by §14 and §15 respectively.
* **No hypothesis states the conclusion or the residual behaviour.**  The only
  hypotheses are `0 < eps`, `eps < 1`, `0 < a`, `0 < r0`, `r0 < rho`,
  `a < (1-eps) * rho`, `0 < annularCExt …`, and the two pointwise geometric
  facts `hout`/`hlow` about `A`.  Residual-zero and summability are **derived**
  inside the proof from the outcome and `G.dominates`.
* **`A` is arbitrary.**  No measurability, countability or separability of `A`
  is assumed anywhere; `directionAngleOuter` is the metric outer measure `μH[1]`.
* **No `rho ≤ 1`, no `1/2 < rho`, no `κ`.**  Confirmed by inspection of the
  signature and by the dependency grep of §15.
* **The bound is not vacuous.**  `annular_exterior_coefficient_pos` shows the
  coefficient is strictly positive under exactly the exit theorem's hypotheses.
* **`A_out` costs nothing extra.**  `A_out_radius` is defined in the CLEAN
  `Trichotomy` (already in the closure); the outside-ball premise is discharged
  by `outsideBall_sub_one_of_not_triangleHull_subset_closedBall`
  (`CaseIIGeometry.lean:98`) with `0 ≤ R₁` obtained from `0 < r0 < R₁ - 1` by
  `linarith`.  No numeric constant and no frozen module is involved.

## 17. Build output, receipts and scans (fourth pass)

```
$ ulimit -n 65535; lake build StarKakeyaLower.AnnularGreedyInfinite
✔ [8326/8326] Built StarKakeyaLower.AnnularGreedyInfinite (5.2s)
Build completed successfully (8326 jobs).

$ ulimit -n 65535; lake build StarKakeyaLower
Build completed successfully (8350 jobs).

$ ulimit -n 65535; lake build StarKakeyaLowerAudit
info: StarKakeyaLower/Audit.lean:385:0:
  'StarKakeyaLower.universal_strong_lower_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8348 jobs).
```

`AnnularGreedyInfinite.lean` emits **zero** diagnostics of its own.

`#print axioms` receipts, taken from a throw-away module deleted immediately
afterwards.  All eighteen new public declarations report exactly

```
[propext, Classical.choice, Quot.sound]
```

namely `FixedDeletionGreedyData.{measurableSet_restrictedTriangle,
restrictedSelectedUnion_eq, measurableSet_restrictedSelectedUnion,
restrictedSelectedUnion_subset, pairwise_disjoint_restrictedTriangle,
volume_restrictedSelectedUnion, tsum_volume_restrictedTriangle_le_outerMeasure,
cost_le_tsum_volume_restrictedTriangle, quarter_cost_eq_cost,
quarter_cost_le_outerMeasure_infinite, outerMeasure_diff_eq_top_of_cost_eq_top,
selected_height_tendsto_zero_of_summable,
residual_height_zero_of_summable_paperWeight,
disjoint_restrictedResidualFan_restrictedSelectedUnion,
geometric_exterior_outerMeasure_lower_infinite,
annular_exterior_lower_bound_of_summable}`,
`annular_exterior_greedy_lower_bound` and
`annular_exterior_A_out_greedy_lower_bound`.

**Receipt methodology, and a negative result worth recording.**  A hand-rolled
constant-dependency walker built on `Environment.find?` / `getConstInfo` was
tried first and is **not** a valid audit tool under this toolchain: in Lean
`v4.30.0-rc2`, `ConstantInfo.value?` returns `none` for *theorems*, so such a
walker silently traverses types only and reports an empty dependency set for
every proof.  It was discarded.  `#print axioms` was then explicitly validated
against a planted `sorry`, both in-module and across a module boundary:

```
$ # temporary StarKakeyaLower/SorryProbeTmp.lean with `theorem … := by sorry`
$ lake env lean <probe importing it>
'StarKakeyaLower.sorry_probe_tmp' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

so `sorryAx` **is** detected through imports and the receipts above are
meaningful.  The probe module and the probe file were deleted.  The structural
claims of §14 and §15 were obtained instead from `#print`ed **proof terms**,
which do expose the bodies.

Scans:

```
$ grep -nE "\bsorry\b|\badmit\b|^axiom |native_decide|unsafe |partial def" \
    StarKakeyaLower/AnnularGreedyInfinite.lean
(no matches)

$ grep -rnE "\bsorry\b|\badmit\b|^axiom |native_decide" StarKakeyaLower/ StarKakeyaLower.lean
(no matches)

$ grep -nE "caseIIKappa|caseIIC|rhoOne|rhoHalf" StarKakeyaLower/AnnularGreedyInfinite.lean
28, 237, 434   (all inside documentation comments; no code occurrence)

$ git --no-pager diff --check
(no output)

$ git status --short   # M4 build snapshot before updating this STATUS/PLAN text
 M …/04-lean/StarKakeyaLower.lean
?? …/04-lean/StarKakeyaLower/AnnularGreedyInfinite.lean

$ git --no-pager diff --stat
 …/04-lean/StarKakeyaLower.lean | 8 +++++---
 1 file changed, 5 insertions(+), 3 deletions(-)
```

At that build snapshot the only tracked Lean file modified was the production
root, and only its `import` list and docstring. Updating this report and the plan
also modifies the two tracked Markdown files. No existing theorem statement was
touched; M3's `AnnularGreedy.lean` is byte-identical to the committed version.

Frozen-dependency check, against the FROZEN list of `LEAN-PLAN.md` §1:

| Module | transitive `StarKakeyaLower` imports | FROZEN in closure |
|---|---|---|
| `AnnularGreedyInfinite` | `AnnularGeometry`, `AnnularGreedy`, `CaseIIGeometry`, `CaseIISelection`, `CircleDilation`, `GreedyResidual`, `LiGeometry`, `ParametricCaseII`, `PolarOuterMeasure`, `QuotientCircle`, `StarKakeyaSet`, `TriangleArea`, `Trichotomy` | **none** |

Every module in the closure has zero occurrences of the frozen witness
constants, so `AnnularGreedyInfinite` is CLEAN in both senses of §1.

## 18. Interface corrections discovered while executing M4

Mirrored into `LEAN-PLAN.md`.  **No exit criterion was weakened.**

1. **`residual_height_zero_of_summable_cost` is unusable for the annular
   route.**  See §15.  Its `height ≤ H` hypothesis is only available under
   `m ρ ≤ 1`.  `LEAN-PLAN.md` §M4 listed it as one of the three ingredients of
   (B4); the correct ingredient is `height_eq_multiplier_rho_sin_paperWeight`
   (`CaseIISelection.lean:987`) plus `residual_height_eq_zero_of_tendsto`
   (`GreedyResidual.lean:39`), which is what was used.
2. **M1's `tsum_outerMeasure_inter_le` is not needed for (8.3a).**
   `LEAN-PLAN.md` §M4 said the cone-only inequality "needs
   `tsum_outerMeasure_inter_le` from M1".  It does not: `PROOF.md` §8.5 routes
   through the shadow cones `S(θ_j,δ_j)` only because `P_j` is merely contained
   in `A^ext ∩ S_j` with `A^ext` nonmeasurable.  In Lean each
   `restrictedTriangle` is *itself* measurable (open minus closed) and *itself*
   contained in `E \ closedBall`, so plain `measure_iUnion` over `ℕ` plus
   `measure_mono` gives the ledger directly.  The shadow cones are therefore
   never constructed.  This is strictly simpler and assumes strictly less; M1's
   countable ledger remains proved but is, as of M4, still unused downstream.
3. **`fixedSelectionOutcome`'s `infinite` constructor supplies only
   `hpositive`.**  Building `FixedDeletionGreedyData` from it additionally needs
   the deletion-cost field, discharged by
   `directionAngleOuter_fixedDeletionBall_le` (`CaseIISelection.lean:26`)
   applied to `Real.arcsin_nonneg`.  The plan's sketch did not mention this
   obligation.
4. **`G.multiplier` is not syntactically `m`.**  It is definitionally `1 - eps`
   through `infiniteGreedyData`, so every `G`-level lemma has to be
   re-expressed with `hmult : G.multiplier = m := rfl` before it matches the
   goal.  This is the same friction `caseII_fixed_greedy_lower_bound` handles
   with `change`; it is bookkeeping, not mathematics.
5. **M4 lives in a sibling module**, not inside `AnnularGreedy.lean`.  See §13.

## 19. Honest statement of what remains after M4 (historical)

Superseded by §20 and §21: M5 has since been executed.  The table as written at
the end of the fourth pass was:

| Milestone | What is missing | Size |
|---|---|---|
| **M5** | Restricted coordinate transport `outerMeasure_centeredCoordinate_image_inter_closedBall` (the existing transport `UniversalAssembly.lean:48` is unrestricted), and variable interior mass — the current plumbing hardwires `strongCaseIQ` (`CaseIEndpointMassIntegral.lean:22`). Both on the confined side, and the confined side's parametric core still sits inside the FROZEN `CaseIAssemblyConditional`, so an extraction is needed first. | substantial |
| **M6** | Hypothesis B/C kernel and endpoint containment for the new parameter tuple, including discharging `0 < annularCExt a r0 rho (1 - eps)` as a *numeric* fact (currently an explicit hypothesis everywhere). | substantial |
| **M7** | Final assembly `universal_annular_lower_bound`, gluing the confined and exterior halves through M1's `outerMeasure_ge_add_of_inter_of_diff`. | small once M5–M6 exist |

---

## 20. M5 — extraction, restricted transport, variable interior mass

### 20.1 What was moved, exactly

Every declaration below was **moved**, not copied: it no longer exists at its
old location, it kept its namespace, name, statement and proof verbatim, and it
is still visible to every old client through the import chain.

| Declaration range | From (at `407b346`) | To |
|---|---|---|
| 33 declarations, `LiFamilyContainment` … `outerMeasure_ge_caseI_lintegral` | `CaseIAssemblyConditional.lean` **lines 25–449** (425 source lines; docstring of `LiFamilyContainment` at `:25`, last body line of `outerMeasure_ge_caseI_lintegral` at `:449`; the trailing blank line 450 went with it) | `CaseIRadialCore.lean:31–449` (`LiFamilyContainment` at `:31`, `outerMeasure_inner_ge_caseI_lintegral_of_raw` at `:408`, `outerMeasure_ge_caseI_lintegral` at `:433`) |
| `FirstArcAggregateMass` | `CaseIEndpointMassIntegral.lean:25–29` | `CaseIRadialCore.lean:466` |
| `planeCoordinateEquiv_measurePreserving` | `UniversalAssembly.lean:41–45` | `UniversalNeedleAdapter.lean:396` |
| `outerMeasure_centeredCoordinate_image` | `UniversalAssembly.lean:47–75` | `UniversalNeedleAdapter.lean:433` (now a one-line corollary of the generalisation at `:403`, which carries the moved proof body) |

The 33 moved declarations are, in order: `LiFamilyContainment`,
`directionOuterMass`, `JGammaCriticalContainment`,
`JGammaOpenCriticalContainment`, `jGammaCriticalContainment_of_zeroRadius`,
`jGammaCriticalContainment_zero_or_positive`,
`DirectionNeedleFamily.firstArcTarget`,
`DirectionNeedleFamily.mem_JGamma_firstArcTarget`,
`DirectionNeedleFamily.subset_iUnion_JGamma_firstArcTarget`,
`FirstArcPointwiseHybridCriticalContainment`,
`firstArcPointwiseHybridCriticalContainment_of_branches`,
`DirectionNeedleFamily.quotientHybrid_firstArc_subset_projected_carrier`,
`DirectionNeedleFamily.aggregateBaseUnion`,
`DirectionNeedleFamily.aggregate_dilated_cover`,
`DirectionNeedleFamily.aggregateBaseUnion_volume_le_angleOuter`,
`DirectionNeedleFamily.liFamilyContainment_of_critical`,
`angleOuter_ge_of_liFamilyContainment`,
`angleOuter_ge_of_firstArcPointwiseAggregate`, `directionNeedleFamilyOfRaw`,
`directionNeedleFamilyOfRaw_needle`, `directionNeedleFamilyOfRaw_arcData`,
`directionTriangleUnion`, `originOpenDisk`, `originClosedDisk`, `originSphere`,
`originClosedDisk_diff_originOpenDisk_subset_sphere`, `volume_originSphere`,
`outerMeasure_originSphere`, `outerMeasure_inter_originOpenDisk_eq_closedDisk`,
`triangle_subset_directionTriangleUnion_univ`,
`angleOuter_directionTriangleUnion_le_inner`,
`outerMeasure_inner_ge_caseI_lintegral_of_raw`,
`outerMeasure_ge_caseI_lintegral`.

Module boundaries after the move:

```
CaseIRadialCore          imports PolarProjectiveOuter, LiNeedleAdapter          -- CLEAN
CaseIAssemblyConditional imports CaseIRadialCore, StrongerKernel                -- FROZEN, unchanged body count 19
UniversalNeedleAdapter   imports CaseIRadialCore, LiNeedleAdapter, Mathlib…     -- CLEAN
AnnularCaseI             imports UniversalNeedleAdapter                          -- CLEAN
UniversalAssembly        unchanged import list                                   -- FROZEN
```

No cycle was created and no frozen import was reintroduced: `UniversalFirstArc`
and `SupportReflection` still reach the Li-specific part of
`CaseIAssemblyConditional` through `CaseIEndpointAnalytic`, so every old name
still resolves for every old client.

### 20.2 New signatures (`UniversalNeedleAdapter`, clean transport layer)

```lean
theorem outerMeasure_centeredCoordinate_image_of_set {E : Set Plane}
    (K : StarShapedKakeya E) (S : Set Plane) :
    volume.toOuterMeasure (centeredCoordinate K '' S) = volume.toOuterMeasure S

theorem centeredCoordinate_injective {E : Set Plane} (K : StarShapedKakeya E) :
    Function.Injective (centeredCoordinate K)

theorem dist_le_iff_sq_add_sq_le {E : Set Plane} (K : StarShapedKakeya E)
    {r0 : ℝ} (hr0 : 0 ≤ r0) (x : Plane) :
    dist x K.center ≤ r0 ↔
      (x 0 - K.center 0) ^ 2 + (x 1 - K.center 1) ^ 2 ≤ r0 ^ 2

theorem centeredCoordinate_image_closedBall {E : Set Plane}
    (K : StarShapedKakeya E) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    centeredCoordinate K '' Metric.closedBall K.center r0 = originClosedDisk r0

theorem outerMeasure_centeredCoordinate_image_inter_closedBall {E : Set Plane}
    (K : StarShapedKakeya E) {r0 : ℝ} (hr0 : 0 ≤ r0) :
    volume.toOuterMeasure ((centeredCoordinate K '' E) ∩ originClosedDisk r0) =
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center r0)

theorem universalDirectionTriangleUnion_inter_originClosedDisk_subset
    {E : Set Plane} (K : StarShapedKakeya E) {r0 : ℝ} :
    directionTriangleUnion (universalDirectionNeedle K) Set.univ ∩ originClosedDisk r0 ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r0
```

`hr0 : 0 ≤ r0` is load bearing in the three displayed theorems that carry it
(`dist_le_iff_sq_add_sq_le`, the ball image, and restricted transport) and is
**not** totalised: at
`r0 < 0` the metric ball is empty while `originClosedDisk r0` is the disk of
radius `|r0|`, so those statements are false there. The final restricted
containment theorem needs no radius hypothesis — it is
`Set.inter_subset_inter_left` applied to the existing
`universalDirectionTriangleUnion_subset`.

### 20.3 New signatures (`CaseIRadialCore`, variable interior mass)

```lean
def annularCaseIQ (L_in : ℝ≥0∞) (g : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  L_in / ENNReal.ofReal (g r)

theorem annular_aggregateMass_of_directionOuterMass
    {r : ℝ} {A : Set ProjectiveDirection} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : 1 ≤ g r) (hmass : L_in ≤ directionOuterMass A) :
    FirstArcAggregateMass A (g r) (annularCaseIQ L_in g r)

theorem ofReal_mul_annularCaseIQ {r : ℝ} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : 1 ≤ g r) :
    ENNReal.ofReal r * annularCaseIQ L_in g r = L_in * ENNReal.ofReal (r / g r)

theorem lintegral_annularCaseIQ_eq_mul {a r₀ : ℝ} {g : ℝ → ℝ} {L_in : ℝ≥0∞}
    (hg : ∀ r ∈ Icc a r₀, 1 ≤ g r)
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / g r))
      (volume.restrict (Icc a r₀))) :
    (∫⁻ r in Icc a r₀, ENNReal.ofReal r * annularCaseIQ L_in g r) =
      L_in * ∫⁻ r in Icc a r₀, ENNReal.ofReal (r / g r)
```

Everything stays in `ℝ≥0∞`.  `L_in = ⊤` is sound: the cancellation
`ofReal (g r) * (L_in / ofReal (g r)) = L_in` uses only `ofReal (g r) ∉ {0, ⊤}`,
and the factorisation uses `lintegral_const_mul''` (the `AEMeasurable` form),
not the `≠ ⊤` form.  `hmeas` is exactly what licenses that step; positivity does
not imply it.

**Interface correction.** The `LEAN-PLAN.md` M5 sketch gave
`lintegral_annularCaseIQ_eq_mul` a hypothesis `ha : 0 ≤ a`.  It is *not* needed
and was therefore not kept: `ENNReal.ofReal` truncates at negative reals, so the
pointwise identity reads `0 = 0` for `r < 0`.  `0 ≤ a` is still load bearing one
level up, where the raw radial theorem consumes it, and it is a hypothesis
there.  This is a hypothesis *removal*, not a weakening of the M5 exit.

### 20.4 The M5 exit theorem (`AnnularCaseI`)

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

with the coordinate-side intermediate

```lean
theorem lintegral_lower_bound_inner_of_raw_variable_mass … :
    I_lower * L_in ≤
      volume.toOuterMeasure
        (directionTriangleUnion N Set.univ ∩ originClosedDisk r₀)
```

(§20.6 replaces the proof of this theorem by a one-term corollary of a generic
theorem, keeping the signature above verbatim, and adds the sibling
`universal_positive_confined_lower_bound_of_trace_containment` for the
positively oriented family that the endpoint chain actually produces.)

This is exactly the stated M5 exit criterion, and no more.  The needle family is
the canonical `universalDirectionNeedle K` built from the raw `StarShapedKakeya`
data; the direction class `A` is radius-indexed, as the raw radial theorem
requires; `L_in` and `I_lower` are variables.  `htrace`, `hcritical`, `hmass`
and `hI` are **hypotheses**: M5 certifies none of them, and discharging the
first two for a concrete parameter tuple is precisely M6.

### 20.5 Builds, receipts and scans (fifth pass)

Shallow builds after each move, in the order performed, all
`Build completed successfully`:

```
lake build StarKakeyaLower.CaseIRadialCore            (8326 jobs)
lake build StarKakeyaLower.CaseIAssemblyConditional
lake build StarKakeyaLower.UniversalNeedleAdapter     (8327 jobs)
lake build StarKakeyaLower.AnnularCaseI               (8328 jobs)
lake build StarKakeyaLower StarKakeyaLowerAudit       (8356 jobs)
```

Cold-ish rebuild: `.lake/build/{lib/lean,ir}/StarKakeyaLower*` deleted, then
`lake build StarKakeyaLower StarKakeyaLowerAudit` → `Build completed
successfully (8356 jobs)` in `3m50s` real.  No stale olean can be responsible
for any of the above.

`#print axioms` (temporary audit file, compiled with `lake env lean`, then
deleted — the audit target was left unchanged, as it was for M1–M4):

| Theorem | Axioms |
|---|---|
| `outerMeasure_inner_ge_caseI_lintegral_of_raw` | `propext, Classical.choice, Quot.sound` |
| `outerMeasure_ge_caseI_lintegral` | idem |
| `FirstArcAggregateMass`, `annularCaseIQ` | idem |
| `annular_aggregateMass_of_directionOuterMass` | idem |
| `ofReal_mul_annularCaseIQ`, `lintegral_annularCaseIQ_eq_mul` | idem |
| `planeCoordinateEquiv_measurePreserving` | idem |
| `outerMeasure_centeredCoordinate_image_of_set` | idem |
| `outerMeasure_centeredCoordinate_image` | idem |
| `centeredCoordinate_injective`, `dist_le_iff_sq_add_sq_le` | idem |
| `centeredCoordinate_image_closedBall` | idem |
| `outerMeasure_centeredCoordinate_image_inter_closedBall` | idem |
| `universalDirectionTriangleUnion_inter_originClosedDisk_subset` | idem |
| `annular_aggregateMass_on_Icc` | idem |
| `lintegral_lower_bound_inner_of_raw_variable_mass` | idem |
| `universal_confined_lower_bound_of_trace_containment` | idem |
| **`universal_strong_lower_bound`** | idem — **unchanged** |

Scans:

* forbidden tokens `sorry` / `admit` / `native_decide` / `^axiom ` across
  `StarKakeyaLower/` and `StarKakeyaLower.lean`: **none**;
* duplicate unqualified declaration names: byte-identical to the scan at
  `407b346` (24 pre-existing collisions, all in unrelated namespaces, none new);
* frozen import-closure scan (`strongA`, `strongR₀`, `strongRLambda`,
  `strongR₁`, `strongRho`, `strongP`, `strongTarget`, `altA`, `altTarget`):

  | Root | modules in closure | frozen-carrying modules |
  |---|---:|---|
  | `CaseIRadialCore` | 14 | none |
  | `UniversalNeedleAdapter` | 15 | none |
  | `AnnularCaseI` | 16 | none |
  | `UniversalAssembly` | 33 | 15 (unchanged; `CaseIAssemblyConditional` still 19 occurrences, i.e. the moved front section carried zero) |

* `git diff --check`: clean.  Nothing was committed or pushed.

Warnings: `AnnularCaseI` and the new material in `UniversalNeedleAdapter` are
warning-free.  `CaseIRadialCore` emits 5 warnings (two deprecated-lemma pairs
and one unused binder) — all of them inherited verbatim with the moved proofs,
which emitted the same 5 warnings from `CaseIAssemblyConditional` before the
move.  Old proofs were not rewritten.

### 20.6 Second pass — the downstream contract

The first pass proved the confined bound only for the **signed** family
`universalDirectionNeedle K`.  The existing endpoint chain
(`universalArcData`, `universal_hybrid_containment`) produces data for the
**positively oriented** family `universalPositiveNeedle K` instead, so the M5
interface as first written could not have been fed by M6.  That is fixed here,
generically and without duplicating any theorem.

#### 20.6.1 Further moved blocks

Again all **moves**: byte-identical text, same namespace/name/statement/proof,
originals deleted.  Verified mechanically against `407b346` — all 15 blocks
reported `IDENTICAL`.

| Declarations | From (at `407b346`) | To |
|---|---|---|
| `supportPoint_add_pi_neg`, `supportNeedleTriangle_add_pi_neg`, `projectiveDirection_add_pi` | `SupportReflection.lean:32–55, 82–85` | `UniversalNeedleAdapter.lean:523, 530, 547` |
| `DirectionNeedle.orientPositive`, `…_height_nonneg`, `…_abs_height`, `…_triangle`, `…_height_eq_abs` | `UniversalFirstArc.lean:148–192`, the whole "Orientation normalization" section | `UniversalNeedleAdapter.lean:556, 566, 575, 583, 591` |
| `universalPositiveNeedle`, `…_triangle`, `…_height_nonneg`, `…_abs_height`, `…_height_lt_of_no_high`, `…_height_le_of_no_high`, `universalPositiveTriangleUnion_subset` | `UniversalEndpointClosure.lean:59–111`, the whole "positively oriented universal support family" section | `UniversalNeedleAdapter.lean:604–643` |

`universalPositiveNeedle_triangle_subset_disk` and everything below it in
`UniversalEndpointClosure` mention `strongR₁` and were **left frozen**, as
required.

The three reflection identities had to travel because `orientPositive` is
defined by them; leaving them in `SupportReflection` (BODY-ONLY over a tainted
chain) would have forced the clean adapter to import a frozen closure.
`SupportReflection` now imports `UniversalNeedleAdapter` and re-exports them, so
its own clients are unaffected.  No cycle: the adapter imports only
`CaseIRadialCore`, `LiNeedleAdapter` and Mathlib, and nothing in that closure
imports `SupportReflection`.

Module boundaries after the second pass:

```
CaseIRadialCore          ← PolarProjectiveOuter, LiNeedleAdapter            CLEAN (14)
UniversalNeedleAdapter   ← CaseIRadialCore, LiNeedleAdapter, Mathlib        CLEAN (15)
AnnularCaseI             ← UniversalNeedleAdapter                           CLEAN (16)
SupportReflection        ← CaseIEndpointAnalytic, UniversalNeedleAdapter    BODY-ONLY
UniversalFirstArc        ← Figure5LocalContact, SupportReflection, adapter  BODY-ONLY
UniversalEndpointClosure ← UniversalFirstArc                                FROZEN
```

#### 20.6.2 New declarations

```lean
-- UniversalNeedleAdapter.lean:656  (no radius hypothesis needed)
theorem universalPositiveTriangleUnion_inter_originClosedDisk_subset
    (K : StarShapedKakeya E) {r0 : ℝ} :
    directionTriangleUnion (universalPositiveNeedle K) Set.univ ∩ originClosedDisk r0 ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r0

-- CaseIRadialCore.lean:541, :547 — the normalization bridge
theorem directionOuterMass_eq_directionOuterMeasure (A : Set ProjectiveDirection) :
    directionOuterMass A = StarShapedKakeya.directionOuterMeasure A := rfl

theorem directionOuterMass_eq_directionAngleOuter (A : Set ProjectiveDirection) :
    directionOuterMass A = directionAngleOuter A
```

The bridge **reuses** `directionOuterMeasure_eq_directionAngleOuter`
(`CaseIIGeometry.lean:722`); the Haar computation is not repeated.  It matters
because M4's exterior bound is stated in `directionAngleOuter` while the
confined branch is stated in `directionOuterMass`, and M7 must add the two.

#### 20.6.3 The refactored wrapper — one proof, two corollaries

`AnnularCaseI.lean` now factors through a single generic physical theorem:

```lean
theorem confined_lower_bound_of_raw_of_restricted_containment
    (K : StarShapedKakeya E) (ha : 0 ≤ a) (hr₀ : 0 ≤ r₀)
    (N : (d : ProjectiveDirection) → DirectionNeedle d)
    (htrace …) (hg …) (hmass …) (hcritical …) (hmeas …) (hI …)
    (hconfined : directionTriangleUnion N Set.univ ∩ originClosedDisk r₀ ⊆
      (centeredCoordinate K '' E) ∩ originClosedDisk r₀) :
    I_lower * L_in ≤ volume.toOuterMeasure (E ∩ Metric.closedBall K.center r₀)
```

with exactly two corollaries, each one term long:

* `universal_confined_lower_bound_of_trace_containment` — signed family,
  **public signature unchanged** from the first pass;
* `universal_positive_confined_lower_bound_of_trace_containment` — positive
  family, otherwise identical hypotheses and identical conclusion.

Plus the instantiation helper

```lean
theorem directionAngleOuter_le_directionOuterMass_const
    (K : StarShapedKakeya E) (R₁ : ℝ) :
    ∀ r ∈ Icc a r₀,
      directionAngleOuter (K.A_in_radius R₁) ≤
        directionOuterMass ((fun _ : ℝ => K.A_in_radius R₁) r)
```

which records the intended M6/M7 choice — constant class `A r = K.A_in_radius R₁`
and `L_in = directionAngleOuter (K.A_in_radius R₁)` — and discharges `hmass`
outright.  **No tuple constant is defined**; `R₁` is a variable.

#### 20.6.4 Contract check (temporary, removed)

To verify the contract is genuinely closed, a temporary file instantiated the
positive wrapper with the *existing* frozen endpoint data — `universalArcData`,
`universal_hybrid_containment`, `one_le_strongPaperG`, the constant class
`K.A_in_radius strongR₁` and `L_in = directionAngleOuter (K.A_in_radius strongR₁)`
— leaving only `hmeas` and `hI` as parameters.  It elaborated with **no errors**
on the first attempt, which is the evidence that M6 has to supply nothing beyond
those two analytic facts plus the new tuple's `htrace`/`hcritical`.  The file was
deleted; it introduced no numeric constant, tuple or certificate, and nothing in
the tree depends on it.

#### 20.6.5 Generic (M5-proved) versus concrete (M6-owed)

| Obligation | Generic form, **proved in M5** | Concrete form, **owed by M6** |
|---|---|---|
| aggregate mass | `annular_aggregateMass_of_directionOuterMass`, `annular_aggregateMass_on_Icc`: `1 ≤ g r` and `L_in ≤ directionOuterMass (A r)` give the `FirstArcAggregateMass` shape at variable `L_in` | a concrete class and mass — constant `A r = K.A_in_radius R₁`, `L_in = directionAngleOuter (…)` — *and* the trichotomy branch hypothesis that gives that mass a value |
| mass normalization | `directionOuterMass_eq_directionAngleOuter`, `directionAngleOuter_le_directionOuterMass_const` | nothing further; this one is closed |
| measurability | `lintegral_annularCaseIQ_eq_mul` consumes `hmeas` as a hypothesis and factors `L_in` out exactly | `hmeas` itself for the concrete `g`, i.e. `AEMeasurable (fun r => ofReal (r / g r)) (volume.restrict (Icc a r₀))` |
| enlargement factor | `hg : ∀ r ∈ Icc a r₀, 1 ≤ g r` is a hypothesis everywhere | a concrete `g` and its `hg`, the analogue of `one_le_strongPaperG` |
| radial integral | `hI : I_lower ≤ ∫⁻ …` is a hypothesis; the multiplication order `I_lower * L_in` is fixed | the two-piece certificate, ending in `∫⁻` form, not `∫` |
| endpoint geometry | the family, the restricted containment and the transport are proved for both `universalDirectionNeedle` and `universalPositiveNeedle` | `htrace` and `hcritical` at the new tuple — the deep parameterisation, still untouched |

#### 20.6.6 Second-pass builds, receipts and scans

Shallow builds in dependency order, all `Build completed successfully`:

```
lake build StarKakeyaLower.UniversalNeedleAdapter    (8327 jobs)
lake build StarKakeyaLower.SupportReflection         (8331 jobs)
lake build StarKakeyaLower.UniversalFirstArc         (8335 jobs)
lake build StarKakeyaLower.UniversalEndpointClosure  (8336 jobs)
lake build StarKakeyaLower.CaseIRadialCore           (8326 jobs)
lake build StarKakeyaLower.AnnularCaseI              (8328 jobs)
lake build StarKakeyaLower StarKakeyaLowerAudit      (8356 jobs)
```

`#print axioms` (temporary audit, since deleted) for all 15 moved declarations,
the three new clean theorems, the generic wrapper, both corollaries, the
instantiation helper, the still-frozen
`universalPositiveNeedle_triangle_subset_disk`, `universal_hybrid_containment`
and `universal_strong_lower_bound`: **every one** is
`[propext, Classical.choice, Quot.sound]`.  The final theorem's receipt is
unchanged.

A second cold-ish rebuild (project oleans and IR deleted) succeeded in `3m49s`,
so no stale olean is involved.

Scans: no `sorry`/`admit`/`axiom`/`native_decide`; duplicate-declaration scan
still byte-identical to `407b346`; frozen import-closure scan empty for
`CaseIRadialCore` (14 modules), `UniversalNeedleAdapter` (15) and `AnnularCaseI`
(16); `git diff --check` clean; all temporary files removed.  Nothing committed.

Warnings: `AnnularCaseI` is warning-free.  The two `'ring' tactic does nothing`
pairs now reported at `UniversalNeedleAdapter.lean:527` and `:544` belong to the
moved `supportPoint_add_pi_neg` / `supportNeedleTriangle_add_pi_neg` proofs; the
`407b346` copy of `SupportReflection.lean` was recompiled in isolation and emits
exactly the same two pairs at the same proofs, so they are inherited, not
introduced.  No moved proof was rewritten.

---

## 21. What remains (M6–M7) — **HISTORICAL, SUPERSEDED BY §22**

> **Superseded.** This section was written at the end of the fifth pass (M5).
> Everything it lists as missing has since been delivered: M6 by four later
> passes (see `M6-KERNEL-STATUS.md`, `M6-INTEGRAL-STATUS.md`,
> `M6-ENDPOINT-STATUS.md`, `M6-ANN-ENDPOINT-STATUS.md`) and M7 by the pass
> recorded in §22. In particular the closing sentence below — that
> `ENNReal.ofReal (Real.pi * (131 / 6250)) < volume.toOuterMeasure E` is not a
> Lean theorem and that `100π/5599` is the only unconditional lower bound in the
> tree — is **no longer true**. It is retained unedited as a record of the state
> of the tree at that time.

Nothing below exists in this worktree.

| Milestone | What is missing | Size |
|---|---|---|
| **M6** | Five concrete inputs to `universal_positive_confined_lower_bound_of_trace_containment`: `htrace` and `hcritical` at the new tuple for `universalPositiveNeedle` — the deep parameterisation of `Figure5EndpointEnvelope` → `Figure5LocalContact` → `UniversalEndpointClosure`; a concrete `g` with `hg` and `hmeas`; and a two-piece integral certificate ending in `∫⁻` form supplying `hI`. Separately, M6 owes the Hypothesis B/C numeric kernel/domain, including `0 < annularCExt a r0 rho (1 - eps)`. The constant-class choice and mass normalization are **not** owed: M5 closed them. | substantial, cost still unknown |
| **M7** | Final assembly `universal_annular_lower_bound`, gluing §20's confined bound and M4's exterior bound through M1's `outerMeasure_ge_add_of_inter_of_diff`. | small once M6 exists |

M5 is **conditional** exactly as its exit criterion says. The generic theorem
still exposes all six analytic/geometric inputs, while the intended constant
`A_in` helper closes the mass input. Because M6 is untouched,
**no claim is made** that
`ENNReal.ofReal (Real.pi * (131 / 6250)) < volume.toOuterMeasure E`
is a Lean theorem, nor that any confined bound with a concrete constant is.
`universal_strong_lower_bound` (`100π/5599`) remains the only unconditional
lower bound in the tree, unchanged, and with an unchanged axiom receipt.

---

# Sixth pass — M7 (`StarKakeyaLower/AnnularAssembly.lean`)

## 22. M7 — final assembly; the route is closed

**Result: M7 is closed, unconditionally.** The joint inner/outer lower bound of
`PROOF.md` Theorem 10.1 is now a Lean theorem. Nothing in §22 is conditional,
and no hypothesis was added anywhere to make it go through: the one interface
that did not exist (a bound on the direction mass of a set together with its
complement, valid without measurability) was proved as a two-line generic helper
inside the new module rather than assumed.

### 22.1 What was added

Exactly one new file, plus an import line in the production root and seventeen
receipts in the audit target.

| File | Lines | Status |
|---|---:|---|
| `StarKakeyaLower/AnnularAssembly.lean` | 251 | **new**, green, **zero warnings** |
| `StarKakeyaLower.lean` | +41 / −15 | production root: +1 import line, docstring rewritten |
| `StarKakeyaLower/Audit.lean` | +36 / −4 | `AnnularEndpoint` import → `AnnularAssembly`; 17 new receipts at `:554`–`:570`; header note updated |

No pre-existing declaration was added, removed, renamed, restated, weakened or
reproved. Inside the Lean root, `git diff` touches only `StarKakeyaLower.lean`
(+41 / −15) and `StarKakeyaLower/Audit.lean` (+31 / −4), and
`AnnularAssembly.lean` is the only untracked file. Outside it, only the spike
documents `LEAN-PLAN.md`, `LEAN-STATUS.md` and `README.md` are modified.

### 22.2 Imports — exactly four

```lean
import StarKakeyaLower.BallSplit             -- M1  : Carathéodory split
import StarKakeyaLower.AnnularGreedyInfinite  -- M4  : exterior greedy exit
import StarKakeyaLower.AnnularAnalytic        -- M6  : gates C1 / C3 / C4
import StarKakeyaLower.AnnularEndpoint        -- M6  : confined exit (+ gate C2
                                              --       transitively, via
                                              --       AnnularCaseIIntegral)
```

Each is consumed. `Trichotomy` (`high_branch_outerMeasure`,
`directionOuterMeasure_univ`, `A_in_radius`, `A_out_radius`) and `CaseIIGeometry`
(`directionAngleOuter`, `directionOuterMeasure_eq_directionAngleOuter`) arrive
transitively through `AnnularAnalytic`/`AnnularGreedyInfinite` and are not
imported again.

**Closure scan.** The transitive import closure of `AnnularAssembly` is **32**
modules:

```
AnnularAnalytic AnnularCaseI AnnularCaseIIntegral AnnularEndpoint
AnnularGeometry AnnularGreedy AnnularGreedyInfinite AnnularKernel BallSplit
CaseIIGeometry CaseIISelection CaseIRadialCore CircleDilation
EndpointConfinedExit Figure5EndpointDomain Figure5EndpointEnvelopeCore
Figure5LocalContactCore GreedyResidual LiGeometry LiNeedleAdapter
ParametricCaseII PolarOuterMeasure PolarProjectiveOuter QuotientCircle
StarKakeyaSet SupportFirstArcSelector SupportReflection TriangleArea Trichotomy
UniversalEndpointClosureCore UniversalFirstArc UniversalNeedleAdapter
```

It does **not** contain `StrongerKernel`, `Figure5FrozenPackage`,
`UniversalAssembly`, `CaseIAssemblyConditional`, `StrongLiLemma25`,
`CaseIStrongIntegral`, `CaseIIAnalytic`, `UniversalEndpointClosure`,
`Figure5EndpointEnvelope` or `Figure5LocalContact`. A body scan (comments and
docstrings stripped) over all 32 modules plus `AnnularAssembly` itself finds
**zero** occurrences of `strongA`, `strongR₀`, `strongR₁`, `strongTarget`,
`strongPaperG`, `strongP`, `strongILower`, `strongPiUpper` or the literal
`5599`. The import graph over `StarKakeyaLower/` is acyclic (DFS colouring, no
back edge).

### 22.3 The statement

```lean
-- AnnularAssembly.lean:228
def UniversalAnnularLowerBound : Prop :=
  ∀ (E : Set Plane), StarShapedKakeya E →
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E

-- AnnularAssembly.lean:233
theorem universal_annular_lower_bound : UniversalAnnularLowerBound :=
  fun _ K => annular_lower_bound K
```

The parameterised theorem behind the wrapper, following the project convention
(`strong_lower_bound_of_caseI` → `universal_strong_lower_bound`):

```lean
-- AnnularAssembly.lean:194
theorem annular_lower_bound {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E
```

`annTarget = 131 / 6250` (`AnnularKernel.lean:33`), so the constant is
`131π/6250`. Normal form:

```lean
-- AnnularAssembly.lean:239
theorem pi_mul_annTarget_eq : Real.pi * annTarget = 131 * Real.pi / 6250
-- AnnularAssembly.lean:243
theorem universal_annular_lower_bound_normalForm (E : Set Plane)
    (K : StarShapedKakeya E) :
    ENNReal.ofReal (131 * Real.pi / 6250) < volume.toOuterMeasure E
```

`131/6250 = 0.020 96` versus `100/5599 = 0.017 860 …`, so the annular constant is
the larger of the two Lean-proved coefficients. Both theorems now live in the
default `lake build` closure.

### 22.4 Declaration inventory (all of `AnnularAssembly.lean`)

| Line | Declaration | Role |
|---:|---|---|
| 77 | `annCExt : ℝ` | the M4 exterior coefficient, literal `min (C_ext/4) ((ρ²−r₀²)/2)` |
| 82 | `annCExt_eq_literal` | `rfl` bridge to the shape M4 produces |
| 89 | `annJointCoefficient : ℝ` | `min annILower annCExt` |
| 91 / 94 | `annJointCoefficient_le_annILower` / `_le_annCExt` | the two lowering steps |
| 98 | `annTarget_lt_annCExt` | = `ann_m4_coefficient_gt_target` |
| 104 | `annTarget_lt_annJointCoefficient` | **the joint gate**, `lt_min` of C2 and C3/C4 |
| 107 | `annJointCoefficient_pos` | positivity, from `annTarget_pos` |
| 117 | `directionAngleOuter_le_pi` | generic: no direction set exceeds the full circle |
| 126 | `pi_le_directionAngleOuter_add_compl` | generic: `π ≤ μ*(A) + μ*(Aᶜ)` by coverage + subadditivity |
| 150 | `ann_target_lt_high_threshold` | gate C1 → `ofReal (π·T) < ofReal (annA/2)` |
| 165 | `annular_joint_ledger` | the M1 glue of the M6 and M4 ledgers |
| 194 | `annular_lower_bound` | the dichotomy |
| 228 / 233 | `UniversalAnnularLowerBound` / `universal_annular_lower_bound` | the final `Prop` and its proof |
| 239 / 243 | `pi_mul_annTarget_eq` / `universal_annular_lower_bound_normalForm` | constant in normal form |

Two of these — `directionAngleOuter_le_pi` and
`pi_le_directionAngleOuter_add_compl` — are the *only* genuinely new
mathematical content of M7. Both are generic in an arbitrary
`A : Set Direction`, and both are proved from
`StarShapedKakeya.directionOuterMeasure_univ` (`Trichotomy.lean:63`),
`measure_mono`, `measure_union_le` and
`directionOuterMeasure_eq_directionAngleOuter` (`CaseIIGeometry.lean:722`).

### 22.5 Proof architecture, as realised

`by_cases hhigh : ∃ theta, annA ≤ (K.needleFamily theta).height K.center`.

**High branch.** `ann_target_lt_high_threshold` is
`(ENNReal.ofReal_lt_ofReal_iff (0 < annA/2)).2` applied to
`π · annTarget < π · (annA / (2π)) = annA / 2`, i.e. gate C1
(`AnnularAnalytic.lean:119`) multiplied by `Real.pi_pos`. It is chained by
`.trans_le` into `K.high_branch_outerMeasure hhigh` (`Trichotomy.lean:188`). No
rational upper bound for `π` is used, so `strongPiUpper`/`StrongerKernel` is
never needed.

**Confined branch.** With `L_in := directionAngleOuter (K.A_in_radius annR₁)`
and `L_out := directionAngleOuter (K.A_out_radius annR₁)`:

1. *Interior.* `annular_confined_lower_bound K hhigh`
   (`AnnularEndpoint.lean:417`) gives
   `ofReal annILower * L_in ≤ μ*(E ∩ closedBall K.center annR₀)`.
2. *Exterior.* `ann_m4_exterior_domain` (`AnnularAnalytic.lean:196`) is
   destructured into its seven components and fed, together with the *same*
   `hhigh`, to `annular_exterior_A_out_greedy_lower_bound`
   (`AnnularGreedyInfinite.lean:516`) at `eps = annEps`, `a = annA`,
   `r0 = annR₀`, `R₁ = annR₁`. This gives
   `ofReal annCExt * L_out ≤ μ*(E \ closedBall K.center annR₀)` after rewriting
   the literal `min` by `← annCExt_eq_literal`. Both ledgers use the *same* ball
   radius `annR₀`, which is what makes the split legal.
3. *Lowering and gluing.* `ENNReal.ofReal_le_ofReal` on
   `annJointCoefficient ≤ annILower` and `≤ annCExt`, then `mul_le_mul_left`,
   then `mul_add` and `outerMeasure_ge_add_of_inter_of_diff`
   (`BallSplit.lean:34`) produce
   `ofReal annJointCoefficient * (L_in + L_out) ≤ μ*(E)`
   (`annular_joint_ledger`).
4. *Direction mass.* `K.A_out_radius annR₁` is **definitionally**
   `(K.A_in_radius annR₁)ᶜ` (`Trichotomy.lean:56`), so
   `pi_le_directionAngleOuter_add_compl` applies directly and yields
   `ofReal π ≤ L_in + L_out`.
5. *Strictness.* `ofReal (π · annTarget) = ofReal annTarget * ofReal π` by
   `← ENNReal.ofReal_mul annTarget_pos.le` and `mul_comm` (this is the explicit
   nonnegativity bridge); then `mul_le_mul_right` against step 4; then
   `ENNReal.mul_lt_mul_left hS0 hStop` applied to
   `(ENNReal.ofReal_lt_ofReal_iff annJointCoefficient_pos).2
   annTarget_lt_annJointCoefficient`; then step 3.

### 22.6 `ℝ≥0∞` and measurability discipline

* **No cancellation.** The single strict multiplicative step is
  `ENNReal.mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) : b*a < c*a`
  — a *monotonicity* lemma. At no point is `a * x < a * y → x < y` used, and at
  no point is a factor divided out.
* **Side conditions are proved, not assumed.**
  `hS0 : L_in + L_out ≠ 0` is `ne_of_gt` of
  `ENNReal.ofReal_pos.2 Real.pi_pos` composed with step 4.
  `hStop : L_in + L_out ≠ ⊤` is `ne_top_of_le_ne_top` of
  `ofReal π + ofReal π ≠ ⊤` and `add_le_add` of two instances of
  `directionAngleOuter_le_pi`.
* **No measurability of direction classes.** `A_in_radius` and `A_out_radius`
  are not asserted measurable anywhere, and M7 does not assert it either. The
  complement identity is therefore used **only** through
  `Set.univ ⊆ A ∪ Aᶜ` + `measure_mono` + `measure_union_le`; the equality
  `L_in + L_out = π`, which would require Carathéodory measurability of `A`, is
  never stated and never used. The one Carathéodory split that *is* used
  (`outerMeasure_ge_add_of_inter_of_diff`) splits along a **closed ball**, which
  is measurable, and `E` itself is not assumed measurable.
* **The direction masses are the same object on both sides.** M4 concludes in
  `directionAngleOuter (K.A_out_radius R₁)` and M5/M6 conclude in
  `directionAngleOuter (K.A_in_radius R₁)`; both are the metric Hausdorff length
  `μH[1]` of `CaseIIGeometry.lean:633`, so no bridge lemma is needed between the
  two ledgers.

### 22.7 Builds

All green, from the worktree Lean root
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`
(toolchain `leanprover/lean4:v4.30.0-rc2`, Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, both unchanged):

```
lake build StarKakeyaLower.AnnularAssembly        Build completed successfully (8345 jobs)
lake build StarKakeyaLower                        Build completed successfully (8364 jobs)
lake build StarKakeyaLowerAudit                   Build completed successfully (8367 jobs)
lake build StarKakeyaLower StarKakeyaLowerAudit   Build completed successfully (8369 jobs)
```

A cold rebuild with all project oleans and IR deleted (Mathlib oleans kept)
succeeded in `2m35s`, so no stale olean is involved.

`AnnularAssembly.lean` emits **zero** warnings — including zero style-linter
warnings; the two deprecated aliases `mul_le_mul_right'` / `mul_le_mul_left'`
that the first draft used were replaced by the current `mul_le_mul_left` /
`mul_le_mul_right`.

### 22.8 Axiom receipts

`lake build StarKakeyaLowerAudit` emits **477** `#print axioms` receipts. After
normalising the line wrapping, the set of distinct axiom lists has exactly one
element:

```
propext, Classical.choice, Quot.sound
```

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.ofReduceNat`, no
`Lean.trustCompiler` occurs anywhere in the audit output. The seventeen new M7
receipts (`Audit.lean:554`–`:570`) are

```
StarKakeyaLower.annCExt                                   [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annCExt_eq_literal                        [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annJointCoefficient                       [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annJointCoefficient_le_annILower          [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annJointCoefficient_le_annCExt            [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annTarget_lt_annCExt                      [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annTarget_lt_annJointCoefficient          [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annJointCoefficient_pos                   [propext, Classical.choice, Quot.sound]
StarKakeyaLower.directionAngleOuter_le_pi                 [propext, Classical.choice, Quot.sound]
StarKakeyaLower.pi_le_directionAngleOuter_add_compl       [propext, Classical.choice, Quot.sound]
StarKakeyaLower.ann_target_lt_high_threshold              [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annular_joint_ledger                      [propext, Classical.choice, Quot.sound]
StarKakeyaLower.annular_lower_bound                       [propext, Classical.choice, Quot.sound]
StarKakeyaLower.UniversalAnnularLowerBound                [propext, Classical.choice, Quot.sound]
StarKakeyaLower.universal_annular_lower_bound             [propext, Classical.choice, Quot.sound]
StarKakeyaLower.pi_mul_annTarget_eq                       [propext, Classical.choice, Quot.sound]
StarKakeyaLower.universal_annular_lower_bound_normalForm  [propext, Classical.choice, Quot.sound]
```

and the old final theorem is unchanged:

```
StarKakeyaLower.universal_strong_lower_bound              [propext, Classical.choice, Quot.sound]
```

### 22.9 Old-API probes

The three probes of the M6 endpoint pass, which pin that the pre-M6 public
names, kinds, constructors and projections are unchanged, were re-run against
the post-M7 tree and all exit `0`:

```
lake env lean probe/ProbeEnvelope.lean       exit 0
lake env lean probe/ProbeLocalContact.lean   exit 0
lake env lean probe/ProbeClosure.lean        exit 0
```

### 22.10 Scans

* `grep -rnE "\bsorry\b|\badmit\b|native_decide|\baxiom "` over
  `StarKakeyaLower/`, `StarKakeyaLower.lean` and `probe/` returns only three
  hits, all of them the word `native_decide` inside prose docstrings of
  `AnnularKernel`, `AnnularAnalytic` and `AnnularEndpoint` saying that it is
  *not* used. No `sorry`, no `admit`, no local `axiom`.
* Import-cycle scan over `StarKakeyaLower/`: acyclic.
* Frozen-constant body scan over the 32-module M7 closure: empty (§22.2).
* `git status`: five modified tracked files —
  `…/04-lean/StarKakeyaLower.lean` (+41 / −15),
  `…/04-lean/StarKakeyaLower/Audit.lean` (+31 / −4), and the three spike
  documents `LEAN-PLAN.md`, `LEAN-STATUS.md` and `README.md` (documentation
  only; `README.md` had two stale claims — "No Lean theorem exists for this
  route" and the "Lean pending" verdict — which are now marked superseded) —
  plus one untracked file,
  `…/04-lean/StarKakeyaLower/AnnularAssembly.lean`.
  `git diff --check` is clean. Nothing else in the repository is touched;
  `paper/` is untouched; `certificate.json` was restored after the re-run, so
  the only re-run side effect (its `elapsed_seconds` field) is not in the diff;
  no sibling worktree was touched. **Nothing is committed and nothing is
  pushed**, so the change is available for independent final review.

### 22.11 Cross-check against the numeric evidence — *evidence, not proof*

The two Python artefacts of this spike were re-run as an independent
cross-check. **They are evidence at the level stated in `README.md`; they are
not part of any Lean proof, no Lean statement depends on them, and the Lean
gates were reproved from scratch by exact rational and squared-rational
arithmetic.**

* `certify.py` (Arb outward-rounded intervals, python-flint 0.9.0):
  `production_decision.accepted = true`, `all_mutation_controls_passed = true`,
  `fixed_path_guard_passed = true`, all four mutation controls and all five
  fixed-path guard controls matched **and rejected**. Reported
  `joint_coefficient_lower = 0.0209706915542672869889884168515` and
  `joint_margin_above_target_lower = 1.069…e-5` above `131/6250 = 0.02096`.
  Re-running reproduces `certificate.json` byte-for-byte except for the
  `elapsed_seconds` field; the file was restored, so it is *not* part of the
  diff.
* `test_annular_geometry.py` (falsification test): `all_passed = true`, with all
  seven checks passing — `one_sidedness_lemma_4_1`, `exact_width_lemma_4_3`,
  `exterior_area_proposition_4_5`, `payment_proposition_5_3`,
  `adversarial_optimisation`, `monte_carlo_cross_validation`,
  `falsification_power_control` (240 overclaim counterexamples found for the
  deliberately-too-strong control, as intended).

The numeric lower bound `0.020 970 69…` for the joint coefficient is consistent
with, and slightly stronger than, the Lean-proved
`annJointCoefficient = min annILower annCExt` with
`annILower = 2097/100000 = 0.02097` — but the Lean proof does not consume it.

### 22.12 Honest statement of what M7 does and does not establish

* It establishes `131π/6250 < L²*(E)` for every star-shaped Kakeya set `E` with
  star centre `K.center`, in Lean, unconditionally, from the three standard
  Mathlib axioms.
* It does **not** retract, weaken or rewrite `100π/5599`; that theorem and its
  receipt are unchanged, and the two proofs are import-disjoint below their
  shared CLEAN base.
* It does **not** claim optimality of the tuple, of the constant, or of the
  route. `scout.py`/`result.json` remain a numerical spike with no optimality
  claim.
* It adds **no** numeric, geometric or analytic assumption of its own: every
  constant it mentions comes from `AnnularKernel`/`AnnularCaseIIntegral`, and
  every inequality it consumes is a theorem proved in M1, M4 or M6.
* It does **not** construct a witness of `StarShapedKakeya E`. As with
  `universal_strong_lower_bound`, the tree contains no `Nonempty
  (StarShapedKakeya _)` instance, so neither final theorem is accompanied by a
  Lean-level refutation of vacuity. This is a pre-existing property of the
  development's hypothesis class, is identical for both final theorems, and is
  outside M7's scope; it does not affect the logical content of
  `∀ E, StarShapedKakeya E → …`.
