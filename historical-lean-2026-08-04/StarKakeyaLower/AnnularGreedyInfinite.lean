import StarKakeyaLower.AnnularGreedy

/-!
# Infinite, summable and `⊤` branches of the annular exterior bound (M4)

`AnnularGreedy.lean` (M3a/M3b) proves the exterior lower bound **conditionally
on a supplied `FiniteFixedSelection`**.  This module removes that input.  It
exhausts the actual `fixedSelectionOutcome` and contributes exactly the three
cases `PROOF.md` §8.6 distinguishes:

* the finite stop — delegated verbatim to M3b;
* the infinite selection with **infinite** deletion cost `B = ⊤` — closed by
  `PROOF.md` (8.3a), which uses only the selected cones: no residual-zero
  argument and no fan;
* the infinite selection with **finite** deletion cost `B ≠ ⊤` — closed by
  `PROOF.md` (B4) + (8.3b), i.e. summability forces the residual heights to
  vanish, after which the M3b annular fan applies.

**No new geometry.**  Every planar estimate is M2's
`UnitNeedle.annular_payment_triangleInterior` or M3b's
`StarShapedKakeya.residualFan_annulus_outerMeasure_lower`; everything added
here is the countable ledger and the case analysis.

Sums live on the **open** restricted triangles `triangleInterior · \ closedBall ·`;
closed hulls are never claimed pairwise disjoint.

The final theorem `annular_exterior_greedy_lower_bound` needs neither
`rho ≤ 1`, nor `1/2 < rho`, nor any `caseIIKappa` factor (`PROOF.md`
Remark 8.2): the two coefficients are combined by an explicit `min`.
-/

open Set MeasureTheory Metric Filter

namespace StarKakeyaLower

noncomputable section

namespace FixedDeletionGreedyData

variable {height H : Direction → ℝ} (G : FixedDeletionGreedyData height H)

/-! ## 1. The countable restricted selected triangles -/

/-- The exterior part of the `n`-th selected **open** triangle.  Countable
analogue of `FiniteFixedSelection.restrictedTriangle`. -/
def restrictedTriangle {E : Set Plane} (K : StarShapedKakeya E) (r0 : ℝ)
    (n : ℕ) : Set Plane :=
  (K.needleFamily (G.selected n)).triangleInterior K.center \
    Metric.closedBall K.center r0

theorem measurableSet_restrictedTriangle {E : Set Plane}
    (K : StarShapedKakeya E) (r0 : ℝ) (n : ℕ) :
    MeasurableSet (G.restrictedTriangle K r0 n) :=
  ((K.needleFamily (G.selected n)).triangleInterior_measurable K.center).diff
    measurableSet_closedBall

/-- The countable union of the restricted selected open triangles. -/
def restrictedSelectedUnion {E : Set Plane} (K : StarShapedKakeya E)
    (r0 : ℝ) : Set Plane :=
  ⋃ n, G.restrictedTriangle K r0 n

theorem restrictedSelectedUnion_eq {E : Set Plane} (K : StarShapedKakeya E)
    (r0 : ℝ) :
    G.restrictedSelectedUnion K r0 =
      (⋃ n, (K.needleFamily (G.selected n)).triangleInterior K.center) \
        Metric.closedBall K.center r0 := by
  simp [restrictedSelectedUnion, restrictedTriangle, iUnion_diff]

theorem measurableSet_restrictedSelectedUnion {E : Set Plane}
    (K : StarShapedKakeya E) (r0 : ℝ) :
    MeasurableSet (G.restrictedSelectedUnion K r0) :=
  MeasurableSet.iUnion fun n => G.measurableSet_restrictedTriangle K r0 n

theorem restrictedSelectedUnion_subset {E : Set Plane}
    (K : StarShapedKakeya E) (r0 : ℝ) :
    G.restrictedSelectedUnion K r0 ⊆ E \ Metric.closedBall K.center r0 := by
  rw [G.restrictedSelectedUnion_eq K r0]
  exact diff_subset_diff_left (iUnion_subset fun n =>
    (UnitNeedle.triangleInterior_subset_triangleHull K.center _).trans
      (K.triangleHull_subset (G.selected n)))

/-- **Restricted disjointness by monotonicity**, countable version: deleting a
common set preserves the disjointness of the selected open triangles.  Nothing
is claimed about the closed hulls. -/
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
      (G.restrictedTriangle K r0 j)) := by
  intro i j hij
  exact (G.pairwise_disjoint_selected_triangleInterior K.center
    (fun n => K.needleFamily (G.selected n)) hrho
    (fun n => hheight (G.selected n)) hselected_pos hselected_lt hH
    (fun n => K.needleFamily_hasDirection (G.selected n))
    (fun n => hout _ (G.remaining_subset_initial n (G.selected_mem n)))
    hij).mono diff_subset diff_subset

/-- **Countable exterior additivity.** -/
theorem volume_restrictedSelectedUnion {E : Set Plane}
    (K : StarShapedKakeya E) (r0 : ℝ)
    (hpair : Pairwise (fun i j => Disjoint (G.restrictedTriangle K r0 i)
      (G.restrictedTriangle K r0 j))) :
    volume (G.restrictedSelectedUnion K r0) =
      ∑' n, volume (G.restrictedTriangle K r0 n) :=
  measure_iUnion hpair fun n => G.measurableSet_restrictedTriangle K r0 n

/-- **The countable exterior ledger** (`PROOF.md` (8.3a), ledger half).  The
series of restricted selected areas is bounded by the exterior outer measure.
This uses **only** the selected cones: no residual, no fan, no (B4). -/
theorem tsum_volume_restrictedTriangle_le_outerMeasure
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (r0 : ℝ) :
    (∑' n, volume (G.restrictedTriangle K r0 n)) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  rw [← G.volume_restrictedSelectedUnion K r0
    (G.pairwise_disjoint_restrictedTriangle K hrho hheight hselected_pos
      hselected_lt hH hout r0), Measure.toOuterMeasure_apply]
  exact measure_mono (G.restrictedSelectedUnion_subset K r0)

/-! ## 2. The infinite annular payment -/

/-- Itemwise M2 payment, summed.  `hCext` is what licenses `ENNReal.ofReal_mul`
in the coefficient extraction. -/
theorem cost_le_tsum_volume_restrictedTriangle
    {E : Set Plane} (K : StarShapedKakeya E) {a rho r0 : ℝ}
    (ha : 0 < a) (harho : a < G.multiplier * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho G.multiplier)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hbound : ∀ theta ∈ G.initial, height theta ≤ a)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho G.multiplier) *
        (∑' n, ENNReal.ofReal (H (G.selected n))) ≤
      ∑' n, volume (G.restrictedTriangle K r0 n) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have hmem : G.selected n ∈ G.initial :=
    G.remaining_subset_initial n (G.selected_mem n)
  have hpay := (K.needleFamily (G.selected n)).annular_payment_triangleInterior
    G.multiplier_pos G.multiplier_lt_one ha harho hr0 hlt
    (by
      have := hbound _ hmem
      rwa [hheight] at this)
    (hout _ hmem)
  rw [← ENNReal.ofReal_mul hCext.le, hH n, hheight]
  exact hpay

/-- The deletion-budget normalisation `C_ext/4` against `Σ' 4 H_n`. -/
theorem quarter_cost_eq_cost {rho r0 a : ℝ} (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho G.multiplier)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho))) :
    ENNReal.ofReal (annularCExt a r0 rho G.multiplier / 4) *
        (∑' n, ENNReal.ofReal (4 * H (G.selected n))) =
      ENNReal.ofReal (annularCExt a r0 rho G.multiplier) *
        (∑' n, ENNReal.ofReal (H (G.selected n))) := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hH0 : 0 ≤ H (G.selected n) := by
    rw [hH n]
    exact Real.arcsin_nonneg.2 (div_nonneg (hselected_pos n).le
      (mul_pos G.multiplier_pos (lt_trans hr0 hlt)).le)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCext.le]
  congr 1
  ring

/-- **`PROOF.md` (8.3a): the unconditional cone-only exterior inequality.**
Only the selected triangles occur; the residual is never mentioned, so this
holds whether or not (B4) is available. -/
theorem quarter_cost_le_outerMeasure_infinite
    {E : Set Plane} (K : StarShapedKakeya E) {a rho r0 : ℝ}
    (ha : 0 < a) (harho : a < G.multiplier * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho G.multiplier)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hbound : ∀ theta ∈ G.initial, height theta ≤ a)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center) :
    ENNReal.ofReal (annularCExt a r0 rho G.multiplier / 4) *
        (∑' n, ENNReal.ofReal (4 * H (G.selected n))) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  rw [G.quarter_cost_eq_cost hr0 hlt hCext hselected_pos hH]
  exact (G.cost_le_tsum_volume_restrictedTriangle K ha harho hr0 hlt hCext
      hheight hbound hH hout).trans
    (G.tsum_volume_restrictedTriangle_le_outerMeasure K (lt_trans hr0 hlt)
      hheight hselected_pos hselected_lt hH hout r0)

/-- **The `B = ⊤` branch.**  Infinite deletion cost together with a positive
payment coefficient forces the exterior outer measure to be infinite.  Proved
from (8.3a) only: no residual-zero argument, no fan. -/
theorem outerMeasure_diff_eq_top_of_cost_eq_top
    {E : Set Plane} (K : StarShapedKakeya E) {a rho r0 : ℝ}
    (ha : 0 < a) (harho : a < G.multiplier * rho)
    (hr0 : 0 < r0) (hlt : r0 < rho)
    (hCext : 0 < annularCExt a r0 rho G.multiplier)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hbound : ∀ theta ∈ G.initial, height theta ≤ a)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hB : (∑' n, ENNReal.ofReal (4 * H (G.selected n))) = ⊤) :
    volume.toOuterMeasure (E \ Metric.closedBall K.center r0) = ⊤ := by
  have hq : ENNReal.ofReal (annularCExt a r0 rho G.multiplier / 4) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hmain := G.quarter_cost_le_outerMeasure_infinite K ha harho hr0 hlt hCext
    hheight hbound hselected_pos hselected_lt hH hout
  rw [hB, ENNReal.mul_top hq] at hmain
  exact top_unique hmain

/-! ## 3. The summable (`B ≠ ⊤`) branch

`PROOF.md` (B4).  The existing `residual_height_zero_of_summable_cost`
(`CaseIISelection.lean:636`) is **not** usable here: its hypothesis
`hheight_le_H : ∀ n, height (G.selected n) ≤ H (G.selected n)` is discharged in
`caseII_fixed_greedy_lower_bound` only through `m * rho ≤ 1`, i.e. through the
`rho ≤ 1` hypothesis that the annular route explicitly does not have
(`PROOF.md` Remark 8.2).  The replacement below takes the route of `PROOF.md`
§8.3 literally instead: `H_n → 0` gives `δ_n = m ρ sin H_n → 0` directly, with
no comparison between `δ_n` and `H_n` and no constraint on `m ρ`. -/

/-- Summable deletion cost forces the **selected** heights to vanish, via the
exact paper-weight relation `δ = m ρ sin (H (δ))`.  No bound of the form
`height ≤ H`, and in particular no `rho ≤ 1`, is used. -/
theorem selected_height_tendsto_zero_of_summable {rho : ℝ} (hrho : 0 < rho)
    (hheight0 : ∀ theta, 0 ≤ height theta)
    (hselected_le : ∀ n, height (G.selected n) ≤ G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hcost : Summable fun n => H (G.selected n)) :
    Tendsto (fun n => height (G.selected n)) atTop (nhds 0) := by
  have hsin : ∀ n, height (G.selected n) =
      G.multiplier * rho * Real.sin (H (G.selected n)) := by
    intro n
    rw [hH n]
    exact height_eq_multiplier_rho_sin_paperWeight G.multiplier_pos hrho
      (hheight0 _) (hselected_le n)
  have hHtend : Tendsto (fun n => H (G.selected n)) atTop (nhds 0) :=
    hcost.tendsto_atTop_zero
  have hmul : Tendsto
      (fun n => G.multiplier * rho * Real.sin (H (G.selected n))) atTop
      (nhds (G.multiplier * rho * Real.sin 0)) :=
    (((Real.continuous_sin.tendsto 0).comp hHtend).const_mul _)
  rw [Real.sin_zero, mul_zero] at hmul
  exact hmul.congr fun n => (hsin n).symm

/-- **`PROOF.md` (B4) for the annular route.**  Summable deletion cost forces
every residual height to vanish.  The order core is the existing
`residual_height_eq_zero_of_tendsto` (`GreedyResidual.lean:39`); the greedy
bound is `G.dominates`. -/
theorem residual_height_zero_of_summable_paperWeight {rho : ℝ} (hrho : 0 < rho)
    (hheight0 : ∀ theta, 0 ≤ height theta)
    (hselected_le : ∀ n, height (G.selected n) ≤ G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (hcost : Summable fun n => H (G.selected n)) :
    ∀ theta ∈ greedyResidual G.remaining, height theta = 0 := by
  intro theta htheta
  exact residual_height_eq_zero_of_tendsto height G.remaining hheight0
    G.multiplier_pos
    (fun n x hx => (G.dominates n x (mem_iInter.mp hx n)).le)
    (G.selected_height_tendsto_zero_of_summable hrho hheight0 hselected_le hH
      hcost)
    htheta

/-- The restricted fan and the restricted selected union stay disjoint:
`PROOF.md` (B3) survives deletion of a common set. -/
theorem disjoint_restrictedResidualFan_restrictedSelectedUnion
    {E : Set Plane} (K : StarShapedKakeya E) {rho : ℝ} (hrho : 0 < rho)
    (hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho)))
    (r0 : ℝ) :
    Disjoint
      (residualFan K (greedyResidual G.remaining) \
        Metric.closedBall K.center r0)
      (G.restrictedSelectedUnion K r0) := by
  rw [G.restrictedSelectedUnion_eq K r0]
  exact (G.disjoint_residualFan_selectedTriangleUnion K hrho hzero hout hheight
    hselected_pos hselected_lt hH).mono diff_subset diff_subset

/-- **`PROOF.md` (8.3b), countable version.**  The restricted residual fan and
the series over the restricted **open** selected triangles are added by
Carathéodory separation inside `E \ closedBall K.center r0`. -/
theorem geometric_exterior_outerMeasure_lower_infinite
    {E : Set Plane} (K : StarShapedKakeya E) {rho r0 : ℝ}
    (hr0 : 0 ≤ r0) (hle : r0 ≤ rho) (hrho : 0 < rho)
    (hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0)
    (hout : ∀ theta ∈ G.initial,
      (K.needleFamily theta).OutsideBall rho K.center)
    (hheight : ∀ theta, height theta = (K.needleFamily theta).height K.center)
    (hselected_pos : ∀ n, 0 < height (G.selected n))
    (hselected_lt : ∀ n, height (G.selected n) < G.multiplier * rho)
    (hH : ∀ n, H (G.selected n) =
      Real.arcsin (height (G.selected n) / (G.multiplier * rho))) :
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
          directionAngleOuter (greedyResidual G.remaining) +
        ∑' n, volume (G.restrictedTriangle K r0 n) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  have hresinit : greedyResidual G.remaining ⊆ G.initial := fun theta htheta =>
    G.remaining_subset_initial 0 (mem_iInter.mp htheta 0)
  have hfan := K.residualFan_annulus_outerMeasure_lower hr0 hle hrho
    (greedyResidual G.remaining) hzero
    (fun theta htheta => hout theta (hresinit htheta))
  have hpair := G.pairwise_disjoint_restrictedTriangle K hrho hheight
    hselected_pos hselected_lt hH hout r0
  have hdisj := G.disjoint_restrictedResidualFan_restrictedSelectedUnion K hrho
    hzero hout hheight hselected_pos hselected_lt hH r0
  have hadd : volume (residualFan K (greedyResidual G.remaining) \
        Metric.closedBall K.center r0) +
      volume (G.restrictedSelectedUnion K r0) ≤
        volume (E \ Metric.closedBall K.center r0) :=
    outerMeasure_add_le_of_disjoint_measurable
      (G.measurableSet_restrictedSelectedUnion K r0) hdisj
      (diff_subset_diff_left (K.residualFan_subset (greedyResidual G.remaining)))
      (G.restrictedSelectedUnion_subset K r0)
  rw [Measure.toOuterMeasure_apply]
  calc
    ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
            directionAngleOuter (greedyResidual G.remaining) +
          ∑' n, volume (G.restrictedTriangle K r0 n)
        = ENNReal.ofReal ((rho ^ 2 - r0 ^ 2) / 2) *
              directionAngleOuter (greedyResidual G.remaining) +
            volume (G.restrictedSelectedUnion K r0) := by
      rw [G.volume_restrictedSelectedUnion K r0 hpair]
    _ ≤ volume (residualFan K (greedyResidual G.remaining) \
            Metric.closedBall K.center r0) +
          volume (G.restrictedSelectedUnion K r0) := by
      refine add_le_add ?_ le_rfl
      rw [← Measure.toOuterMeasure_apply]
      exact hfan
    _ ≤ volume (E \ Metric.closedBall K.center r0) := hadd

/-- **The `B ≠ ⊤` branch.**  Same `min` coefficient as the finite theorem of
M3b, obtained from the same three ingredients: the deletion coverage budget
(B1), the annular payment (8.2), and the exterior geometry (8.3b). -/
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
        (min (annularCExt a r0 rho G.multiplier / 4)
          ((rho ^ 2 - r0 ^ 2) / 2)) *
        directionAngleOuter G.initial ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  have hrho : 0 < rho := lt_trans hr0 hlt
  have hH0 : ∀ n, 0 ≤ H (G.selected n) := by
    intro n
    rw [hH n]
    exact Real.arcsin_nonneg.2 (div_nonneg (hselected_pos n).le
      (mul_pos G.multiplier_pos hrho).le)
  have hsum : Summable fun n => H (G.selected n) :=
    summable_of_cost_tsum_ne_top hH0 hB
  have hzeroHeight := G.residual_height_zero_of_summable_paperWeight hrho
    hheight0 (fun n => (hselected_lt n).le) hH hsum
  have hzero : ∀ theta ∈ greedyResidual G.remaining,
      (K.needleFamily theta).height K.center = 0 := by
    intro theta htheta
    have h := hzeroHeight theta htheta
    rwa [hheight] at h
  have hpayment : ENNReal.ofReal (annularCExt a r0 rho G.multiplier / 4) *
      (∑' n, ENNReal.ofReal (4 * H (G.selected n))) ≤
        ∑' n, volume (G.restrictedTriangle K r0 n) := by
    rw [G.quarter_cost_eq_cost hr0 hlt hCext hselected_pos hH]
    exact G.cost_le_tsum_volume_restrictedTriangle K ha harho hr0 hlt hCext
      hheight hbound hH hout
  exact round2_min_initial_angle_lower_bound
    (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    G.initial_directionAngleOuter_le_residual_add_cost hpayment
    (G.geometric_exterior_outerMeasure_lower_infinite K hr0.le hlt.le hrho hzero
      hout hheight hselected_pos hselected_lt hH)

end FixedDeletionGreedyData

/-! ## 4. The outcome wrapper

The `FiniteFixedSelection` input of M3b is discharged here by running the actual
`fixedSelectionOutcome` (`CaseIISelection.lean:194`) and exhausting its two
constructors; in the infinite constructor the deletion cost is split on
`B = ⊤` versus `B ≠ ⊤`.  The resulting theorem takes no selection as input. -/

/-- **M4 exit theorem** (`PROOF.md` Proposition 8.1, exterior greedy budget).
For an **arbitrary, possibly nonmeasurable** direction set `A` all of whose
chosen needles escape `B(center, rho)` and stay below the height cap `a`, the
exterior outer measure is bounded below by
`min (C_ext / 4) ((rho² - r₀²) / 2)` times the initial angular outer measure.

Unconditional in the deletion budget: the finite stop, the summable infinite
selection and the `B = ⊤` infinite selection are all covered.  Following
`PROOF.md` Remark 8.2 there is **no** `rho ≤ 1`, **no** `1/2 < rho` and **no**
`caseIIKappa` factor; the two coefficients are combined by an explicit `min`.
`hCext` is threaded unchanged from M3a: it is what licenses `ENNReal.ofReal_mul`
in the coefficient extraction at every level. -/
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
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  have hrho : 0 < rho := lt_trans hr0 hlt
  set height : Direction → ℝ := fun theta =>
    (K.needleFamily theta).height K.center with hheightdef
  set m : ℝ := 1 - eps with hmdef
  set H : Direction → ℝ := fun theta =>
    Real.arcsin (height theta / (m * rho)) with hHdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have hm1 : m < 1 := by rw [hmdef]; linarith
  have hheight0 : ∀ theta, 0 ≤ height theta := fun theta =>
    UnitNeedle.height_nonneg _ _
  have hbound : ∀ theta ∈ A, height theta ≤ a := fun theta htheta =>
    (hlow theta htheta).le
  have hH0 : ∀ theta, 0 ≤ H theta := fun theta =>
    Real.arcsin_nonneg.2 (div_nonneg (hheight0 theta) (mul_pos hm0 hrho).le)
  cases fixedSelectionOutcome height H m A hheight0 hbound with
  | finite F =>
      exact annular_exterior_lower_bound_of_finiteSelection K F hm0 hm1 ha
        harhoScaled hr0 hlt hCext (fun _ => rfl) (fun _ => rfl) hout hlow
  | infinite hpositive =>
      let G : FixedDeletionGreedyData height H :=
        infiniteGreedyData hm0 hm1 hbound hpositive
          (fun n => directionAngleOuter_fixedDeletionBall_le (hH0 _))
      have hmem : ∀ n, G.selected n ∈ A := fun n =>
        G.remaining_subset_initial n (G.selected_mem n)
      have hmult : G.multiplier = m := rfl
      have hpos : ∀ n, 0 < height (G.selected n) := by
        intro n
        have hd := G.dominates n (G.selected n) (G.selected_mem n)
        rw [hmult] at hd
        nlinarith [hheight0 (G.selected n)]
      have hscaled : ∀ n, height (G.selected n) < G.multiplier * rho := by
        intro n
        rw [hmult]
        exact (hlow _ (hmem n)).trans harhoScaled
      have hHG : ∀ n, H (G.selected n) =
          Real.arcsin (height (G.selected n) / (G.multiplier * rho)) :=
        fun n => by rw [hmult]
      have houtG : ∀ theta ∈ G.initial,
          (K.needleFamily theta).OutsideBall rho K.center := hout
      have hboundG : ∀ theta ∈ G.initial, height theta ≤ a := hbound
      have hCextG : 0 < annularCExt a r0 rho G.multiplier := by rwa [hmult]
      have harhoG : a < G.multiplier * rho := by rwa [hmult]
      by_cases hB : (∑' n, ENNReal.ofReal (4 * H (G.selected n))) = ⊤
      · rw [G.outerMeasure_diff_eq_top_of_cost_eq_top K ha harhoG hr0 hlt hCextG
          (fun _ => rfl) hboundG hpos hscaled hHG houtG hB]
        exact le_top
      · have hmain := G.annular_exterior_lower_bound_of_summable K ha harhoG hr0
          hlt hCextG (fun _ => rfl) hheight0 hboundG hpos hscaled hHG houtG hB
        rwa [hmult] at hmain

/-- Non-vacuity of the exit theorem's coefficient: under the hypotheses of
`annular_exterior_greedy_lower_bound` the `min` is **strictly positive**, so the
conclusion is not the trivial `0 ≤ ·`.  (`(rho² - r₀²)/2 > 0` because
`0 < r₀ < rho`; `C_ext/4 > 0` is `hCext`.) -/
theorem annular_exterior_coefficient_pos {a r0 rho m : ℝ}
    (hr0 : 0 < r0) (hlt : r0 < rho) (hCext : 0 < annularCExt a r0 rho m) :
    0 < min (annularCExt a r0 rho m / 4) ((rho ^ 2 - r0 ^ 2) / 2) :=
  lt_min (by linarith) (by nlinarith)

/-- Paper `A_out` specialisation, mirroring
`caseII_A_out_fixed_greedy_lower_bound` (`CaseIISelection.lean:1292`): on the
radius-`R₁` escaping class the outside-ball hypothesis is supplied by the
radial structure of `triangleHull` itself, so callers provide only the
no-high-triangle premise.  No numeric constant and no frozen module is
involved: `A_out_radius` lives in the CLEAN `Trichotomy`, already in the import
closure. -/
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
      volume.toOuterMeasure (E \ Metric.closedBall K.center r0) := by
  apply annular_exterior_greedy_lower_bound K (K.A_out_radius R₁) heps0 heps1 ha
    hr0 hlt harhoScaled hCext
  · intro theta htheta
    exact (K.needleFamily theta).outsideBall_sub_one_of_not_triangleHull_subset_closedBall
      (by linarith) htheta
  · intro theta _
    exact lt_of_not_ge fun h => hhigh ⟨theta, h⟩

end

end StarKakeyaLower
