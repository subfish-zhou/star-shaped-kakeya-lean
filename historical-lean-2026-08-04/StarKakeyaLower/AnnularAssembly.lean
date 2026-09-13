import StarKakeyaLower.BallSplit
import StarKakeyaLower.AnnularGreedyInfinite
import StarKakeyaLower.AnnularAnalytic
import StarKakeyaLower.AnnularEndpoint

/-!
# M7 — final assembly of the joint inner/outer annular lower bound

This module closes the joint inner/outer route of
`spikes/001-joint-inner-outer/PROOF.md`: it glues the confined (inner) ledger of
M5/M6 to the exterior (outer) ledger of M3/M4 along the M1 Carathéodory split
and reads off the unconditional planar lower bound

`ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E`

for every star-shaped Kakeya set `E`, with `annTarget = 131 / 6250`.

## Architecture

Fix the production tuple of `StarKakeyaLower.AnnularKernel`.  The proof is a
two-way split on the height dichotomy at the cap `annA`:

* **High branch.** Some chosen triangle reaches height `annA`, so the area is at
  least `annA / 2` (`high_branch_outerMeasure`, `Trichotomy.lean`).  Gate (C1)
  `annTarget < annA / (2 * π)` (`AnnularAnalytic.lean`) turns this into the
  target after multiplying by `π > 0`.

* **Confined branch.**  No triangle is high.  Then

  - `annular_confined_lower_bound` (M6, `AnnularEndpoint.lean`) pays
    `ofReal annILower * L_in ≤ μ*(E ∩ closedBall K.center annR₀)`, and
  - `annular_exterior_A_out_greedy_lower_bound` (M4,
    `AnnularGreedyInfinite.lean`), instantiated at the production tuple through
    `ann_m4_exterior_domain`, pays
    `ofReal annCExt * L_out ≤ μ*(E \ closedBall K.center annR₀)`,

  where `L_in = directionAngleOuter (K.A_in_radius annR₁)` and
  `L_out = directionAngleOuter (K.A_out_radius annR₁)`.  The two ledgers are
  added by the M1 split `outerMeasure_ge_add_of_inter_of_diff`
  (`BallSplit.lean`) after lowering both coefficients to the common
  `annJointCoefficient = min annILower annCExt`, which by the interior gate (C2)
  `annTarget_lt_annILower` and the exterior gate `ann_m4_coefficient_gt_target`
  still strictly exceeds `annTarget`.

## Measurability discipline

Neither `A_in_radius` nor `A_out_radius` is claimed measurable, so the direction
mass identity `L_in + L_out = π` is **not** available.  Only the inequality
`ofReal π ≤ L_in + L_out` is used, and it is obtained from coverage of the
direction circle plus outer-measure subadditivity
(`pi_le_directionAngleOuter_add_compl` below).  The complementary bound
`L_in, L_out ≤ ofReal π` — also pure monotonicity — supplies the finiteness side
condition of the ENNReal strict multiplication.  No cancellation law on
`ℝ≥0∞` is used anywhere.

## Import hygiene

The four imports are exactly the modules whose statements are consumed: the M1
split, the M4 exterior exit, the M6 numeric/analytic gates and the M6
endpoint/confined exit (which transitively supplies the M6 integral gate).  In
particular no module carrying the frozen `100π/5599` witness constants is
reached, so the new bound is independent of the published one.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-! ## The joint coefficient -/

/-- The exterior payment coefficient of the annular tuple, in the literal
`min (C_ext / 4) ((ρ² - r₀²) / 2)` shape produced by the M4 exit theorem
`annular_exterior_A_out_greedy_lower_bound`. -/
def annCExt : ℝ :=
  min (annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) / 4)
    (((annR₁ - 1) ^ 2 - annR₀ ^ 2) / 2)

/-- `annCExt` is definitionally the coefficient appearing in the M4 conclusion. -/
theorem annCExt_eq_literal :
    annCExt =
      min (annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) / 4)
        (((annR₁ - 1) ^ 2 - annR₀ ^ 2) / 2) := rfl

/-- The coefficient common to both ledgers: the smaller of the certified radial
gain `annILower` (interior) and the greedy payment rate `annCExt` (exterior). -/
def annJointCoefficient : ℝ := min annILower annCExt

theorem annJointCoefficient_le_annILower : annJointCoefficient ≤ annILower :=
  min_le_left _ _

theorem annJointCoefficient_le_annCExt : annJointCoefficient ≤ annCExt :=
  min_le_right _ _

/-- Exterior gate at the production tuple, in the `annCExt` spelling. -/
theorem annTarget_lt_annCExt : annTarget < annCExt :=
  ann_m4_coefficient_gt_target

/-- **The joint gate.**  Both ledgers beat the target, hence so does the common
coefficient.  This is the only place where the interior gate (C2) and the
exterior gates (C3)/(C4) are combined. -/
theorem annTarget_lt_annJointCoefficient : annTarget < annJointCoefficient :=
  lt_min annTarget_lt_annILower annTarget_lt_annCExt

theorem annJointCoefficient_pos : 0 < annJointCoefficient :=
  annTarget_pos.trans annTarget_lt_annJointCoefficient

/-! ## Direction mass on a set and its complement

Both statements below are generic in the direction set: they use only
monotonicity and finite subadditivity of the outer Haar measure on the
projective direction circle, and never assume measurability. -/

/-- No direction set carries more angular mass than the whole circle. -/
theorem directionAngleOuter_le_pi (A : Set Direction) :
    directionAngleOuter A ≤ ENNReal.ofReal Real.pi := by
  rw [← directionOuterMeasure_eq_directionAngleOuter,
    ← StarShapedKakeya.directionOuterMeasure_univ]
  exact measure_mono (subset_univ A)

/-- **Direction mass ledger.**  A set and its complement cover the direction
circle, so their angular outer measures add up to at least `π`.  Equality would
require measurability and is deliberately not claimed. -/
theorem pi_le_directionAngleOuter_add_compl (A : Set Direction) :
    ENNReal.ofReal Real.pi ≤ directionAngleOuter A + directionAngleOuter Aᶜ := by
  have hcover : (Set.univ : Set Direction) ⊆ A ∪ Aᶜ := by
    intro d _
    by_cases hd : d ∈ A
    · exact Or.inl hd
    · exact Or.inr hd
  calc
    ENNReal.ofReal Real.pi
        = StarShapedKakeya.directionOuterMeasure (Set.univ : Set Direction) :=
      StarShapedKakeya.directionOuterMeasure_univ.symm
    _ ≤ StarShapedKakeya.directionOuterMeasure (A ∪ Aᶜ) := measure_mono hcover
    _ ≤ StarShapedKakeya.directionOuterMeasure A +
          StarShapedKakeya.directionOuterMeasure Aᶜ := measure_union_le _ _
    _ = directionAngleOuter A + directionAngleOuter Aᶜ := by
      rw [directionOuterMeasure_eq_directionAngleOuter,
        directionOuterMeasure_eq_directionAngleOuter]

/-! ## The two branches of the height dichotomy -/

/-- **High branch arithmetic.**  Gate (C1) `annTarget < annA / (2π)` is exactly
the statement that the unconditional high-triangle area `annA / 2` beats the
target `π · annTarget`.  `Real.pi` is eliminated by multiplying (C1) by `π > 0`;
no further transcendental input is used. -/
theorem ann_target_lt_high_threshold :
    ENNReal.ofReal (Real.pi * annTarget) < ENNReal.ofReal (annA / 2) := by
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num [annA] : 0 < annA / 2)).2 ?_
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmul : Real.pi * annTarget < Real.pi * (annA / (2 * Real.pi)) :=
    mul_lt_mul_of_pos_left ann_gate_C1 hpi
  have hsimp : Real.pi * (annA / (2 * Real.pi)) = annA / 2 := by
    field_simp
  rwa [hsimp] at hmul

variable {E : Set Plane}

/-- **The confined-branch ledger.**  Under the no-high hypothesis the interior
(M6) and exterior (M4) payments are lowered to the common coefficient and glued
by the M1 Carathéodory split at radius `annR₀`. -/
theorem annular_joint_ledger (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      annA ≤ (K.needleFamily theta).height K.center) :
    ENNReal.ofReal annJointCoefficient *
        (directionAngleOuter (K.A_in_radius annR₁) +
          directionAngleOuter (K.A_out_radius annR₁)) ≤
      volume.toOuterMeasure E := by
  obtain ⟨heps0, heps1, ha, hr0, hlt, harho, hCextPos⟩ := ann_m4_exterior_domain
  have hconf := annular_confined_lower_bound K hhigh
  have hext := annular_exterior_A_out_greedy_lower_bound K heps0 heps1 ha hr0 hlt
    harho hCextPos hhigh
  rw [← annCExt_eq_literal] at hext
  have hin : ENNReal.ofReal annJointCoefficient *
      directionAngleOuter (K.A_in_radius annR₁) ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center annR₀) :=
    le_trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal annJointCoefficient_le_annILower) _) hconf
  have hout : ENNReal.ofReal annJointCoefficient *
      directionAngleOuter (K.A_out_radius annR₁) ≤
      volume.toOuterMeasure (E \ Metric.closedBall K.center annR₀) :=
    le_trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal annJointCoefficient_le_annCExt) _) hext
  rw [mul_add]
  exact outerMeasure_ge_add_of_inter_of_diff E K.center annR₀ hin hout

/-- **The joint lower bound for a fixed star-shaped Kakeya set.**

Both branches of the height dichotomy at the cap `annA` are discharged; no
geometric, analytic or numeric hypothesis remains. -/
theorem annular_lower_bound (K : StarShapedKakeya E) :
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E := by
  by_cases hhigh : ∃ theta : Direction,
      annA ≤ (K.needleFamily theta).height K.center
  · exact ann_target_lt_high_threshold.trans_le (K.high_branch_outerMeasure hhigh)
  set Lin := directionAngleOuter (K.A_in_radius annR₁) with hLin
  set Lout := directionAngleOuter (K.A_out_radius annR₁) with hLout
  have hcompl : K.A_out_radius annR₁ = (K.A_in_radius annR₁)ᶜ := rfl
  have hpi_le : ENNReal.ofReal Real.pi ≤ Lin + Lout := by
    rw [hLin, hLout, hcompl]
    exact pi_le_directionAngleOuter_add_compl _
  have hpi_pos : (0 : ℝ≥0∞) < ENNReal.ofReal Real.pi :=
    ENNReal.ofReal_pos.2 Real.pi_pos
  have hS0 : Lin + Lout ≠ 0 := ne_of_gt (hpi_pos.trans_le hpi_le)
  have hStop : Lin + Lout ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (add_le_add (directionAngleOuter_le_pi (K.A_in_radius annR₁))
        (directionAngleOuter_le_pi (K.A_out_radius annR₁)))
    exact (ENNReal.add_ne_top).2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  calc
    ENNReal.ofReal (Real.pi * annTarget)
        = ENNReal.ofReal annTarget * ENNReal.ofReal Real.pi := by
      rw [← ENNReal.ofReal_mul annTarget_pos.le, mul_comm]
    _ ≤ ENNReal.ofReal annTarget * (Lin + Lout) := mul_le_mul_right hpi_le _
    _ < ENNReal.ofReal annJointCoefficient * (Lin + Lout) :=
      ENNReal.mul_lt_mul_left hS0 hStop
        ((ENNReal.ofReal_lt_ofReal_iff annJointCoefficient_pos).2
          annTarget_lt_annJointCoefficient)
    _ ≤ volume.toOuterMeasure E := annular_joint_ledger K hhigh

/-! ## The final statement -/

/-- **The joint inner/outer annular lower bound.**  It is proved below by
`universal_annular_lower_bound`. -/
def UniversalAnnularLowerBound : Prop :=
  ∀ (E : Set Plane), StarShapedKakeya E →
    ENNReal.ofReal (Real.pi * annTarget) < volume.toOuterMeasure E

/-- **The joint inner/outer annular lower bound, unconditionally.** -/
theorem universal_annular_lower_bound : UniversalAnnularLowerBound :=
  fun _ K => annular_lower_bound K

/-! ## Normal form of the constant -/

/-- The target coefficient in lowest terms: `π · annTarget = 131 π / 6250`. -/
theorem pi_mul_annTarget_eq : Real.pi * annTarget = 131 * Real.pi / 6250 := by
  rw [annTarget]; ring

/-- The final bound with the constant displayed in normal form. -/
theorem universal_annular_lower_bound_normalForm (E : Set Plane)
    (K : StarShapedKakeya E) :
    ENNReal.ofReal (131 * Real.pi / 6250) < volume.toOuterMeasure E := by
  rw [← pi_mul_annTarget_eq]
  exact annular_lower_bound K

end

end StarKakeyaLower
