import StarKakeyaLower.CaseIRadialCore

/-!
# Endpoint-capacity sliver covering adapter

A zero-safe arbitrary-family wrapper around the existing quotient-circle Haar
growth theorem.  Geometry callers provide:

* containment of the direction class in the union of dilated slivers;
* the direction-mass lower bound;
* containment of the undilated sliver bases in the actual radial section.

The conclusion is a fixed-radius angular-section lower bound.  This module is
pure covering/measure infrastructure; it does not yet construct slivers from a
physical unit chord.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-- Zero-safe arbitrary-family containment by quotient-circle slivers. -/
def HybridSliverFamilyContainment {ι : Type*}
    (A : Set ProjectiveDirection) (g : ℝ) (x rad : ι → ℝ) : Prop :=
  A ⊆ ⋃ i, quotientHybridCenteredDilate g Real.pi (x i) (rad i)

/-- **Hybrid sliver covering adapter.**  Arbitrary-family quotient-circle Haar
growth converts direction mass and undilated-base section containment into a
fixed-radius angular outer-measure lower bound.

No countability, measurability, or positive-radius hypothesis is imposed on the
input family. -/
theorem angleOuter_ge_of_hybridSliverFamilyContainment
    {ι : Type*} {E : Set CoordinatePlane} {rho g : ℝ}
    {A : Set ProjectiveDirection} {x rad : ι → ℝ} {q : ℝ≥0∞}
    (hg : 1 ≤ g) (hrad : ∀ i, 0 ≤ rad i)
    (hcover : HybridSliverFamilyContainment A g x rad)
    (hmass : ENNReal.ofReal g * q ≤ volume A)
    (hbase : volume (⋃ i, quotientHybridCenteredArc Real.pi (x i) (rad i)) ≤
      angleOuter E rho) :
    q ≤ angleOuter E rho := by
  have hcovered : volume A ≤
      volume (⋃ i, quotientHybridCenteredDilate g Real.pi (x i) (rad i)) :=
    measure_mono hcover
  have hdilate := volume_iUnion_quotientHybridCenteredDilate_le
    g Real.pi hg x rad hrad
  have hmul : ENNReal.ofReal g * q ≤
      ENNReal.ofReal g * angleOuter E rho :=
    hmass.trans
      (hcovered.trans (hdilate.trans (mul_le_mul_right hbase _)))
  exact (ENNReal.mul_le_mul_iff_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
    ENNReal.ofReal_ne_top).mp hmul

end

end StarKakeyaLower
