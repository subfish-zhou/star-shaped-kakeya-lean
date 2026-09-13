import StarKakeyaLower.EndpointCapacityFinalAssembly64
import StarKakeyaLower.EndpointCapacityLowConcrete64
import StarKakeyaLower.EndpointCapacityHighConcrete64

/-!
# Unconditional N=64 endpoint-capacity lower bound

This module discharges the two concrete local payment inputs of the final
assembly with the frozen 127-row low schedule and the concrete uniform
high-tail certificate.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace StarKakeyaLower.Witness3527

/-- Universal lower bound at the exact minimum value certified by the frozen
four-term rational surrogate.  This is the headline theorem: the full rational
coefficient and the projective-direction factor `π` are both retained. -/
theorem universal_certifiedCoefficient_mul_pi :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (certifiedCoefficient * Real.pi) ≤
        volume.toOuterMeasure E := by
  apply final_certifiedCoefficient_mul_pi_of_concrete_local_bounds
  intro E K hheight
  exact ⟨certifiedCoefficient_mul_lowUnion_le_lintegral K,
    certifiedCoefficient_mul_tsum_highClass_le_lintegral K hheight⟩

/-- Strict rational corollary retained as a compact internal certificate. -/
theorem universal_three_five_two_seven_over_fifty_thousand :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (3527 / 50000 : ℝ) < volume.toOuterMeasure E := by
  apply final_3527_over_50000_of_concrete_local_bounds
  intro E K hheight
  exact ⟨common_mul_lowUnion_le_lintegral K,
    common_mul_tsum_highClass_le_lintegral K hheight⟩

/-- Non-strict presentation of the certified lower bound. -/
theorem universal_three_five_two_seven_over_fifty_thousand_le
    {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (3527 / 50000 : ℝ) ≤ volume.toOuterMeasure E :=
  (universal_three_five_two_seven_over_fifty_thousand E K).le

end StarKakeyaLower.Witness3527
