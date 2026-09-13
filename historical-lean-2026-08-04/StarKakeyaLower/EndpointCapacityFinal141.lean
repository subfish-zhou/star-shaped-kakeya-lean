import StarKakeyaLower.EndpointCapacityFinalAssembly
import StarKakeyaLower.EndpointCapacityLowConcrete
import StarKakeyaLower.EndpointCapacityHighConcrete

/-!
# Unconditional `141/2000` endpoint-capacity lower bound

This module discharges the two concrete local payment inputs of the final
assembly with the frozen 63-row low schedule and the concrete uniform high-tail
certificate.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace StarKakeyaLower.Witness141

/-- Unconditional universal lower bound certified by the frozen 32-class
endpoint-capacity schedule. -/
theorem universal_one_forty_one_over_two_thousand :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (141 / 2000 : ℝ) < volume.toOuterMeasure E := by
  apply final_141_over_2000_of_concrete_local_bounds
  intro E K hheight
  exact ⟨common_mul_lowUnion_le_lintegral K,
    common_mul_tsum_highClass_le_lintegral K hheight⟩

/-- Non-strict presentation of the certified lower bound. -/
theorem universal_one_forty_one_over_two_thousand_le
    {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (141 / 2000 : ℝ) ≤ volume.toOuterMeasure E :=
  (universal_one_forty_one_over_two_thousand E K).le

end StarKakeyaLower.Witness141
