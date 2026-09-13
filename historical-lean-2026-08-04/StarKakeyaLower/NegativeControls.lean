import StarKakeyaLower.CaseIEndpointAnalytic

/-!
# Negative controls

Regression guards for endpoint arguments that look plausible but are false.
These are *not* production lemmas: nothing in the production dependency closure
of `universal_strong_lower_bound` may import this module.  It is reached only
from `StarKakeyaLower.Audit`.

The control kept here rules out closing the Case-I exterior branch by the naive
"arcsine dispatch": taking the projective envelope `S = arcsin (R₁ sin t)` and
discharging the gap with either the frozen ratio or the large-angle fallback.
At `r = strongA` and `t = π/4` the arcsine saturates, so `S = π/2`, while all
three branches of `strongPaperG strongA` stay below three; hence neither
alternative holds.  The angle is geometrically realizable by a unit chord
outside `B strongA` with endpoint norms below `strongR₁`, so no change of the
signed-height convention or of the angular lifts can remove the obstruction.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- All three branches of the paper's `g` stay below three at `r = strongA`. -/
theorem strongPaperG_strongA_lt_three : strongPaperG strongA < 3 := by
  rw [strongPaperG, max_lt_iff, max_lt_iff]
  constructor
  · norm_num [strongInteriorRatio, strongA]
  constructor
  · norm_num [strongFrozenRatio, strongRLambda]
  · rw [strongLargeAngleRatio]
    have hat : Real.arctan (2 * strongA) < Real.pi / 6 := by
      have hself : Real.arctan (2 * strongA) < 2 * strongA :=
        arctan_lt_self_of_pos (by norm_num [strongA])
      have hpilo : (3 : ℝ) < Real.pi := Real.pi_gt_three
      norm_num [strongA] at hself ⊢
      linarith
    have hden : 0 < Real.pi / 2 - Real.arctan (2 * strongA) := by
      linarith [Real.pi_pos]
    rw [div_lt_iff₀ hden]
    linarith [Real.pi_pos]

/-- The arcsine argument saturates at `t = π/4`. -/
theorem one_le_strongR₁_mul_sin_pi_div_four :
    1 ≤ strongR₁ * Real.sin (Real.pi / 4) := by
  rw [Real.sin_pi_div_four]
  have hR := strongParameterDomain.r₁_gt_rational_lower
  have hsqrt : (7 / 5 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  norm_num [strongR₁Lower] at hR ⊢
  nlinarith

/-- Exact scalar counterexample to the exterior arcsine dispatch. -/
theorem exterior_arcsin_dispatch_counterexample :
    let t := Real.pi / 4
    let S := Real.arcsin (strongR₁ * Real.sin t)
    ¬ (Real.pi ≤ strongPaperG strongA * t ∨
      2 * S - t < strongFrozenRatio * t) := by
  dsimp
  rw [Real.arcsin_eq_pi_div_two.mpr one_le_strongR₁_mul_sin_pi_div_four]
  have hg := strongPaperG_strongA_lt_three
  have hf : strongFrozenRatio < 3 := by
    norm_num [strongFrozenRatio, strongRLambda]
  intro h
  rcases h with hsat | hgap
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

end

end StarKakeyaLower
