import StarKakeyaLower.AnnularKernel
import StarKakeyaLower.AnnularGeometry

/-!
# Analytic gates of the joint inner/outer annular certificate

This module discharges the *paper-facing* numeric gates of
`spikes/001-joint-inner-outer/PROOF.md` Hypothesis C that do not involve the
radial integral:

* **(C1)** `T < h₀ / (2π)` — the high-triangle branch;
* **(C3)** `T < C_ext / 4` — the exterior payment branch, with the exterior
  divisor written **literally as `/ 4`**, exactly as it occurs in the `min`
  coefficient of `annular_exterior_greedy_lower_bound`;
* **(C4)** `T < (ρ² - r₀²) / 2` — the fan branch;

together with `0 < C_ext`, the combined `min` coefficient gate, and every
numeric domain hypothesis of the M4 exterior interface.

**Not proved here:** gate (C2), the raw radial integral `I > T`, and the
endpoint containment geometry.  Those are separate obligations and no statement
below presupposes them.

The only transcendental input is `Real.pi_lt_d20` together with the elementary
cubic lower bound for `sin`, which is reproved locally
(`sin_ge_sub_cube_div_six`) rather than imported from the frozen
`CaseIIAnalytic`: this module's import closure contains no module carrying the
frozen witness constants.  Every comparison is kernel-checked; no decimal
evaluation and no `native_decide` occurs.

`spikes/001-joint-inner-outer/certify.py` computes the same gates with
outward-rounded Arb intervals.  Those intervals are **outward evidence only**
and are not used by any proof below.
-/

namespace StarKakeyaLower

noncomputable section

/-! ## A local, generic cubic lower bound for `sin`

This is the standard `x - x³/6 ≤ sin x` estimate for `0 ≤ x`.  It is stated
generically and reproved here so that the annular route does not import the
frozen-tuple module in which the same estimate happens to live. -/

/-- **Generic cubic lower bound for the sine.**  For every `0 ≤ x`,
`x - x ^ 3 / 6 ≤ sin x`. -/
theorem sin_ge_sub_cube_div_six {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  set g : ℝ → ℝ := fun y => Real.sin y - y + y ^ 3 / 6 with hg
  set g' : ℝ → ℝ := fun y => Real.cos y - 1 + y ^ 2 / 2 with hg'
  have hgderiv : ∀ y, HasDerivAt g (g' y) y := by
    intro y
    simp only [hg, hg']
    convert ((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 6) using 1
    simp [id_eq]
    ring
  have hgmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      ((Real.continuous_sin.sub continuous_id).add
        ((continuous_id.pow 3).div_const 6)).continuousOn
    · intro y _
      exact (hgderiv y).hasDerivWithinAt
    · intro y _
      simp only [hg']
      linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have h := hgmono (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show x ∈ Set.Ici 0 by simpa) hx
  have hzero : g 0 = 0 := by simp [hg]
  rw [hzero] at h
  simp only [hg] at h
  nlinarith

/-! ## The arcsine gate -/

/-- Rational upper bound for the escaping-weight argument `h₀ / (m ρ)`,
obtained from the rational lower bound `annRhoLower` for `ρ`. -/
def annArcsinArgUpper : ℝ := 1949945 / 10000000

/-- Rational upper bound for the escaping weight `H(h₀) = arcsin (h₀ / (m ρ))`. -/
def annArcsinUpper : ℝ := 196255 / 1000000

theorem ann_arcsin_arg_lt_upper :
    annA / (annM * annRho) < annArcsinArgUpper := by
  have hrho := ann_rho_lower
  have hm := annM_pos
  rw [div_lt_iff₀ annM_mul_annRho_pos]
  have hstep : annArcsinArgUpper * (annM * annRhoLower) ≤
      annArcsinArgUpper * (annM * annRho) := by
    have := mul_le_mul_of_nonneg_left hrho.le hm.le
    exact mul_le_mul_of_nonneg_left this (by norm_num [annArcsinArgUpper])
  refine lt_of_lt_of_le ?_ hstep
  norm_num [annA, annArcsinArgUpper, annM, annEps, annRhoLower]

/-- **The escaping weight is below its stored rational bound.**  The proof is a
sine-cubic comparison: `annArcsinArgUpper < U - U³/6 ≤ sin U`, so
`arcsin (h₀ / (m ρ)) < U`.  No decimal evaluation of `arcsin` occurs. -/
theorem ann_arcsin_lt_upper :
    Real.arcsin (annA / (annM * annRho)) < annArcsinUpper := by
  have hU0 : 0 < annArcsinUpper := by norm_num [annArcsinUpper]
  have hcubic : annArcsinArgUpper < annArcsinUpper - annArcsinUpper ^ 3 / 6 := by
    norm_num [annArcsinArgUpper, annArcsinUpper]
  have hsin : annArcsinArgUpper < Real.sin annArcsinUpper :=
    hcubic.trans_le (sin_ge_sub_cube_div_six hU0.le)
  refine (Real.arcsin_lt_iff_lt_sin' ?_).2
    (ann_arcsin_arg_lt_upper.trans hsin)
  exact ⟨by linarith [Real.pi_pos, hU0], by
    have := Real.pi_gt_three
    rw [annArcsinUpper]
    linarith⟩

theorem ann_arcsin_pos : 0 < Real.arcsin (annA / (annM * annRho)) :=
  Real.arcsin_pos.2 ann_arg_m_rho_pos

/-! ## `PROOF.md` Hypothesis C, gate (C1) -/

/-- **Gate (C1)** of `PROOF.md` Hypothesis C: the high-triangle branch already
beats the target.  The only transcendental input is `Real.pi_lt_d20`. -/
theorem ann_gate_C1 : annTarget < annA / (2 * Real.pi) := by
  have hpi := Real.pi_lt_d20
  have hpi0 := Real.pi_pos
  rw [lt_div_iff₀ (by positivity)]
  rw [annTarget, annA]
  norm_num at hpi ⊢
  linarith

/-! ## `PROOF.md` Hypothesis C, gates (C3) and (C4) -/

/-- Rational lower bound for the exterior payment coefficient `C_ext`. -/
theorem ann_cExt_lower :
    annA / (2 * annArcsinUpper) - annM * annR₀ ^ 2 / 2 <
      annularCExt annA annR₀ annRho annM := by
  have hasin := ann_arcsin_lt_upper
  have hasin0 := ann_arcsin_pos
  have hU0 : (0 : ℝ) < annArcsinUpper := by norm_num [annArcsinUpper]
  have hquot : annA / (2 * annArcsinUpper) <
      annA / (2 * Real.arcsin (annA / (annM * annRho))) :=
    (div_lt_div_iff_of_pos_left annA_pos (by positivity) (by positivity)).2
      (by linarith)
  simp only [annularCExt]
  linarith

/-- **Gate (C3)** of `PROOF.md` Hypothesis C, with the exterior divisor written
literally as `/ 4`: the exterior payment rate beats the target. -/
theorem ann_gate_C3 : annTarget < annularCExt annA annR₀ annRho annM / 4 := by
  have hlow := ann_cExt_lower
  have hrat : annTarget <
      (annA / (2 * annArcsinUpper) - annM * annR₀ ^ 2 / 2) / 4 := by
    norm_num [annTarget, annA, annArcsinUpper, annM, annEps, annR₀]
  linarith

/-- `C_ext > 0`, the non-degeneracy input of the M3a/M3b/M4 coefficient
extraction.  It follows from (C3) because the target is positive. -/
theorem ann_cExt_pos : 0 < annularCExt annA annR₀ annRho annM := by
  have h := ann_gate_C3
  have := annTarget_pos
  linarith

/-- **Gate (C4)** of `PROOF.md` Hypothesis C: the fan coefficient beats the
target. -/
theorem ann_gate_C4 : annTarget < (annRho ^ 2 - annR₀ ^ 2) / 2 := by
  have hrho := ann_rho_lower
  have hrho0 : (0 : ℝ) < annRhoLower := by norm_num [annRhoLower]
  have hsq : annRhoLower ^ 2 < annRho ^ 2 := by nlinarith
  have hrat : annTarget < (annRhoLower ^ 2 - annR₀ ^ 2) / 2 := by
    norm_num [annTarget, annRhoLower, annR₀]
  linarith

/-- The **combined exterior coefficient** produced by the M4 exit theorem
`annular_exterior_greedy_lower_bound` — the literal
`min (C_ext / 4) ((ρ² - r₀²) / 2)` — strictly exceeds the target. -/
theorem ann_gate_min_exterior :
    annTarget <
      min (annularCExt annA annR₀ annRho annM / 4) ((annRho ^ 2 - annR₀ ^ 2) / 2) :=
  lt_min ann_gate_C3 ann_gate_C4

/-! ## The numeric domain of the M4 exterior interface

`annular_exterior_greedy_lower_bound` and
`annular_exterior_A_out_greedy_lower_bound` (`AnnularGreedyInfinite.lean`) take
their parameters in the shape `eps`, `a`, `r0`, `R₁` with `rho = R₁ - 1` and
`m = 1 - eps`.  The following statements are exactly those hypotheses at the
production tuple. -/

theorem ann_m4_r₀_lt_rho : annR₀ < annR₁ - 1 := annR₀_lt_annRho

theorem ann_m4_a_lt_scaled_rho : annA < (1 - annEps) * (annR₁ - 1) :=
  annA_lt_annM_mul_annRho

theorem ann_m4_cExt_pos : 0 < annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) :=
  ann_cExt_pos

/-- **All numeric hypotheses of the M4 exterior interface at the production
tuple**, in the literal `eps / a / r₀ / R₁` shape that
`annular_exterior_A_out_greedy_lower_bound` expects. -/
theorem ann_m4_exterior_domain :
    0 < annEps ∧ annEps < 1 ∧ 0 < annA ∧ 0 < annR₀ ∧ annR₀ < annR₁ - 1 ∧
      annA < (1 - annEps) * (annR₁ - 1) ∧
      0 < annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) :=
  ⟨annEps_pos, annEps_lt_one, annA_pos, annR₀_pos, ann_m4_r₀_lt_rho,
    ann_m4_a_lt_scaled_rho, ann_m4_cExt_pos⟩

/-- The M4 exterior coefficient at the production tuple, in the literal shape of
the M4 conclusion, strictly exceeds the target. -/
theorem ann_m4_coefficient_gt_target :
    annTarget <
      min (annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) / 4)
        (((annR₁ - 1) ^ 2 - annR₀ ^ 2) / 2) :=
  ann_gate_min_exterior

end

end StarKakeyaLower
