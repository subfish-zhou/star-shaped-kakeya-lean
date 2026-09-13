import StarKakeyaLower.CaseIEndpointR1Analytic
import StarKakeyaLower.Figure5EndpointEnvelopeCore

/-!
# The `100π/5599` instance of the clean endpoint interface

This is the *only* module in which the stronger witness tuple is turned into a
`Figure5EndpointDomain` and a `Figure5EndpointAnalyticPackage`.  It contains no
geometry: it just packages `StrongerKernel`, `CaseIEndpointAnalytic` and
`CaseIEndpointR1Analytic` into the two structures the generic endpoint chain
consumes.

It is deliberately placed *below* the historical facades
`Figure5EndpointEnvelope`, `Figure5LocalContact` and `UniversalEndpointClosure`,
so that those facades can mention `strongFigure5Domain` without creating an
import cycle with the CLEAN core modules.

A new parameter tuple gets a sibling of this module and of the facades; the
geometry itself is never duplicated.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

theorem strongR₁_pos_of_rational_lower : 0 < strongR₁ := by
  have h1 := strong_r₁_gt_rational_lower
  have h2 : (0 : ℝ) < strongR₁Lower := by norm_num [strongR₁Lower]
  linarith

/-- The frozen stronger tuple, as a clean endpoint domain. -/
def strongFigure5Domain : Figure5EndpointDomain where
  a := strongA
  r0 := strongR₀
  R1 := strongR₁
  g := strongPaperG
  a_pos := strongParameterDomain.a_pos
  a_le_r0 :=
    (strongParameterDomain.a_lt_rLambda.trans
      strongParameterDomain.rLambda_lt_r₀).le
  r0_lt_half := strongParameterDomain.r₀_lt_half
  R1_pos := strongR₁_pos_of_rational_lower

@[simp] theorem strongFigure5Domain_a : strongFigure5Domain.a = strongA := rfl

@[simp] theorem strongFigure5Domain_r0 : strongFigure5Domain.r0 = strongR₀ := rfl

@[simp] theorem strongFigure5Domain_R1 : strongFigure5Domain.R1 = strongR₁ := rfl

@[simp] theorem strongFigure5Domain_g (r : ℝ) :
    strongFigure5Domain.g r = strongPaperG r := rfl

/-- The analytic package of the frozen tuple.  Its base-ray gate is exactly
`base_ray_frozen_analytic` followed by `strongFrozenRatio_le_paperG`. -/
theorem strongFigure5AnalyticPackage :
    Figure5EndpointAnalyticPackage strongFigure5Domain :=
  Figure5EndpointAnalyticPackage.of_dominations
    (fun {r} hr => by
      have _ : r ∈ Icc strongA strongR₀ := hr
      exact strongInteriorRatio_le_paperG r)
    (fun {r} hr => by
      have _ : r ∈ Icc strongA strongR₀ := hr
      exact strongLargeAngleRatio_le_paperG r)
    (fun {r t α} hr ht0 htop hhalf hαtop hsint hR1 hheight => by
      have hr' : r ∈ Icc strongA strongR₀ := hr
      have hgap := base_ray_frozen_analytic hr' ht0 htop hhalf hαtop hsint hR1
        hheight
      exact hgap.trans_le
        (mul_le_mul_of_nonneg_right (strongFrozenRatio_le_paperG r) ht0.le))

end

end StarKakeyaLower
