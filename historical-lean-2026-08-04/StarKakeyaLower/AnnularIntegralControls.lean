import StarKakeyaLower.AnnularCaseIIntegral

/-!
# Negative controls and tightness tests for the annular radial integral (M6)

Regression guards for the two-active-segment certificate of
`StarKakeyaLower.AnnularCaseIIntegral`.  These are *not* production lemmas:
nothing in the production dependency closure imports this module; it is reached
only from `StarKakeyaLower.Audit`.

Three things are guarded.

1. **The strengthened logarithm tail is load bearing.**  The `π/56` route bounds
   the tail of the `log (1+x)` series by `2 z^7 / (1 - z^2)`, dropping the
   factor `1/(2k+7) ≤ 1/7`.  At the `2097/100000` target of the annular route
   that crude bound is *insufficient*: the certified sum falls strictly below
   `annILower`.  This is proved here, so the refinement cannot be silently
   reverted.

2. **The certificate is not over-claiming.**  The two retained segments really
   do integrate to about `0.0209709770`, so the next decimal step
   `2098/100000` is *not* provable from this certificate.  A regression that
   made the closing `norm_num` gate accept `0.02098` would therefore be caught.

3. **The frozen branch is hidden, strictly.**  `annFrozenRatio` is strictly
   below the large-angle branch already at the left endpoint `annA`, and the two
   rational cuts `annQL`, `annQR` genuinely straddle the single branch switch:
   the interior branch is below the large-angle branch at `annQL` and above it
   at `annQR`.  A three-piece cut in the style of `CaseIStrongIntegral`, which
   assumes the frozen branch is active on a middle segment, is therefore wrong
   for this tuple.
-/

open Set

namespace StarKakeyaLower

noncomputable section

/-- The exact rational value certified for the left (large-angle) segment. -/
def annLeftCertificate : ℝ :=
  (annQL ^ 2 - annA ^ 2) / 4 + annLeftC / annPiUpper - annCoeffQL / 4

/-- The exact rational value certified for the right (interior) segment. -/
def annRightCertificate : ℝ :=
  (-annR₀ ^ 2 / 2 + annR₀) - (-annQR ^ 2 / 2 + annQR) - annLogGeomUpper / 2

/-- The crude geometric tail `2 z^7 / (1 - z^2)` of the `π/56` route: the same
three explicit terms, but with the factor `1/7` dropped from every tail term. -/
def annLogGeomUpperCrude : ℝ :=
  2 * annLogZ + 2 * annLogZ ^ 3 / 3 + 2 * annLogZ ^ 5 / 5
    + 2 * annLogZ ^ 7 / (1 - annLogZ ^ 2)

/-- The right-segment value the crude tail would certify. -/
def annRightCertificateCrude : ℝ :=
  (-annR₀ ^ 2 / 2 + annR₀) - (-annQR ^ 2 / 2 + annQR) - annLogGeomUpperCrude / 2

/-- Positive control: with the strengthened tail the two retained segments do
clear the target. -/
theorem ann_certificate_sum_ge_target :
    annILower ≤ annLeftCertificate + annRightCertificate := by
  rw [annRightCertificate, annLogGeomUpper, annLogZ_eq, annLeftCertificate]
  norm_num [annILower, annLeftC, annCoeffA, annCoeffQL, annAtanLower6, annYQL,
    annPiUpper, annA, annQL, annR₀, annQR]

/-- **Negative control.**  With the crude `π/56` tail the very same two segments
fall strictly *below* the target: the `1/(2k+7) ≤ 1/7` refinement is load
bearing and may not be reverted. -/
theorem ann_crude_log_tail_negative_control :
    annLeftCertificate + annRightCertificateCrude < annILower := by
  rw [annRightCertificateCrude, annLogGeomUpperCrude, annLogZ_eq,
    annLeftCertificate]
  norm_num [annILower, annLeftC, annCoeffA, annCoeffQL, annAtanLower6, annYQL,
    annPiUpper, annA, annQL, annR₀, annQR]

/-- **Negative control.**  The certificate does not prove `0.02098`; the true
value of the two retained integrals is about `0.0209709770`. -/
theorem ann_target_2098_negative_control :
    ¬ ((2098 : ℝ) / 100000 ≤ annLeftCertificate + annRightCertificate) := by
  rw [annRightCertificate, annLogGeomUpper, annLogZ_eq, annLeftCertificate]
  norm_num [annLeftC, annCoeffA, annCoeffQL, annAtanLower6, annYQL,
    annPiUpper, annA, annQL, annR₀, annQR]

/-- **The frozen branch is hidden, strictly**, already at the left endpoint. -/
theorem ann_frozen_lt_large_at_annA : annFrozenRatio < annLargeAngleRatio annA := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * annA) := ann_largeAngle_den_pos annA
  have hlow : annAtanLower6 (2 * annA) ≤ Real.arctan (2 * annA) :=
    ann_atanLower6_le (by norm_num [annA]) (by norm_num [annA])
  have hgate : annPiUpper / 2 - annPiLower / annFrozenRatio <
      annAtanLower6 (2 * annA) := by
    norm_num [annPiUpper, annPiLower, annFrozenRatio, annRLambda, annAtanLower6,
      annA]
  have hpl := ann_pi_lower_lt
  have hpu := ann_pi_lt_upper
  have hfr : 0 < annFrozenRatio := annFrozenRatio_pos
  have h2 : annPiLower / annFrozenRatio ≤ Real.pi / annFrozenRatio := by
    rw [div_le_div_iff₀ hfr hfr]
    nlinarith
  have hstep : Real.pi / 2 - Real.pi / annFrozenRatio < Real.arctan (2 * annA) := by
    have h1 : Real.pi / 2 ≤ annPiUpper / 2 := by linarith
    linarith
  rw [annLargeAngleRatio, lt_div_iff₀ hden]
  have hpi : Real.pi / annFrozenRatio * annFrozenRatio = Real.pi := by field_simp
  nlinarith

/-- **The two rational cuts straddle the single branch switch.**  At `annQL` the
interior branch is still below the large-angle branch, at `annQR` it is already
above it; by monotonicity of `annH` the crossing is inside `(annQL, annQR)`, so
neither retained segment may be extended across the gap. -/
theorem ann_cuts_straddle_switch :
    annInteriorRatio annQL ≤ annLargeAngleRatio annQL ∧
      annLargeAngleRatio annQR ≤ annInteriorRatio annQR := by
  refine ⟨ann_interior_le_large_of_H (by norm_num [annQL]) (by norm_num [annQL])
    ann_H_annQL_nonpos,
    ann_large_le_interior_of_H (by norm_num [annQR]) (by norm_num [annQR])
      ann_H_annQR_nonneg⟩

end

end StarKakeyaLower
