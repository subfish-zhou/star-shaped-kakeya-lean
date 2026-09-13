import StarKakeyaLower.EndpointCapacityHighAggregate64

open Set MeasureTheory Real Function
open scoped ENNReal Topology BigOperators Interval

namespace StarKakeyaLower.Witness3527

noncomputable section

/-- The concrete measurable subinterval used for every high ledger. -/
def concreteHighJ (k : ℕ) : Set ℝ := Icc (highB k) (highOuterRadius k)

@[simp] theorem concreteHighJ_measurable (k : ℕ) :
    MeasurableSet (concreteHighJ k) := by
  simp [concreteHighJ]

theorem highOuterRadius_shifted_lower (k : ℕ) :
    highRadiusLower + (k : ℝ) / 2 ≤ highOuterRadius k := by
  let x : ℝ := (k : ℝ) / 2
  have hx : 0 ≤ x := by positivity
  have hinner : 0 ≤ highA k ^ 2 - eta ^ 2 := by
    rw [show highA k = eta + x by rfl]
    nlinarith [eta_pos]
  have hsqrt : x ≤ Real.sqrt (highA k ^ 2 - eta ^ 2) := by
    rw [Real.le_sqrt hx hinner]
    rw [show highA k = eta + x by rfl]
    nlinarith [eta_pos]
  have hshift : 0 ≤ highRadiusLower + x := by
    dsimp [highRadiusLower]
    positivity
  rw [highOuterRadius, Real.le_sqrt hshift (by positivity)]
  have hbase := highRadiusLower_sq_lt_one_add_eta_sq
  have hcoef : highRadiusLower < eta + 1 := by
    norm_num [highRadiusLower, eta]
  have hcoefx : highRadiusLower * x ≤ (eta + 1) * x :=
    mul_le_mul_of_nonneg_right hcoef.le hx
  have hsqbound : (highRadiusLower + x) ^ 2 ≤
      (eta + x) ^ 2 + 1 + 2 * x := by
    nlinarith
  have hsqrt' : x ≤ Real.sqrt ((eta + x) ^ 2 - eta ^ 2) := by
    simpa [show highA k = eta + x by rfl] using hsqrt
  have hrootbound : (eta + x) ^ 2 + 1 + 2 * x ≤
      (eta + x) ^ 2 + 1 + 2 * Real.sqrt ((eta + x) ^ 2 - eta ^ 2) := by
    nlinarith
  rw [show highA k = eta + x by rfl]
  exact hsqbound.trans hrootbound

/-- Uniform width supplied by the `R_k/B_k` geometry. -/
theorem highWidthLower_le_width (k : ℕ) :
    highWidthLower ≤ highOuterRadius k - highB k := by
  have hR := highOuterRadius_shifted_lower k
  unfold highWidthLower highB highA
  linarith

@[simp] theorem highWidthLower_pos : 0 < highWidthLower := by
  norm_num [highWidthLower, highRadiusLower, highB, highA, eta]

@[simp] theorem highFactorLower_pos : 0 < highFactorLower := by
  norm_num [highFactorLower, eta]

/-- On the whole chosen subinterval, the rational factor in the kernel has the
frozen uniform lower bound. -/
theorem highFactorLower_le_ratio (k : ℕ) {u : ℝ}
    (hu : u ∈ concreteHighJ k) :
    highFactorLower ≤ u / (highOuterRadius k + u) := by
  have hx : 0 ≤ (k : ℝ) / 2 := by positivity
  have hB0 : 0 < highB k := by
    unfold highB
    linarith [highA_pos k]
  have hnext0 : 0 < highB (k + 1) := by
    unfold highB
    linarith [highA_pos (k + 1)]
  have hu0 : 0 < u := hB0.trans_le hu.1
  have hR0 : 0 < highOuterRadius k := (highB_lt_highOuterRadius k).trans' hB0
  have hden0 : 0 < highOuterRadius k + u := by positivity
  have hD0 : 0 < highB (k + 1) + highB k := by positivity
  have hfr : highFactorLower ≤ highB k / (highB (k + 1) + highB k) := by
    unfold highFactorLower
    apply (div_le_div_iff₀ (by norm_num [eta]) hD0).2
    unfold highB highA
    push_cast
    nlinarith [eta_pos]
  have hprod : highB k * highOuterRadius k ≤ u * highB (k + 1) := by
    calc
      highB k * highOuterRadius k ≤ highB k * highB (k + 1) :=
        mul_le_mul_of_nonneg_left (highOuterRadius_lt_next_highB k).le hB0.le
      _ ≤ u * highB (k + 1) :=
        mul_le_mul_of_nonneg_right hu.1 hnext0.le
  have hrat : highB k / (highB (k + 1) + highB k) ≤
      u / (highOuterRadius k + u) := by
    rw [div_le_div_iff₀ hD0 hden0]
    nlinarith
  exact hfr.trans hrat

/-- Pointwise kernel lower bound on the measurable interval `J_k`. -/
theorem concreteHighJ_kernel_lower (k : ℕ) {u : ℝ}
    (hu : u ∈ concreteHighJ k) :
    ENNReal.ofReal (highFactorLower * (highOuterRadius k - u)) ≤
      ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) := by
  apply ENNReal.ofReal_le_ofReal
  have hdiff : 0 ≤ highOuterRadius k - u := sub_nonneg.mpr hu.2
  have hratio := highFactorLower_le_ratio k hu
  unfold endpointWindowKernel
  have hden : highOuterRadius k + u ≠ 0 := by
    have : 0 < highOuterRadius k + u := by
      have hB0 : 0 < highB k := by
        unfold highB
        linarith [highA_pos k]
      have hu0 : 0 < u := hB0.trans_le hu.1
      have hR0 : 0 < highOuterRadius k := (highB_lt_highOuterRadius k).trans'
        (by unfold highB; linarith [highA_pos k])
      positivity
    exact ne_of_gt this
  rw [show u * (highOuterRadius k - u) / (highOuterRadius k + u) =
      (u / (highOuterRadius k + u)) * (highOuterRadius k - u) by
    field_simp]
  exact mul_le_mul_of_nonneg_right hratio hdiff

/-- Exact size/payment of the affine lower kernel on `J_k`. -/
theorem concreteHighJ_affine_payment (k : ℕ) :
    ENNReal.ofReal
        (highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2) =
      ∫⁻ u in concreteHighJ k,
        ENNReal.ofReal (highFactorLower * (highOuterRadius k - u)) := by
  let f : ℝ → ℝ := fun u => highFactorLower * (highOuterRadius k - u)
  have hBR : highB k ≤ highOuterRadius k := (highB_lt_highOuterRadius k).le
  have hfi : IntegrableOn f (concreteHighJ k) := by
    apply Continuous.integrableOn_Icc
    dsimp [f]
    fun_prop
  have hnn : 0 ≤ᶠ[ae (volume.restrict (concreteHighJ k))] f := by
    filter_upwards [ae_restrict_mem (concreteHighJ_measurable k)] with u hu
    dsimp [f]
    exact mul_nonneg highFactorLower_pos.le (sub_nonneg.mpr hu.2)
  change ENNReal.ofReal
      (highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2) =
    ∫⁻ u in concreteHighJ k, ENNReal.ofReal (f u)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn]
  congr 1
  rw [concreteHighJ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hBR]
  dsimp [f]
  symm
  calc
    (∫ u in highB k..highOuterRadius k,
        highFactorLower * (highOuterRadius k - u)) =
      highFactorLower *
        (∫ u in highB k..highOuterRadius k, (highOuterRadius k - u)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2 := by
      have hint : (∫ u in highB k..highOuterRadius k,
          (highOuterRadius k - u)) =
          (highOuterRadius k - highB k) ^ 2 / 2 := by
        calc
          (∫ u in highB k..highOuterRadius k, (highOuterRadius k - u)) =
              (∫ _u in highB k..highOuterRadius k, highOuterRadius k) -
              (∫ u in highB k..highOuterRadius k, u) := by
                exact intervalIntegral.integral_sub
                  (continuous_const.intervalIntegrable _ _)
                  (continuous_id.intervalIntegrable _ _)
          _ = (highOuterRadius k - highB k) ^ 2 / 2 := by
            rw [intervalIntegral.integral_const, integral_id]
            ring
      rw [hint]
      ring

/-- Frozen constants imply that the affine payment on every chosen interval is
at least the common coefficient. -/
theorem concreteHighJ_size (k : ℕ) :
    ENNReal.ofReal common ≤
      ENNReal.ofReal
        (highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2) := by
  apply ENNReal.ofReal_le_ofReal
  have hw := highWidthLower_le_width k
  have hw0 : 0 ≤ highWidthLower := highWidthLower_pos.le
  have hW0 : 0 ≤ highOuterRadius k - highB k :=
    sub_nonneg.mpr (highB_lt_highOuterRadius k).le
  have hsq : highWidthLower ^ 2 ≤ (highOuterRadius k - highB k) ^ 2 :=
    (sq_le_sq₀ hw0 hW0).2 hw
  have hp : highPaymentLower ≤
      highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2 := by
    unfold highPaymentLower
    nlinarith [highFactorLower_pos]
  exact common_lt_highPaymentLower.le.trans hp

/-- Concrete uniform high-payment certificate with coefficient
`ENNReal.ofReal common`. -/
theorem concrete_uniformHighPaymentCertificate :
    UniformHighPaymentCertificate (ENNReal.ofReal common) := by
  intro k
  calc
    ENNReal.ofReal common ≤
        ENNReal.ofReal
          (highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2) :=
      concreteHighJ_size k
    _ = ∫⁻ u in concreteHighJ k,
          ENNReal.ofReal (highFactorLower * (highOuterRadius k - u)) :=
      concreteHighJ_affine_payment k
    _ ≤ ∫⁻ u in concreteHighJ k,
          ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (concreteHighJ_measurable k)] with u hu
      exact concreteHighJ_kernel_lower k hu
    _ = ∫⁻ u in highLedger k,
          ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) := by
      rfl

/-- Concrete high local-integral bound used by the final one-payment assembly. -/
theorem common_mul_tsum_highClass_le_lintegral
    {E : Set Plane} (K : StarShapedKakeya E)
    (hheight : ∀ d, (universalPositiveNeedle K d).height < eta) :
    ENNReal.ofReal common * ∑' k, volume (highClass K k) ≤
      ∫⁻ u in ⋃ k, highLedger k,
        ENNReal.ofReal u *
          (radialSuperlevelOuter
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim u := by
  apply highTail_countable_aggregate K (ENNReal.ofReal common)
  intro k
  exact highLocalPayment_of_certificate K hheight
    concrete_uniformHighPaymentCertificate k

/-- Concrete countable high-tail outer-measure corollary. -/
theorem common_mul_tsum_highClass_le_selectedTriangleOuter
    {E : Set Plane} (K : StarShapedKakeya E)
    (hheight : ∀ d, (universalPositiveNeedle K d).height < eta) :
    ENNReal.ofReal common * ∑' k, volume (highClass K k) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
  apply highTail_aggregate_le_selectedTriangleOuter K (ENNReal.ofReal common)
  intro k
  exact highLocalPayment_of_certificate K hheight
    concrete_uniformHighPaymentCertificate k

/-- High-tail size at the exact minimum rational low-surrogate coefficient. -/
theorem certifiedCoefficient_concreteHighJ_size (k : ℕ) :
    ENNReal.ofReal certifiedCoefficient ≤
      ENNReal.ofReal
        (highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2) := by
  apply ENNReal.ofReal_le_ofReal
  have hw := highWidthLower_le_width k
  have hsq : highWidthLower ^ 2 ≤ (highOuterRadius k - highB k) ^ 2 :=
    (sq_le_sq₀ highWidthLower_pos.le
      (sub_nonneg.mpr (highB_lt_highOuterRadius k).le)).2 hw
  have hp : highPaymentLower ≤
      highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2 := by
    unfold highPaymentLower
    nlinarith [highFactorLower_pos]
  exact certifiedCoefficient_le_highPaymentLower.trans hp

theorem certifiedCoefficient_uniformHighPaymentCertificate :
    UniformHighPaymentCertificate (ENNReal.ofReal certifiedCoefficient) := by
  intro k
  calc
    ENNReal.ofReal certifiedCoefficient ≤
        ENNReal.ofReal
          (highFactorLower * (highOuterRadius k - highB k) ^ 2 / 2) :=
      certifiedCoefficient_concreteHighJ_size k
    _ = ∫⁻ u in concreteHighJ k,
          ENNReal.ofReal (highFactorLower * (highOuterRadius k - u)) :=
      concreteHighJ_affine_payment k
    _ ≤ ∫⁻ u in concreteHighJ k,
          ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (concreteHighJ_measurable k)] with u hu
      exact concreteHighJ_kernel_lower k hu
    _ = ∫⁻ u in highLedger k,
          ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) := by
      rfl

theorem certifiedCoefficient_mul_tsum_highClass_le_lintegral
    {E : Set Plane} (K : StarShapedKakeya E)
    (hheight : ∀ d, (universalPositiveNeedle K d).height < eta) :
    ENNReal.ofReal certifiedCoefficient * ∑' k, volume (highClass K k) ≤
      ∫⁻ u in ⋃ k, highLedger k,
        ENNReal.ofReal u *
          (radialSuperlevelOuter
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim u := by
  apply highTail_countable_aggregate K (ENNReal.ofReal certifiedCoefficient)
  intro k
  exact highLocalPayment_of_certificate K hheight
    certifiedCoefficient_uniformHighPaymentCertificate k

end
end StarKakeyaLower.Witness3527
