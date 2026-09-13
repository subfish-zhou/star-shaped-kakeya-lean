import StarKakeyaLower.EndpointCapacityHighLedger
import StarKakeyaLower.EndpointCapacityLeftLimit
import StarKakeyaLower.EndpointCapacityPayment

/-! A compiled POC for aggregation of the infinite high tail. -/

open Set MeasureTheory Real Function
open scoped ENNReal Topology BigOperators

namespace StarKakeyaLower.Witness141

noncomputable section

/-- The half-open high nearest-radius classes are genuinely pairwise disjoint. -/
theorem highClasses_pairwise_disjoint {E : Set Plane} (K : StarShapedKakeya E) :
    Pairwise (fun k l : ℕ => Disjoint (highClass K k) (highClass K l)) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · rw [highClass, highClass]
    apply endpointCapacityBandClass_disjoint K
    · have hc : ((k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h
      unfold highB highA
      norm_num at hc ⊢
      linarith
    · unfold highB
      linarith [highA_pos k]
  · apply Disjoint.symm
    rw [highClass, highClass]
    apply endpointCapacityBandClass_disjoint K
    · have hc : ((l + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      unfold highB highA
      norm_num at hc ⊢
      linarith
    · unfold highB
      linarith [highA_pos l]

/-- Every squared nearest radius above `eta²` belongs to one of the half-unit
high classes.  This statement is independent of the height hypothesis; in the
`no-high-height` branch that hypothesis is used only for ledger eligibility. -/
theorem highClasses_cover_nearestSq_gt_eta_sq
    {E : Set Plane} (K : StarShapedKakeya E) :
    {d | eta ^ 2 < (universalPositiveNeedle K d).nearestRadiusSq} ⊆
      ⋃ k : ℕ, highClass K k := by
  intro d hd
  let x := (universalPositiveNeedle K d).nearestRadiusSq
  have hx0 : 0 ≤ x := (universalPositiveNeedle K d).nearestRadiusSq_nonneg
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.sqrt x)
  have hsqrt : Real.sqrt x < (n : ℝ) / 2 := by nlinarith
  have hBn0 : 0 ≤ highB n := by
    unfold highB
    exact (highA_pos n).le.trans (by linarith)
  have hex : ∃ n : ℕ, x ≤ highB n ^ 2 := by
    refine ⟨n, ?_⟩
    rw [← Real.sq_sqrt hx0]
    have : Real.sqrt x ≤ highB n := by
      unfold highB highA
      nlinarith [eta_pos]
    nlinarith [Real.sqrt_nonneg x]
  let n := Nat.find hex
  have hnupper : x ≤ highB n ^ 2 := Nat.find_spec hex
  have hnlower : highA n ^ 2 < x := by
    by_cases hn0 : n = 0
    · simpa [hn0, highA] using hd
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hnot : ¬ x ≤ highB m ^ 2 :=
        Nat.find_min hex (by simp [n, hm])
      have heq : highA (m + 1) = highB m := by
        simp [highA, highB, Nat.cast_add]
        ring
      rw [hm, heq]
      exact lt_of_not_ge hnot
  exact mem_iUnion.2 ⟨n, hnlower, hnupper⟩

private def selectedQ {E : Set Plane} (K : StarShapedKakeya E) : ℝ → ℝ≥0∞ :=
  radialSuperlevelOuter
    (directionTriangleUnion (universalPositiveNeedle K) Set.univ)

/-- At every point of ledger `k`, fixed-window gives exactly the integrand
needed by the high-tail accounting. -/
theorem highClass_ledger_integrand
    {E : Set Plane} (K : StarShapedKakeya E)
    (hheight : ∀ d, (universalPositiveNeedle K d).height < eta)
    (k : ℕ) {u : ℝ} (hu : u ∈ highLedger k)
    (huR : u < highOuterRadius k) :
    ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) *
        volume (highClass K k) ≤
      ENNReal.ofReal u * (selectedQ K).leftLim u := by
  have hu0 : 0 < u := (highA_pos k).trans
    (lt_of_lt_of_le (by unfold highB; linarith) hu.1)
  have hsub : volume (highClass K k) ≤
      volume (endpointCapacityWindowDirections K u (highOuterRadius k)) :=
    measure_mono (highClass_subset_windowDirections K hheight k hu)
  have hw := K.endpointCapacity_fixedWindow_leftLim u (highOuterRadius k) hu0 huR
  have hratio : 0 ≤ (highOuterRadius k - u) / (highOuterRadius k + u) := by
    have hden : 0 ≤ highOuterRadius k + u := by linarith
    exact div_nonneg (sub_nonneg.mpr huR.le) hden
  have hker : endpointWindowKernel (highOuterRadius k) u =
      u * ((highOuterRadius k - u) / (highOuterRadius k + u)) := by
    unfold endpointWindowKernel
    ring
  calc
    ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) *
        volume (highClass K k) =
      ENNReal.ofReal u *
        (ENNReal.ofReal ((highOuterRadius k - u) /
          (highOuterRadius k + u)) * volume (highClass K k)) := by
            rw [hker, ENNReal.ofReal_mul hu0.le]
            ring
    _ ≤ ENNReal.ofReal u *
        (ENNReal.ofReal ((highOuterRadius k - u) /
          (highOuterRadius k + u)) *
            volume (endpointCapacityWindowDirections K u (highOuterRadius k))) := by
          exact mul_le_mul_right (mul_le_mul_right hsub _) _
    _ ≤ ENNReal.ofReal u * (selectedQ K).leftLim u :=
      mul_le_mul_right hw _

/-- A uniform payment certificate: each disjoint ledger pays the same constant.
This is deliberately phrased in terms of the exact kernel, so either the closed
form `endpointWindowPayment` or a cruder pointwise estimate can discharge it. -/
def UniformHighPaymentCertificate (c : ℝ≥0∞) : Prop :=
  ∀ k : ℕ,
    c ≤ ∫⁻ u in highLedger k,
      ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u)

/-- Crude certificate constructor: it is enough to lower-bound the kernel by
`c / volume(Icc)` on any measurable subinterval of every ledger.  The
multiplication form avoids division and remains valid in `ℝ≥0∞`. -/
theorem uniformHighPaymentCertificate_of_crude
    {c a : ℝ≥0∞}
    (J : ℕ → Set ℝ) (hJm : ∀ k, MeasurableSet (J k))
    (hJ : ∀ k, J k ⊆ highLedger k)
    (hsize : ∀ k, c ≤ a * volume (J k))
    (hkernel : ∀ k u, u ∈ J k →
      a ≤ ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u)) :
    UniformHighPaymentCertificate c := by
  intro k
  calc
    c ≤ a * volume (J k) := hsize k
    _ = ∫⁻ _u in J k, a := (setLIntegral_const (J k) a).symm
    _ ≤ ∫⁻ u in J k,
        ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hJm k)] with u hu
      exact hkernel k u hu
    _ ≤ ∫⁻ u in highLedger k,
        ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) :=
      lintegral_mono_set (hJ k)

/-- A payment certificate plus the fixed-window estimate supplies the local
hypothesis used by countable aggregation.  At the right endpoint the kernel
vanishes, so the strict-window theorem is sufficient almost everywhere. -/
theorem highLocalPayment_of_certificate
    {E : Set Plane} (K : StarShapedKakeya E)
    (hheight : ∀ d, (universalPositiveNeedle K d).height < eta)
    {c : ℝ≥0∞} (hcert : UniformHighPaymentCertificate c) (k : ℕ) :
    c * volume (highClass K k) ≤
      ∫⁻ u in highLedger k,
        ENNReal.ofReal u * (selectedQ K).leftLim u := by
  have hmeas : Measurable (fun u =>
      ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u)) := by
    unfold endpointWindowKernel
    fun_prop
  calc
    c * volume (highClass K k) ≤
        (∫⁻ u in highLedger k,
          ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u)) *
            volume (highClass K k) := by
      simpa [mul_comm] using
        mul_le_mul_right (hcert k) (volume (highClass K k))
    _ = ∫⁻ u in highLedger k,
          ENNReal.ofReal (endpointWindowKernel (highOuterRadius k) u) *
            volume (highClass K k) := by
      rw [lintegral_mul_const]
      exact hmeas
    _ ≤ ∫⁻ u in highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by simp [highLedger] :
        MeasurableSet (highLedger k))] with u hu
      by_cases hstrict : u < highOuterRadius k
      · exact highClass_ledger_integrand K hheight k hu hstrict
      · have heq : u = highOuterRadius k :=
          le_antisymm hu.2 (le_of_not_gt hstrict)
        simp [endpointWindowKernel, heq]

/-- Abstract countable disjoint-ledger aggregation.  This is the monotone
convergence/countable-sum core, separated from the numerical payment bound. -/
theorem highTail_countable_aggregate
    {E : Set Plane} (K : StarShapedKakeya E) (c : ℝ≥0∞)
    (hlocal : ∀ k,
      c * volume (highClass K k) ≤
        ∫⁻ u in highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u) :
    c * ∑' k, volume (highClass K k) ≤
      ∫⁻ u in ⋃ k, highLedger k,
        ENNReal.ofReal u * (selectedQ K).leftLim u := by
  rw [← ENNReal.tsum_mul_left]
  calc
    ∑' k, c * volume (highClass K k) ≤
        ∑' k, ∫⁻ u in highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u :=
      ENNReal.tsum_le_tsum hlocal
    _ = ∫⁻ u in ⋃ k, highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u := by
      exact (lintegral_iUnion (fun k => by simp [highLedger])
        (fun k l hkl => highLedger_pairwise_disjoint hkl) _).symm

/-- The countable union of high ledgers is still paid by the selected triangle
outer measure.  Finite restrictions are controlled by the existing layer-cake
theorem; `tsum_le_of_sum_le'` is the monotone-convergence passage. -/
theorem highLedgers_lintegral_le_selectedTriangleOuter
    {E : Set Plane} (K : StarShapedKakeya E) :
    (∫⁻ u in ⋃ k, highLedger k,
      ENNReal.ofReal u * (selectedQ K).leftLim u) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
  rw [lintegral_iUnion (fun k => by simp [highLedger])
    (fun k l hkl => highLedger_pairwise_disjoint hkl)]
  apply tsum_le_of_sum_le' bot_le
  intro s
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hsum : (∑ k ∈ s, ∫⁻ u in highLedger k,
        ENNReal.ofReal u * (selectedQ K).leftLim u) =
        ∫⁻ u in ⋃ k : s, highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u := by
      have hi := lintegral_iUnion
        (μ := volume)
        (s := fun k : s => highLedger k.1)
        (fun _ => by simp [highLedger])
        (fun i j hij => highLedger_pairwise_disjoint (by
          intro h; apply hij; exact Subtype.ext h))
        (fun u => ENNReal.ofReal u * (selectedQ K).leftLim u)
      rw [hi]
      simp only [tsum_fintype]
      exact (Finset.sum_attach s (fun k => ∫⁻ u in highLedger k,
        ENNReal.ofReal u * (selectedQ K).leftLim u)).symm
    rw [hsum]
    calc
      (∫⁻ u in ⋃ k : s, highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u) ≤
        ∫⁻ u in Icc (highB 0) (highB (m + 1)),
          ENNReal.ofReal u * (selectedQ K).leftLim u := by
        apply lintegral_mono_set
        rintro u hu
        rcases mem_iUnion.1 hu with ⟨k, hk⟩
        have hk0 : highB 0 ≤ highB k := by
          unfold highB highA
          norm_num
          positivity
        have hkm : k.1 ≤ m := Finset.le_max' s k.1 k.2
        have htop : highOuterRadius k ≤ highB (m + 1) := by
          exact (highOuterRadius_lt_next_highB k).le.trans (by
            unfold highB highA
            norm_num
            have hc : ((k.1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
            linarith)
        exact ⟨hk0.trans hk.1, hk.2.trans htop⟩
      _ ≤ volume.toOuterMeasure
          (directionTriangleUnion (universalPositiveNeedle K) Set.univ) :=
        K.selectedTriangleUnion_leftLim_lintegral_le (by
          unfold highB
          linarith [highA_pos 0])
  · simp at hs
    simp [hs]

/-- Final analytic POC: once every class has paid `c` on its ledger, the full
infinite high tail is bounded by the selected triangle outer measure. -/
theorem highTail_aggregate_le_selectedTriangleOuter
    {E : Set Plane} (K : StarShapedKakeya E) (c : ℝ≥0∞)
    (hlocal : ∀ k,
      c * volume (highClass K k) ≤
        ∫⁻ u in highLedger k,
          ENNReal.ofReal u * (selectedQ K).leftLim u) :
    c * ∑' k, volume (highClass K k) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) :=
  (highTail_countable_aggregate K c hlocal).trans
    (highLedgers_lintegral_le_selectedTriangleOuter K)

end
end StarKakeyaLower.Witness141
