import StarKakeyaLower.OneTenthKernelIntegrals

/-! Local section-to-price interface. This is not a universal geometry theorem.
All minorants concern the very same physical section of G. -/
open Set MeasureTheory Real
open scoped ENNReal Interval
namespace StarKakeyaLower.OneTenth.KernelIntegrals
noncomputable section

theorem Ioo_inter_positive {a b : ℝ} (ha : 0 ≤ a) :
    Ioo a b ∩ Ioi (0 : ℝ) = Ioo a b := by
  apply inter_eq_left.mpr
  intro r hr
  exact lt_of_le_of_lt ha hr.1

/-- Removing the lower endpoint, including r=0, changes no radial receipt.
This is a single endpoint-null operation for Lebesgue measure. -/
theorem radialBank_Ico_eq_Ioo (G : Set CoordinatePlane) (a b : ℝ) :
    radialBank G (Ico a b) = radialBank G (Ioo a b) := by
  unfold radialBank
  apply setLIntegral_congr
  filter_upwards [(Ioo_ae_eq_Ico (μ := (volume : Measure ℝ)) (a := a) (b := b)).symm] with r hr
  exact congrArg (fun p : Prop => p ∧ 0 < r) hr

/-- The actual bounded bank is integrable, even when volume G is infinite. -/
theorem integrable_density_Ioo {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun r => (openBankDensity G r).toReal) (Ioo a b) := by
  have h := integrableOn_openBankDensity_toReal hG
    (s := Ioo a b) (by simp)
  rwa [Ioo_inter_positive ha] at h

/-- Ordinary finite-interval comparison, transferred to the existing ENNReal
bank only AFTER both ordinary integrals have been justified. -/
theorem integral_le_radialBank {G : Set CoordinatePlane} (hG : MeasurableSet G)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hminor : ∀ r ∈ Ioo a b, f r ≤ min r 1 * (physicalLength G r).toReal) :
    ENNReal.ofReal (∫ r in a..b, f r) ≤ radialBank G (Ioo a b) := by
  rw [radialBank_eq_ofReal_integral hG (by simp), Ioo_inter_positive ha,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply ENNReal.ofReal_le_ofReal
  apply setIntegral_mono_on
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hf)
    (integrable_density_Ioo hG ha) measurableSet_Ioo
  intro r hr
  rw [openBankDensity_toReal (by linarith [hr.1])]
  exact hminor r hr

theorem same_section_convex {x y s lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hx : x ≤ s) (hy : y ≤ s) : lam*x + (1-lam)*y ≤ s := by
  calc
    _ ≤ lam*s + (1-lam)*s := add_le_add (mul_le_mul_of_nonneg_left hx hlam0)
      (mul_le_mul_of_nonneg_left hy (by linarith))
    _ = s := by ring

/-- Explicit low-lane contract: v=b+u is the B/U mass addition; k5 and k6
are SEPARATE minorants of ONE physical section, never summable angular sets. -/
theorem low_price_le_radialBanks {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (b u v : ℝ) (hv : b+u=v)
    (h4 : ∀ r ∈ Ioo (0 : ℝ) (1/5), k4 r * (v+b) ≤ (physicalLength G r).toReal)
    (h5 : ∀ r ∈ Ioo (1/5 : ℝ) (1/2), k (1/2) r * v ≤ (physicalLength G r).toReal)
    (h6 : ∀ r ∈ Ioo (7/20 : ℝ) (1/2), k (3/5) r * u ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal (lowCoefficient*v) ≤
      radialBank G (Ioo 0 (1/5 : ℝ)) +
      radialBank G (Ico (1/5 : ℝ) (7/20)) +
      radialBank G (Ico (7/20 : ℝ) (1/2)) := by
  have p4 : ENNReal.ofReal (C4*(v+b)) ≤ radialBank G (Ioo 0 (1/5 : ℝ)) := by
    have h := integral_le_radialBank hG (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 1/5) (integrable_weighted_k4.mul_const (v+b))
      (fun r hr => by
        rw [min_eq_left (by linarith [hr.2] : r ≤ 1)]
        calc r*k4 r*(v+b) = r*(k4 r*(v+b)) := by ring
             _ ≤ r*(physicalLength G r).toReal := mul_le_mul_of_nonneg_left (h4 r hr) hr.1.le)
    simpa only [intervalIntegral.integral_mul_const, integral_C4] using h
  have p5 : ENNReal.ofReal (C5*v) ≤ radialBank G (Ioo (1/5 : ℝ) (7/20)) := by
    have h := integral_le_radialBank hG (by norm_num : (0 : ℝ) ≤ 1/5)
      (by norm_num : (1/5 : ℝ) ≤ 7/20)
      ((integrable_weighted_k (m := (1/2 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num : (1/5 : ℝ) ≤ 7/20)).mul_const v)
      (fun r hr => by
        rw [min_eq_left (by linarith [hr.2] : r ≤ 1)]
        calc r*k (1/2) r*v = r*(k (1/2) r*v) := by ring
             _ ≤ r*(physicalLength G r).toReal := mul_le_mul_of_nonneg_left
               (h5 r ⟨hr.1, by linarith [hr.2]⟩) (by linarith [hr.1]))
    simpa only [intervalIntegral.integral_mul_const, integral_C5] using h
  have i6 := (integrable_weighted_k (m := (3/5 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num : (7/20 : ℝ) ≤ 1/2)).mul_const (price*u)
  have i5 := (integrable_weighted_k (m := (1/2 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num : (7/20 : ℝ) ≤ 1/2)).mul_const ((1-price)*v)
  have p65 : ENNReal.ofReal (C6*(price*u)+D5*((1-price)*v)) ≤
      radialBank G (Ioo (7/20 : ℝ) (1/2)) := by
    have h := integral_le_radialBank hG (by norm_num : (0 : ℝ) ≤ 7/20)
      (by norm_num : (7/20 : ℝ) ≤ 1/2) (i6.add i5)
      (fun r hr => by
        rw [min_eq_left (by linarith [hr.2] : r ≤ 1)]
        have hs := same_section_convex price_mem_Ioo.1.le price_mem_Ioo.2.le
          (h6 r hr) (h5 r ⟨by linarith [hr.1], hr.2⟩)
        calc
          r*k (3/5) r*(price*u) + r*k (1/2) r*((1-price)*v) =
            r*(price*(k (3/5) r*u)+(1-price)*(k (1/2) r*v)) := by ring
          _ ≤ r*(physicalLength G r).toReal := mul_le_mul_of_nonneg_left hs (by linarith [hr.1]))
    simpa only [intervalIntegral.integral_add i6 i5, intervalIntegral.integral_mul_const,
      integral_C6, integral_D5] using h
  rw [radialBank_Ico_eq_Ioo, radialBank_Ico_eq_Ioo]
  have he : C4*(v+b)+C5*v+(C6*(price*u)+D5*((1-price)*v)) = lowCoefficient*v := by
    rw [← hv]
    nlinarith [low_payment_identity b u]
  rw [← he]
  exact ENNReal.ofReal_add_le.trans
    (add_le_add (ENNReal.ofReal_add_le.trans (add_le_add p4 p5)) p65)

/-- Same explicit minorants, now paid by actual planar area through the three
DISJOINT radial supports. Final universal geometry is deliberately not assumed. -/
theorem low_price_le_volume {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (b u v : ℝ) (hv : b+u=v)
    (h4 : ∀ r ∈ Ioo (0 : ℝ) (1/5), k4 r * (v+b) ≤ (physicalLength G r).toReal)
    (h5 : ∀ r ∈ Ioo (1/5 : ℝ) (1/2), k (1/2) r * v ≤ (physicalLength G r).toReal)
    (h6 : ∀ r ∈ Ioo (7/20 : ℝ) (1/2), k (3/5) r * u ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal (lowCoefficient*v) ≤ volume G :=
  (low_price_le_radialBanks hG b u v hv h4 h5 h6).trans (low_three_radialBanks_le_volume hG)

/-- Finite source measure addition is derived from the disjoint B/U partition,
not supplied as a scalar payment. No measurability of a generated union of
triangles occurs here. -/
theorem source_mass_add {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {B U V : Set α} (hU : MeasurableSet U) (hd : Disjoint B U)
    (hBU : B ∪ U = V) (hV : μ V ≠ ∞) :
    (μ B).toReal + (μ U).toReal = (μ V).toReal := by
  have hB : μ B ≠ ∞ := ne_top_of_le_ne_top hV
    (measure_mono (show B ⊆ V by rw [← hBU]; exact subset_union_left))
  have hUfin : μ U ≠ ∞ := ne_top_of_le_ne_top hV
    (measure_mono (show U ⊆ V by rw [← hBU]; exact subset_union_right))
  rw [← hBU, measure_union hd hU, ENNReal.toReal_add hB hUfin]

/-- Measure-valued source adapter for a finite B/U partition. The three input
inequalities still need the actual geometric SectionBounds proof. -/
theorem low_price_of_source_partition {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {B U V : Set α} (hU : MeasurableSet U)
    (hd : Disjoint B U) (hBU : B ∪ U = V) (hV : μ V ≠ ∞)
    {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (h4 : ∀ r ∈ Ioo (0 : ℝ) (1/5),
      k4 r * ((μ V).toReal+(μ B).toReal) ≤ (physicalLength G r).toReal)
    (h5 : ∀ r ∈ Ioo (1/5 : ℝ) (1/2),
      k (1/2) r * (μ V).toReal ≤ (physicalLength G r).toReal)
    (h6 : ∀ r ∈ Ioo (7/20 : ℝ) (1/2),
      k (3/5) r * (μ U).toReal ≤ (physicalLength G r).toReal) :
    ENNReal.ofReal (lowCoefficient*(μ V).toReal) ≤
      radialBank G (Ioo 0 (1/5 : ℝ)) +
      radialBank G (Ico (1/5 : ℝ) (7/20)) +
      radialBank G (Ico (7/20 : ℝ) (1/2)) :=
  low_price_le_radialBanks hG _ _ _ (source_mass_add μ hU hd hBU hV) h4 h5 h6

end
end StarKakeyaLower.OneTenth.KernelIntegrals
