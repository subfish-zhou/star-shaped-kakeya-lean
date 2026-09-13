import StarKakeyaLower.OneTenthGlobalAssembly

/-! Actual Borel D(n+1) family receipts obtained from the proved general
physical section theorem and the bounded quarter-annulus integral. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.GlobalAssembly
noncomputable section
open Sources SectionBounds

/-- A coarse constant minorant of the already proved literal bounded kernel. -/
theorem tail_bounded_kernel_lower {m r : ℝ} (hm : 16/5 ≤ m)
    (hr : r ∈ highTailSupport m) :
    1/(6*m) ≤ min (K (2*m) (1/5)) ((m-r)/(m+r)) := by
  have hlo : m/2 ≤ r := hr.1
  have hhi : r < 3*m/4 := hr.2
  apply le_min
  · unfold K
    apply one_div_le_one_div_of_le
    · have h := coneBudget_nonneg (2*m) (1/5)
      linarith
    · change 1+2*highTailConeBudget m ≤ 6*m
      linarith [highTail_coneBudget_le hm]
  · have h1 : (1/(6*m) : ℝ) ≤ 1/7 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    apply h1.trans
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7)
      (by linarith : 0 < m+r)).mpr
    linarith

/-- Tail geometry is discharged for the actual source class, including signed
and zero heights by bounded_section_real. The receipt is individual bank mass. -/
theorem actual_tail_radial_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) (n : ℕ) :
    ENNReal.ofReal ((mass (D o c (n+1))).toReal/24) ≤
      radialBank (centeredCoordinateEnvelope o G) (highTailDyadicSupport n) := by
  let m := dyadicScale (n+1)
  have hm : 16/5 ≤ m := highTail_dyadic_lower n
  apply highTail_radialBank_receipt (isOpen_centeredCoordinateEnvelope o hG).measurableSet hm
  intro r hr
  have hrlo : m/2 ≤ r := hr.1
  have hrhi : r < 3*m/4 := hr.2
  have H := bounded_section_real o hc (measurableSet_D o hc (n+1)) inter_subset_left
    G (fun q hq => htri q hq.1) (by norm_num : (1/5 : ℝ) ≤ 1/2)
    (by linarith : (1/5 : ℝ) < 2*m) (fun q hq => hh q hq.1)
    (fun q hq => hq.2.2.le) (fun q hq => hq.2.1)
    (by linarith : 0 < r) (by linarith : r < m)
  apply le_trans _ H
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    mul_le_mul_of_nonneg_right (tail_bounded_kernel_lower hm hr)
      (ENNReal.toReal_nonneg : 0 ≤ (mass (D o c (n+1))).toReal)

theorem actual_tail_bank_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) (n : ℕ) :
    ENNReal.ofReal (1/(10*Real.pi)) * mass (sourceCut o c (n+3)) ≤
      radialBank (centeredCoordinateEnvelope o G) (radialSupport (n+3)) := by
  have H := actual_tail_radial_price o hc G hG htri hh n
  have he : (mass (D o c (n+1))).toReal/24 =
      (1/24 : ℝ)*(mass (D o c (n+1))).toReal := by ring
  rw [he,ofReal_mul_mass] at H
  exact (mul_le_mul_right' (ENNReal.ofReal_le_ofReal highTail_price_strict.le) _).trans H

end
end StarKakeyaLower.OneTenth.GlobalAssembly
