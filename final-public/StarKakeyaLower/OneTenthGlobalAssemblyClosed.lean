import StarKakeyaLower.OneTenthGlobalAssemblyTail
import StarKakeyaLower.OneTenthFixedHighBank

/-! Global one-tenth assembly from actual physical bank receipts. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.GlobalAssembly
noncomputable section
open Sources SectionBounds

theorem actual_F_bank_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal (1/(10*Real.pi)) * mass (sourceCut o c 1) ≤
      radialBank (centeredCoordinateEnvelope o G) (radialSupport 1) := by
  have H := FixedHigh.actual_F_radial_price o hc G hG
    (fun q hq => htri q hq.1) (fun q hq => hh q hq.1)
  rw [ofReal_mul_mass] at H
  exact (mul_le_mul_right' (ENNReal.ofReal_le_ofReal finite_high_gt_target.le) _).trans H

theorem actual_D0_bank_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal (1/(10*Real.pi)) * mass (sourceCut o c 2) ≤
      radialBank (centeredCoordinateEnvelope o G) (radialSupport 2) := by
  have H := FixedHigh.actual_D0_radial_price o hc G hG
    (fun q hq => htri q hq.1) (fun q hq => hh q hq.1)
  rw [ofReal_mul_mass] at H
  exact (mul_le_mul_right' (ENNReal.ofReal_le_ofReal first_tail_gt_target.le) _).trans H

/-- Every actual source is paid by its assigned disjoint physical bank. -/
theorem actual_bank_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) (n : ℕ) :
    ENNReal.ofReal (1/(10*Real.pi)) * mass (sourceCut o c n) ≤
      radialBank (centeredCoordinateEnvelope o G) (radialSupport n) := by
  rcases n with _ | _ | _ | n
  · exact actual_low_bank_price o hc G hG htri hh
  · exact actual_F_bank_price o hc G hG htri hh
  · exact actual_D0_bank_price o hc G hG htri hh
  · exact actual_tail_bank_price o hc G hG htri hh n

/-- The small-height branch, with all angular, radial and area receipts proved.
No finite-area assumption and no conversion of volume G to a real number. -/
theorem small_height_one_tenth (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume G := by
  rw [← target_prices_sum o hc]
  exact (ENNReal.tsum_le_tsum (actual_bank_price o hc G hG htri hh)).trans
    (actual_banks_sum_le_volume o hG)

/-- Every open cover of the faithful original arbitrary star-shaped Kakeya set
has area at least 1/10. The recovery and high-height alternative are discharged. -/
theorem open_cover_one_tenth {E G : Set Plane} (Kak : StarShapedKakeya E)
    (hEG : E ⊆ G) (hG : IsOpen G) : ENNReal.ofReal (1/10 : ℝ) ≤ volume G := by
  rcases recovered_small_height_or_area Kak hEG hG with h | ⟨c,hc,_hfin,hcG⟩
  · exact h
  · exact small_height_one_tenth Kak.center hc G hG
      (fun q hq => (hcG q hq).2.1) (fun q hq => (hcG q hq).2.2.le)

end
end StarKakeyaLower.OneTenth.GlobalAssembly
