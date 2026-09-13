import StarKakeyaLower.OneTenthHighTailIntegration

/-! Tail n pays unchanged source bin D (n+1); D0 keeps its old bank. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth
noncomputable section

def highTailDyadicSupport (n : ℕ) : Set ℝ :=
  highTailSupport (Sources.dyadicScale (n+1))

theorem highTail_dyadic_lower (n : ℕ) : 16/5 ≤ Sources.dyadicScale (n+1) := by
  rw [Sources.dyadicScale_succ]
  linarith [Sources.dyadicScale_lower n]

theorem measurableSet_highTailDyadicSupport (n : ℕ) :
    MeasurableSet (highTailDyadicSupport n) := measurableSet_Ico

theorem highTailDyadicSupport_first : highTailDyadicSupport 0 = Ico (8/5 : ℝ) (12/5) := by
  norm_num [highTailDyadicSupport, highTailSupport, Sources.dyadicScale]

theorem highTailDyadicSupport_disjoint_of_lt {n k : ℕ} (hnk : n < k) :
    Disjoint (highTailDyadicSupport n) (highTailDyadicSupport k) := by
  have hstep := Sources.dyadicScale_mono (Nat.succ_le_iff.mpr (Nat.succ_lt_succ hnk))
  rw [Sources.dyadicScale_succ (n+1)] at hstep
  have hp := highTail_dyadic_lower n
  apply disjoint_left.mpr
  intro r hr hs
  change Sources.dyadicScale (n+1)/2 ≤ r ∧ r < 3*Sources.dyadicScale (n+1)/4 at hr
  change Sources.dyadicScale (k+1)/2 ≤ r ∧ r < 3*Sources.dyadicScale (k+1)/4 at hs
  linarith [hr.2, hs.1]

theorem pairwise_disjoint_highTailDyadicSupport :
    Pairwise (fun n k => Disjoint (highTailDyadicSupport n) (highTailDyadicSupport k)) := by
  intro n k hnk
  rcases lt_or_gt_of_ne hnk with h | h
  · exact highTailDyadicSupport_disjoint_of_lt h
  · exact (highTailDyadicSupport_disjoint_of_lt h).symm

theorem highTailDyadicSupport_above (n : ℕ) : highTailDyadicSupport n ⊆ Ici (8/5 : ℝ) := by
  intro r hr
  have h : Sources.dyadicScale (n+1)/2 ≤ r := hr.1
  have hm := highTail_dyadic_lower n
  change 8/5 ≤ r
  linarith

theorem highTailDyadicSupport_disjoint_below (n : ℕ) :
    Disjoint (highTailDyadicSupport n) (Iio (8/5 : ℝ)) := by
  apply disjoint_left.mpr
  intro r hr hs
  exact not_lt_of_ge (show 8/5 ≤ r from highTailDyadicSupport_above n hr)
    (show r < 8/5 from hs)

theorem highTailDyadicSupport_disjoint_low (n : ℕ) :
    Disjoint (highTailDyadicSupport n) (Ioo (0 : ℝ) (1/2)) := by
  apply (highTailDyadicSupport_disjoint_below n).mono_right
  intro r hr
  change r < 8/5
  linarith [hr.2]

theorem highTailDyadicSupport_disjoint_F (n : ℕ) :
    Disjoint (highTailDyadicSupport n) (Ico (1/2 : ℝ) (4/5)) := by
  apply (highTailDyadicSupport_disjoint_below n).mono_right
  intro r hr
  change r < 8/5
  linarith [hr.2]

theorem highTailDyadicSupport_disjoint_D0 (n : ℕ) :
    Disjoint (highTailDyadicSupport n) (Ico (4/5 : ℝ) (6/5)) := by
  apply (highTailDyadicSupport_disjoint_below n).mono_right
  intro r hr
  change r < 8/5
  linarith [hr.2]

/-- Countable tail receipts are paid by one physical bank, not one copy of
area per dyadic source. Low/F/D0 can be adjoined using the disjointness above. -/
theorem highTail_dyadic_receipts_le_volume {G : Set CoordinatePlane} (hG : MeasurableSet G)
    (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (hsection : ∀ n r, r ∈ highTailDyadicSupport n →
      ENNReal.ofReal (L n * highTailKernel (Sources.dyadicScale (n+1)) r) ≤
        physicalLength G r) :
    (∑' n, ENNReal.ofReal (L n/24)) ≤ volume G := by
  apply le_trans (ENNReal.tsum_le_tsum (fun n =>
    highTail_kernel_radialBank_receipt hG (highTail_dyadic_lower n) (hL n) (hsection n)))
  exact disjoint_radialBank_sum_le_volume hG highTailDyadicSupport
    measurableSet_highTailDyadicSupport pairwise_disjoint_highTailDyadicSupport

end
end StarKakeyaLower.OneTenth
