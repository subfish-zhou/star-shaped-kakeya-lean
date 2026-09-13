import StarKakeyaLower.OneTenthArithmetic
import StarKakeyaLower.OneTenthOpenBankAssembly

/-! Exact ordinary radial integrals for the fixed one-tenth proof.
The closed constants are those of OneTenthArithmetic, not new prices. -/
open Set MeasureTheory Real
open scoped ENNReal Interval
namespace StarKakeyaLower.OneTenth.KernelIntegrals
noncomputable section

def Q (m r : ℝ) : ℝ := -r^2/2 + 2*m*r - 2*m^2*Real.log (1+r/m)
def k (m r : ℝ) : ℝ := (m-r)/(m+r)
def k4 (r : ℝ) : ℝ := min (2/3) (k (2/5) r)

theorem Q_hasDerivAt {m r : ℝ} (hm : 0 < m) (hr : 0 < m+r) :
    HasDerivAt (Q m) (r * k m r) r := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hd : m+r ≠ 0 := ne_of_gt hr
  have hl : 1+r/m ≠ 0 := by
    rw [one_add_div hm0]
    exact div_ne_zero hd hm0
  have hlog := ((hasDerivAt_const r 1).add ((hasDerivAt_id r).div_const m)).log hl
  have h := ((((hasDerivAt_id r).pow 2).neg.div_const 2).add
    ((hasDerivAt_id r).const_mul (2*m))).sub (hlog.const_mul (2*m^2))
  convert h using 1 <;> dsimp [Q, k] <;> field_simp <;> ring

theorem continuousOn_weighted_k {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) :
    ContinuousOn (fun r => r * k m r) (Icc a b) := by
  apply continuousOn_id.mul
  apply (continuousOn_const.sub continuousOn_id).div
    (continuousOn_const.add continuousOn_id)
  intro r hr
  apply ne_of_gt
  dsimp only [Pi.add_apply, id_eq]
  linarith [hr.1]

theorem integrable_weighted_k {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun r => r * k m r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact continuousOn_weighted_k hm ha

theorem integral_weighted_k {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ r in a..b, r * k m r) = Q m b - Q m a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r hr
    rw [uIcc_of_le hab] at hr
    exact Q_hasDerivAt hm (by linarith [hr.1])
  · exact integrable_weighted_k hm ha hab

theorem integral_C5 : (∫ r in (1/5 : ℝ)..(7/20), r * k (1/2) r) = C5 := by
  rw [integral_weighted_k (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Q, C5]
  have hl : Real.log (17/10 : ℝ) - Real.log (7/5) = Real.log (17/14) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1 <;> norm_num
  linarith [hl]

theorem integral_C6 : (∫ r in (7/20 : ℝ)..(1/2), r * k (3/5) r) = C6 := by
  rw [integral_weighted_k (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Q, C6]
  have hl : Real.log (11/6 : ℝ) - Real.log (19/12) = Real.log (22/19) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1 <;> norm_num
  linarith [hl]

theorem integral_D5 : (∫ r in (7/20 : ℝ)..(1/2), r * k (1/2) r) = D5 := by
  rw [integral_weighted_k (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Q, D5]
  have hl : Real.log (2 : ℝ) - Real.log (17/10) = Real.log (20/17) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1 <;> norm_num
  linarith [hl]

theorem k4_left {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2/25) : k4 r = 2/3 := by
  apply min_eq_left
  unfold k
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < 2/5+r)).mpr
  linarith

theorem k4_right {r : ℝ} (hr : 2/25 ≤ r) : k4 r = k (2/5) r := by
  apply min_eq_right
  unfold k
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 2/5+r)).mpr
  linarith

theorem continuousOn_weighted_k4 : ContinuousOn (fun r => r*k4 r) (Icc (0 : ℝ) (1/5)) := by
  apply continuousOn_id.mul
  apply continuousOn_const.inf
  apply (continuousOn_const.sub continuousOn_id).div
    (continuousOn_const.add continuousOn_id)
  intro r hr
  apply ne_of_gt
  dsimp only [Pi.add_apply, id_eq]
  linarith [hr.1]

theorem integrable_weighted_k4 : IntervalIntegrable (fun r => r*k4 r) volume 0 (1/5) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/5)]
  exact continuousOn_weighted_k4

theorem integral_C4 : (∫ r in (0 : ℝ)..(1/5), r*k4 r) = C4 := by
  have hleft : (∫ r in (0 : ℝ)..(2/25), r*k4 r) = (2/25)^2/3 := by
    calc
      _ = ∫ r in (0 : ℝ)..(2/25), r*(2/3) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2/25)] at hr
        dsimp only
        rw [k4_left hr.1 hr.2]
      _ = _ := by rw [intervalIntegral.integral_mul_const, integral_id]; norm_num
  have hright : (∫ r in (2/25 : ℝ)..(1/5), r*k4 r) = Q (2/5) (1/5) - Q (2/5) (2/25) := by
    calc
      _ = ∫ r in (2/25 : ℝ)..(1/5), r*k (2/5) r := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le (by norm_num : (2/25 : ℝ) ≤ 1/5)] at hr
        dsimp only
        rw [k4_right hr.1]
      _ = _ := integral_weighted_k (by norm_num) (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (2/25 : ℝ))
    (integrable_weighted_k4.mono_set (by intro r hr; simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2/25), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/5), mem_Icc] at *; constructor <;> linarith [hr.1, hr.2]))
    (integrable_weighted_k4.mono_set (by intro r hr; simp only [uIcc_of_le (by norm_num : (2/25 : ℝ) ≤ 1/5), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/5), mem_Icc] at *; constructor <;> linarith [hr.1, hr.2]))]
  rw [hleft, hright]
  norm_num [Q, C4]
  have hl : Real.log (3/2 : ℝ) - Real.log (6/5) = Real.log (5/4) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1 <;> norm_num
  linarith [hl]

end
end StarKakeyaLower.OneTenth.KernelIntegrals
