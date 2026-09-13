import StarKakeyaLower.OneTenthSectionBoundsReal

/-! Fixed high-source constants from actual bounded physical sections.
The source cuts, signed heights, external feet and filled triangles are unchanged. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.FixedHigh
noncomputable section
open Sources SectionBounds

/-- A coarse exact square comparison suffices for the paper's F constant. -/
theorem F_sqrt_lower : (79/50 : ℝ) ≤ Real.sqrt ((8/5 : ℝ)^2-(1/5)^2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (8/5)^2-(1/5)^2)
  have hn := Real.sqrt_nonneg ((8/5 : ℝ)^2-(1/5)^2)
  nlinarith

theorem K_F_lower : (7/30 : ℝ) ≤ K (8/5) (1/5) := by
  rw [K_eq_sqrt_div (by norm_num) (by norm_num)]
  apply (le_div_iff₀ (by positivity)).2
  nlinarith [F_sqrt_lower]

/-- D0 needs only sqrt(256/25-1/25) >= 3. -/
theorem D0_sqrt_lower : (3 : ℝ) ≤ Real.sqrt ((16/5 : ℝ)^2-(1/5)^2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (16/5)^2-(1/5)^2)
  have hn := Real.sqrt_nonneg ((16/5 : ℝ)^2-(1/5)^2)
  nlinarith

theorem K_D0_lower : (1/8 : ℝ) ≤ K (16/5) (1/5) := by
  rw [K_eq_sqrt_div (by norm_num) (by norm_num)]
  apply (le_div_iff₀ (by positivity)).2
  nlinarith [D0_sqrt_lower]

theorem F_variable_lower1 {r : ℝ} (hr : r ∈ Ico (1/2 : ℝ) (3/5)) :
    (7/30 : ℝ) ≤ ((99/100)-r)/((99/100)+r) := by
  apply (le_div_iff₀ (by linarith [hr.1])).2
  linarith [hr.2]

theorem F_variable_lower2 {r : ℝ} (hr : r ∈ Ico (3/5 : ℝ) (7/10)) :
    (29/169 : ℝ) ≤ ((99/100)-r)/((99/100)+r) := by
  apply (le_div_iff₀ (by linarith [hr.1])).2
  linarith [hr.2]

theorem F_variable_lower3 {r : ℝ} (hr : r ∈ Ico (7/10 : ℝ) (4/5)) :
    (19/179 : ℝ) ≤ ((99/100)-r)/((99/100)+r) := by
  apply (le_div_iff₀ (by linarith [hr.1])).2
  linarith [hr.2]

theorem D0_variable_lower {r : ℝ} (hr : r ∈ Ico (4/5 : ℝ) (6/5)) :
    (1/8 : ℝ) ≤ ((8/5)-r)/((8/5)+r) := by
  apply (le_div_iff₀ (by linarith [hr.1])).2
  linarith [hr.2]

theorem F_kernel_lower1 {r : ℝ} (hr : r ∈ Ico (1/2 : ℝ) (3/5)) :
    (7/30 : ℝ) ≤ min (K (8/5) (1/5)) (((99/100)-r)/((99/100)+r)) :=
  le_min K_F_lower (F_variable_lower1 hr)

theorem F_kernel_lower2 {r : ℝ} (hr : r ∈ Ico (3/5 : ℝ) (7/10)) :
    (29/169 : ℝ) ≤ min (K (8/5) (1/5)) (((99/100)-r)/((99/100)+r)) :=
  le_min ((by norm_num : (29/169 : ℝ) ≤ 7/30).trans K_F_lower) (F_variable_lower2 hr)

theorem F_kernel_lower3 {r : ℝ} (hr : r ∈ Ico (7/10 : ℝ) (4/5)) :
    (19/179 : ℝ) ≤ min (K (8/5) (1/5)) (((99/100)-r)/((99/100)+r)) :=
  le_min ((by norm_num : (19/179 : ℝ) ≤ 7/30).trans K_F_lower) (F_variable_lower3 hr)

theorem D0_kernel_lower {r : ℝ} (hr : r ∈ Ico (4/5 : ℝ) (6/5)) :
    (1/8 : ℝ) ≤ min (K (16/5) (1/5)) (((8/5)-r)/((8/5)+r)) :=
  le_min K_D0_lower (D0_variable_lower hr)

/-- The actual F cut supplies both endpoint radius bounds. No angular premise. -/
theorem F_bounded_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVF : V ⊆ F o c)
    (G : Set Plane) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 0 < r) (hrm : r < 99/100) :
    min (K (8/5) (1/5)) (((99/100)-r)/((99/100)+r))*(mass V).toReal ≤
      (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact bounded_section_real o hc hV (fun q hq => (hVF hq).1) G htri
    (by norm_num) (by norm_num) hh
    (fun q hq => (hVF hq).2.2.le) (fun q hq => (hVF hq).2.1) hr hrm

/-- D0 is literally Sources.D o c 0, not a substitute source. -/
theorem D0_bounded_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVD : V ⊆ D o c 0)
    (G : Set Plane) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 0 < r) (hrm : r < 8/5) :
    min (K (16/5) (1/5)) (((8/5)-r)/((8/5)+r))*(mass V).toReal ≤
      (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  apply bounded_section_real o hc hV (fun q hq => (hVD hq).1) G htri
    (by norm_num) (by norm_num) hh _ _ hr hrm
  · intro q hq
    have h := (hVD hq).2.2.le
    norm_num only [dyadicScale_zero] at h
    linarith
  · intro q hq
    simpa only [dyadicScale_zero] using (hVD hq).2.1

theorem F_section_real1 (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVF : V ⊆ F o c)
    (G : Set Plane) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : r ∈ Ico (1/2 : ℝ) (3/5)) :
    (7/30)*(mass V).toReal ≤ (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact (mul_le_mul_of_nonneg_right (F_kernel_lower1 hr) ENNReal.toReal_nonneg).trans
    (F_bounded_section_real o hc hV hVF G htri hh (by linarith [hr.1]) (by linarith [hr.2]))

theorem F_section_real2 (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVF : V ⊆ F o c)
    (G : Set Plane) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : r ∈ Ico (3/5 : ℝ) (7/10)) :
    (29/169)*(mass V).toReal ≤ (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact (mul_le_mul_of_nonneg_right (F_kernel_lower2 hr) ENNReal.toReal_nonneg).trans
    (F_bounded_section_real o hc hV hVF G htri hh (by linarith [hr.1]) (by linarith [hr.2]))

theorem F_section_real3 (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVF : V ⊆ F o c)
    (G : Set Plane) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : r ∈ Ico (7/10 : ℝ) (4/5)) :
    (19/179)*(mass V).toReal ≤ (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact (mul_le_mul_of_nonneg_right (F_kernel_lower3 hr) ENNReal.toReal_nonneg).trans
    (F_bounded_section_real o hc hV hVF G htri hh (by linarith [hr.1]) (by linarith [hr.2]))

theorem D0_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVD : V ⊆ D o c 0)
    (G : Set Plane) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : r ∈ Ico (4/5 : ℝ) (6/5)) :
    (1/8)*(mass V).toReal ≤ (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact (mul_le_mul_of_nonneg_right (D0_kernel_lower hr) ENNReal.toReal_nonneg).trans
    (D0_bounded_section_real o hc hV hVD G htri hh (by linarith [hr.1]) (by linarith [hr.2]))

end
end StarKakeyaLower.OneTenth.FixedHigh
