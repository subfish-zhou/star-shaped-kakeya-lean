import StarKakeyaLower.OneTenthSectionBounds

/-! Real minorants and the actual recovery/high-height split.
No area premise is concealed: the high-height case is an explicit conclusion. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.SectionBounds
noncomputable section
open Sources

theorem mass_ne_top (V : Set ℝ) : mass V ≠ ∞ := measure_ne_top _ _

theorem mass_eq_volume {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart) :
    mass V = volume V := by
  exact (chart_image_measure Real.pi 0 V hV (by simpa only [zero_add] using hchart)).2

/-- The actual B/U source ledger, independent of physical overlaps. -/
theorem mass_split (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart) :
    mass (V ∩ B o c)+mass (V \ B o c) = mass V := by
  rw [mass_eq_volume (hV.inter (measurableSet_B o hc)) (inter_subset_left.trans hchart),
    mass_eq_volume (hV.diff (measurableSet_B o hc)) (diff_subset.trans hchart),
    mass_eq_volume hV hchart]
  exact measure_inter_add_diff V (measurableSet_B o hc)

theorem mass_split_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart) :
    (mass (V ∩ B o c)).toReal+(mass (V \ B o c)).toReal = (mass V).toReal := by
  rw [← ENNReal.toReal_add (mass_ne_top _) (mass_ne_top _),mass_split o hc hV hchart]

theorem minorant_toReal {W : Set CoordinatePlane} {r κ : ℝ} {μ : ℝ≥0∞}
    (hκ : 0 ≤ κ) (h : ENNReal.ofReal κ*μ ≤ physicalLength W r) :
    κ*μ.toReal ≤ (physicalLength W r).toReal := by
  have ht : physicalLength W r ≠ ∞ :=
    (lt_of_le_of_lt (physicalLength_le_full_turn W r) ENNReal.ofReal_lt_top).ne
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hκ] using ENNReal.toReal_mono ht h

theorem k4_nonneg {r : ℝ} (hr : 0 ≤ r) (hrmax : r ≤ 2/5) : 0 ≤ k4 r := by
  unfold k4
  apply le_min (by norm_num)
  exact div_nonneg (by linarith) (by linarith)

theorem low_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 0 < r) (hrmax : r < 2/5) :
    k4 r*((mass V).toReal+(mass (V ∩ B o c)).toReal) ≤
      (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  have H := minorant_toReal (k4_nonneg hr.le hrmax.le)
    (low_section o hc hV hVL G hG hh hr hrmax)
  simpa only [ENNReal.toReal_add (mass_ne_top _) (mass_ne_top _)] using H

theorem mid_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 1/5 ≤ r) (hrmax : r < 1/2) :
    k5 r*(mass V).toReal ≤ (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact minorant_toReal (div_nonneg (by linarith) (by linarith))
    (mid_section o hc hV hVL G hG hh hr hrmax)

theorem outer_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 1/5 ≤ r) (hrmax : r < 3/5) :
    k6 r*(mass (V \ B o c)).toReal ≤
      (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  exact minorant_toReal (div_nonneg (by linarith) (by linarith))
    (outer_section o hc hV hVL G hG hh hr hrmax)

theorem bounded_section_real (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    {r m R H : ℝ} (hH : H ≤ 1/2) (hRH : H < R)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ H)
    (hMR : ∀ q ∈ V, M o c q ≤ R) (hmM : ∀ q ∈ V, m ≤ M o c q)
    (hr : 0 < r) (hrm : r < m) :
    min (K R H) ((m-r)/(m+r))*(mass V).toReal ≤
      (physicalLength (centeredCoordinateEnvelope o G) r).toReal := by
  have hC := coneBudget_nonneg R H
  have hk : 0 ≤ K R H := by unfold K; positivity
  exact minorant_toReal (le_min hk (div_nonneg (by linarith) (by linarith)))
    (bounded_section o hc hV hchart G hG hH hRH hh hMR hmM hr hrm)

/-- Identification with the literal K(R,H) displayed in the paper. -/
theorem K_eq_sqrt_div {R H : ℝ} (hH : 0 ≤ H) (hRH : H < R) :
    K R H = Real.sqrt (R^2-H^2)/(Real.sqrt (R^2-H^2)+2*R^2) := by
  have hs : Real.sqrt (R^2-H^2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith : 0 < R^2-H^2)).ne'
  have he : 1+2*(R^2/Real.sqrt (R^2-H^2)) =
      (Real.sqrt (R^2-H^2)+2*R^2)/Real.sqrt (R^2-H^2) := by
    field_simp
  unfold K coneBudget
  rw [he,one_div_div]

/-- The literal paper kernel, with all physical interval obligations proved. -/
theorem bounded_section_sqrt (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    {r m R H : ℝ} (hH0 : 0 ≤ H) (hH : H ≤ 1/2) (hRH : H < R)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ H)
    (hMR : ∀ q ∈ V, M o c q ≤ R) (hmM : ∀ q ∈ V, m ≤ M o c q)
    (hr : 0 < r) (hrm : r < m) :
    ENNReal.ofReal (min (Real.sqrt (R^2-H^2)/(Real.sqrt (R^2-H^2)+2*R^2))
      ((m-r)/(m+r)))*mass V ≤ physicalLength (centeredCoordinateEnvelope o G) r := by
  rw [← K_eq_sqrt_div hH0 hRH]
  exact bounded_section o hc hV hchart G hG hH hRH hh hMR hmM hr hrm

/-- If the actual target has not already paid 1/10, every recovered triangle
has SMALL signed height. This is a proved consequence, not a selection premise. -/
theorem small_height_of_not_area (o : Plane) (c : ℝ → Plane) {V : Set ℝ}
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (harea : ¬ ENNReal.ofReal (1/10 : ℝ) ≤ volume G) :
    ∀ q ∈ V, |farHeight o c q| < 1/5 := by
  intro q hq
  by_contra hh
  apply harea
  apply one_tenth_le_of_triangle_height (needle c q) (hG q hq)
  rw [needle_height,← abs_farHeight]
  exact le_of_not_gt hh

/-- Literal Borel recovery followed by the proved high-height alternative. -/
theorem recovered_small_height_or_area {E G : Set Plane} (Kak : StarShapedKakeya E)
    (hEG : E ⊆ G) (hG : IsOpen G) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume G ∨
    ∃ c : ℝ → Plane, Measurable c ∧ (range c).Finite ∧
      ∀ q ∈ chart, (needle c q).HasDirection (q : Direction) ∧
        triangle Kak.center c q ⊆ G ∧ |farHeight Kak.center c q| < 1/5 := by
  classical
  by_cases ha : ENNReal.ofReal (1/10 : ℝ) ≤ volume G
  · exact Or.inl ha
  · obtain ⟨c,hc,hfin,ht⟩ := borel_midpoint_recovery Kak hEG hG
    refine Or.inr ⟨c,hc,hfin,?_⟩
    intro q hq
    exact ⟨(ht q hq).1,(ht q hq).2,
      small_height_of_not_area Kak.center c G (fun t ht' => (ht t ht').2) ha q hq⟩

end
end StarKakeyaLower.OneTenth.SectionBounds
