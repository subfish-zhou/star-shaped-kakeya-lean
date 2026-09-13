import StarKakeyaLower.OneTenthSectionBoundsGeneral
import StarKakeyaLower.OneTenthSourcesPartition
import StarKakeyaLower.OneTenthOpenBankPlane

/-! Global physical section bounds of the SAME actual open envelope.
All interval extension and membership obligations are constructed below.
The single-far interface uses the empty near label set, even at high radii. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.SectionBounds
noncomputable section
open Sources

def mass (V : Set ℝ) : ℝ≥0∞ := volume ((fun q : ℝ => (q : ProjectiveDirection)) '' V)
def k4 (r : ℝ) : ℝ := min (2/3) ((2/5-r)/(2/5+r))
def k5 (r : ℝ) : ℝ := (1/2-r)/(1/2+r)
def k6 (r : ℝ) : ℝ := (3/5-r)/(3/5+r)

/-- Exact Euclidean source map, not the product sup norm. -/
theorem sourcePlane_eq_centered (o : Plane) (z : CoordinatePlane) :
    sourcePlane o z = o+openBankCoordinates.symm z := by
  ext i
  fin_cases i <;> rfl

theorem source_preimage_eq_centered (o : Plane) (G : Set Plane) :
    sourcePlane o ⁻¹' G = centeredCoordinateEnvelope o G := by
  ext z
  simp only [mem_preimage,centeredCoordinateEnvelope,sourcePlane_eq_centered]

theorem source_far_radius (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    endpointRadius |farHeight o c q| (x o c q) = M o c q := by
  have hM : 0 ≤ M o c q := le_trans (by norm_num : (0:ℝ) ≤ 1/2) (half_le_M o c q)
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hM).mp
  rw [Real.sq_sqrt (by positivity),sq_abs,M_sq]
  ring

theorem source_near_radius (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    endpointRadius |farHeight o c q| (1-x o c q) = N o c q := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (endpoint_radius_bounds o c q).1).mp
  rw [Real.sq_sqrt (by positivity),sq_abs,N_sq]
  ring

def IntervalAt (α h p r t ρ : ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ a-ρ*(b-a) ≤ t ∧ t ≤ b+ρ*(b-a) ∧
    ∀ θ ∈ Icc a b, polarPoint r θ ∈ supportNeedleTriangle α h (p-1/2)

theorem LocalInterval.at {h p r t ρ : ℝ} (H : LocalInterval h p r t ρ) (α : ℝ) :
    IntervalAt α h p r (α+t) ρ := by
  obtain ⟨a,b,hab,hl,hr,hp⟩ := H
  refine ⟨α+a,α+b,by linarith,by nlinarith,by nlinarith,?_⟩
  intro θ hθ
  have := hp α (θ-α) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
  simpa only [add_sub_cancel] using this

/-- The opposite lift may differ from farAngle+π by a full turn. -/
theorem LocalInterval.at_opposite {h p r ρ : ℝ}
    (H : LocalInterval h p r Real.pi ρ) (A : Set ℝ) (q : ℝ) :
    IntervalAt (selectedAngle A q) h p r (selectedAngle Aᶜ q) ρ := by
  classical
  by_cases hq : q ∈ A
  · simpa [selectedAngle,hq,add_comm] using H.at (selectedAngle A q)
  · have H' := H.sub_turn.at (selectedAngle A q)
    convert H' using 1
    simp [selectedAngle,hq]
    ring

/-- Reciprocal conversion is finite and positive; no finite-area premise. -/
theorem reciprocal_receipt {μ ℓ : ℝ≥0∞} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : μ ≤ ENNReal.ofReal (1+2*ρ)*ℓ) :
    ENNReal.ofReal (1/(1+2*ρ))*μ ≤ ℓ := by
  have hd : 0 < 1+2*ρ := by positivity
  calc
    ENNReal.ofReal (1/(1+2*ρ))*μ ≤
      ENNReal.ofReal (1/(1+2*ρ))*(ENNReal.ofReal (1+2*ρ)*ℓ) :=
      mul_le_mul_right h _
    _ = ℓ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity),
        one_div_mul_cancel hd.ne',ENNReal.ofReal_one,one_mul]

theorem reciprocal_ratio {r m : ℝ} (_hr : 0 ≤ r) (hrm : r < m) :
    1/(1+2*(r/(m-r))) = (m-r)/(m+r) := by
  have hd : m-r ≠ 0 := (sub_pos.mpr hrm).ne'
  have he : 1+2*(r/(m-r)) = (m+r)/(m-r) := by
    field_simp
    ring
  rw [he,one_div_div]

theorem reciprocal_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1/(1+2*max a b) = min (1/(1+2*a)) (1/(1+2*b)) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,min_eq_right]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · rw [max_eq_left h,min_eq_left]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Far-only receipt. The geometry hypothesis here is an internal composition
interface; the raw geometric public theorems below supply every witness. -/
theorem single_far_receipt (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    {r ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ q ∈ V, LocalInterval (farHeight o c q) (x o c q) r 0 ρ) :
    ENNReal.ofReal (1/(1+2*ρ))*mass V ≤
      physicalLength (centeredCoordinateEnvelope o G) r := by
  classical
  have hi : ∀ i : EligibleLabel V (∅ : Set ℝ),
      ∃ a b : ℝ, a ≤ b ∧ a-ρ*(b-a) ≤ eligibleAngle V ∅ (A o c) i ∧
        eligibleAngle V ∅ (A o c) i ≤ b+ρ*(b-a) ∧
        ∀ θ ∈ Icc a b, polarPoint r θ ∈ sourcePlane o ⁻¹' G := by
    intro i
    cases i with
    | inl q =>
      obtain ⟨a,b,hab,hl,hr,hp⟩ := (hw q q.property).at (farAngle o c q)
      refine ⟨a,b,hab,by simpa [eligibleAngle,farAngle] using hl,
        by simpa [eligibleAngle,farAngle] using hr,?_⟩
      intro θ hθ
      apply hG q q.property
      rw [triangle_eq_support_image]
      exact ⟨polarPoint r θ,hp θ hθ,rfl⟩
    | inr q => exact q.property.elim
  choose a b hab hl hr hp using hi
  have H := eligible_physical_section_receipt hV MeasurableSet.empty
    (measurableSet_A o hc) hchart (empty_subset V) ρ hρ a b hab hl hr
    (sourcePlane o ⁻¹' G) r hp
  simp only [image_empty,measure_empty,add_zero] at H
  have := reciprocal_receipt hρ H
  simpa only [mass,source_preimage_eq_centered,physicalLength,Measure.toOuterMeasure_apply] using this

/-- Genuine low eligible section minorant; V is any Borel low subfamily. -/
theorem low_section (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 0 < r) (hrmax : r < 2/5) :
    ENNReal.ofReal (k4 r)*(mass V+mass (V ∩ B o c)) ≤
      physicalLength (centeredCoordinateEnvelope o G) r := by
  classical
  let ρ : ℝ := max (1/4) (r/(2/5-r))
  have hρ : 0 ≤ ρ := (by norm_num : (0:ℝ) ≤ 1/4).trans (le_max_left _ _)
  have hi : ∀ i : EligibleLabel V (V ∩ B o c),
      IntervalAt (farAngle o c (labelDirection V o c i))
        (farHeight o c (labelDirection V o c i)) (x o c (labelDirection V o c i)) r
        (eligibleAngle V (V ∩ B o c) (A o c) i) ρ := by
    intro i
    cases i with
    | inl q =>
      have hx := low_x_bounds o c (hVL q.property)
      have hM : 2/5 ≤ endpointRadius |farHeight o c q| (x o c q) := by
        rw [source_far_radius]
        linarith [half_le_M o c q]
      have H := (low_far (hh q q.property) hx.1 (by linarith [hx.2.1]) hr hrmax hM).at
        (farAngle o c q)
      simpa only [labelDirection,Sum.elim_inl,eligibleAngle,farAngle,add_zero] using H
    | inr q =>
      have hx := low_x_bounds o c (hVL q.property.1)
      have hM : 2/5 ≤ endpointRadius |farHeight o c q| (x o c q) := by
        rw [source_far_radius]
        linarith [half_le_M o c q]
      have hN : 2/5 ≤ endpointRadius |farHeight o c q| (1-x o c q) := by
        rw [source_near_radius]
        exact q.property.2
      have H := (low_near (hh q q.property.1) hx.1 (by linarith [hx.2.1]) hr hrmax hM hN).at_opposite
        (A o c) q
      simpa only [labelDirection,Sum.elim_inr,eligibleAngle,farAngle] using H
  choose a b hab hl hr' hp using hi
  have H := actual_support_section_receipt o hc hV (fun q hq => (hVL hq).1)
    G hG r ρ hρ a b hab hl hr' hp
  have H' := reciprocal_receipt hρ H
  have hk : 1/(1+2*ρ) = k4 r := by
    dsimp only [ρ]
    rw [reciprocal_max (by norm_num) (div_nonneg hr.le (sub_pos.mpr hrmax).le),
      reciprocal_ratio hr.le hrmax]
    norm_num [k4]
  simpa only [hk,mass,source_preimage_eq_centered,physicalLength,Measure.toOuterMeasure_apply] using H'

/-- General bounded M/h single-far kernel, retaining external feet and all seams. -/
theorem bounded_section (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hchart : V ⊆ chart)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    {r m R H : ℝ} (hH : H ≤ 1/2) (hRH : H < R)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ H)
    (hMR : ∀ q ∈ V, M o c q ≤ R) (hmM : ∀ q ∈ V, m ≤ M o c q)
    (hr : 0 < r) (hrm : r < m) :
    ENNReal.ofReal (min (K R H) ((m-r)/(m+r)))*mass V ≤
      physicalLength (centeredCoordinateEnvelope o G) r := by
  have hρ : 0 ≤ max (coneBudget R H) (r/(m-r)) :=
    (coneBudget_nonneg R H).trans (le_max_left _ _)
  have H' := single_far_receipt o hc hV hchart G hG hρ (r := r) (fun q hq =>
    bounded_far (hh q hq) hH (by unfold x; linarith [abs_nonneg (longitudinal o c q)])
      hRH (by rw [source_far_radius]; exact hMR q hq) hr hrm
      (by rw [source_far_radius]; exact hmM q hq))
  rw [reciprocal_max (coneBudget_nonneg R H) (div_nonneg hr.le (sub_pos.mpr hrm).le),
    reciprocal_ratio hr.le hrm] at H'
  exact H'

/-- Common single-far low subfamily kernel, including r=|h|. -/
theorem mid_section_kernel (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    {r m : ℝ} (hh : ∀ q ∈ V, |farHeight o c q| ≤ r)
    (hmM : ∀ q ∈ V, m ≤ M o c q) (hr : 0 < r) (hrm : r < m) :
    ENNReal.ofReal ((m-r)/(m+r))*mass V ≤
      physicalLength (centeredCoordinateEnvelope o G) r := by
  have H := single_far_receipt o hc hV (fun q hq => (hVL hq).1) G hG
    (div_nonneg hr.le (sub_pos.mpr hrm).le) (r := r) (fun q hq =>
      mid_far (hh q hq) (low_x_bounds o c (hVL hq)).1
        (by linarith [(low_x_bounds o c (hVL hq)).2.1]) hr hrm
        (by rw [source_far_radius]; exact hmM q hq))
  rwa [reciprocal_ratio hr.le hrm] at H

theorem mid_section (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 1/5 ≤ r) (hrmax : r < 1/2) :
    ENNReal.ofReal (k5 r)*mass V ≤ physicalLength (centeredCoordinateEnvelope o G) r := by
  exact mid_section_kernel o hc hV hVL G hG (fun q hq => (hh q hq).trans hr)
    (fun q _ => half_le_M o c q) (by linarith) hrmax

/-- U(V)=V\\B; no opposite labels are passed to the circle receipt. -/
theorem outer_section (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5)
    {r : ℝ} (hr : 1/5 ≤ r) (hrmax : r < 3/5) :
    ENNReal.ofReal (k6 r)*mass (V \ B o c) ≤
      physicalLength (centeredCoordinateEnvelope o G) r := by
  exact mid_section_kernel o hc (hV.diff (measurableSet_B o hc))
    (fun q hq => hVL hq.1) G (fun q hq => hG q hq.1)
    (fun q hq => (hh q hq.1).trans hr)
    (fun q hq => (U_far_radius_gt o c ⟨hVL hq.1,hq.2⟩).le) (by linarith) hrmax

end
end StarKakeyaLower.OneTenth.SectionBounds
