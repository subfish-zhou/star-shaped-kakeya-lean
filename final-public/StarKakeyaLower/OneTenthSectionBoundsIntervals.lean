import StarKakeyaLower.OneTenthLobesPhysical
import StarKakeyaLower.OneTenthCapsEndpoints

/-! Real closed interval witnesses in the original signed support triangle.
No interval measurability, angular inequality, or area premise is assumed. -/
open Set Real
namespace StarKakeyaLower.OneTenth.SectionBounds
noncomputable section

/-- Local real lifts; the last field is literal pointwise physical membership. -/
def LocalInterval (h p r t ρ : ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ a-ρ*(b-a) ≤ t ∧ t ≤ b+ρ*(b-a) ∧
    ∀ α φ : ℝ, φ ∈ Icc a b →
      polarPoint r (α+φ) ∈ supportNeedleTriangle α h (p-1/2)

theorem LocalInterval.mono {h p r t ρ σ : ℝ}
    (H : LocalInterval h p r t ρ) (hρσ : ρ ≤ σ) : LocalInterval h p r t σ := by
  obtain ⟨a,b,hab,hl,hr,hp⟩ := H
  have := mul_le_mul_of_nonneg_right hρσ (sub_nonneg.mpr hab)
  exact ⟨a,b,hab,by linarith,by linarith,hp⟩

/-- Negating the local angle changes the signed height, not the physical set. -/
theorem LocalInterval.neg {h p r t ρ : ℝ}
    (H : LocalInterval h p r t ρ) : LocalInterval (-h) p r (-t) ρ := by
  obtain ⟨a,b,hab,hl,hr,hp⟩ := H
  refine ⟨-b,-a,by linarith,by nlinarith,by nlinarith,?_⟩
  intro α φ hφ
  have H := (signed_section_iff α h (p-1/2) r (-φ)).mpr
    (hp α (-φ) ⟨by linarith [hφ.2],by linarith [hφ.1]⟩)
  simpa only [sub_neg_eq_add] using H

theorem polarPoint_add_turn (r θ : ℝ) :
    polarPoint r (θ+2*Real.pi) = polarPoint r θ := by
  ext <;> simp [polarPoint,scaleCoordinatePlane,unitDirection,Real.cos_add,Real.sin_add]

theorem polarPoint_sub_turn (r θ : ℝ) :
    polarPoint r (θ-2*Real.pi) = polarPoint r θ := by
  simpa only [sub_add_cancel] using (polarPoint_add_turn r (θ-2*Real.pi)).symm

/-- A real full-turn shift preserves every physical polar point. -/
theorem LocalInterval.add_turn {h p r t ρ : ℝ}
    (H : LocalInterval h p r t ρ) : LocalInterval h p r (t+2*Real.pi) ρ := by
  obtain ⟨a,b,hab,hl,hr,hp⟩ := H
  refine ⟨a+2*Real.pi,b+2*Real.pi,by linarith,by nlinarith,by nlinarith,?_⟩
  intro α φ hφ
  have H := hp α (φ-2*Real.pi) ⟨by linarith [hφ.1],by linarith [hφ.2]⟩
  rw [show α+(φ-2*Real.pi) = (α+φ)-2*Real.pi by ring,
    polarPoint_sub_turn] at H
  exact H

theorem LocalInterval.sub_turn {h p r t ρ : ℝ}
    (H : LocalInterval h p r t ρ) : LocalInterval h p r (t-2*Real.pi) ρ := by
  obtain ⟨a,b,hab,hl,hr,hp⟩ := H
  refine ⟨a-2*Real.pi,b-2*Real.pi,by linarith,by nlinarith,by nlinarith,?_⟩
  intro α φ hφ
  have H := hp α (φ+2*Real.pi) ⟨by linarith [hφ.1],by linarith [hφ.2]⟩
  rw [show α+(φ+2*Real.pi) = (α+φ)+2*Real.pi by ring,
    polarPoint_add_turn] at H
  exact H

theorem zero_far {p r ρ : ℝ} (hr : 0 < r) (hrp : r ≤ p) :
    LocalInterval 0 p r 0 ρ := by
  refine ⟨0,0,le_rfl,by simp,by simp,?_⟩
  intro α φ hφ
  have hφ0 : φ=0 := le_antisymm hφ.2 hφ.1
  subst φ
  exact (zero_height_section_iff hr ⟨le_rfl,Real.pi_pos.le⟩).mpr (Or.inl ⟨rfl,hrp⟩)

theorem zero_near {p r ρ : ℝ} (hr : 0 < r) (hrp : r ≤ 1-p) :
    LocalInterval 0 p r Real.pi ρ := by
  refine ⟨Real.pi,Real.pi,le_rfl,by simp,by simp,?_⟩
  intro α φ hφ
  have hφ0 : φ=Real.pi := le_antisymm hφ.2 hφ.1
  subst φ
  exact (zero_height_section_iff hr ⟨Real.pi_pos.le,le_rfl⟩).mpr (Or.inr ⟨rfl,hrp⟩)

/-- Upper-side full cone, valid also with an external foot. -/
theorem cone_far {h p r ρ : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hrh : r ≤ h) (hρ : 0 ≤ ρ)
    (hcap : endpointAngle h p ≤ ρ*(endpointAngle h (p-1)-endpointAngle h p)) :
    LocalInterval h p r 0 ρ := by
  have hab := ((endpointAngle_strictAnti hh) (by linarith : p-1<p)).le
  have hlen := mul_nonneg hρ (sub_nonneg.mpr hab)
  refine ⟨endpointAngle h p,endpointAngle h (p-1),hab,by linarith,
    by linarith [endpointAngle_pos h (p-1)],?_⟩
  intro α φ hφ
  exact (full_cone_iff hh hr hrh
    ⟨(endpointAngle_pos h p).le.trans hφ.1,
      hφ.2.trans (endpointAngle_lt_pi h (p-1)).le⟩).mpr hφ

/-- Internal-foot far lobe with its actual complete interval. -/
theorem internal_far {h p r m ρ : ℝ} (hh : 0 < h) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) (hhr : h < r) (hrm : r < m)
    (hm : m ≤ endpointRadius h p) (hρ : r/(m-r) ≤ ρ) :
    LocalInterval h p r 0 ρ := by
  have H := far_lobe_receipt (α := 0) hh hp (by linarith : 0 ≤ 1-p)
    (by ring : p+(1-p)=1) hhr hrm hm
  have he := (div_le_iff₀ H.2.1).mp (H.2.2.trans hρ)
  have ha := endpointAngle_pos h p
  have hb : 0 < Real.arcsin (h/r) := by linarith [H.2.1]
  refine ⟨endpointAngle h p,Real.arcsin (h/r),by linarith [H.2.1],
    by linarith,by nlinarith,?_⟩
  intro α φ hφ
  exact (far_lobe_receipt (α := α) hh hp (by linarith : 0 ≤ 1-p)
    (by ring : p+(1-p)=1) hhr hrm hm).1 ⟨φ,hφ,rfl⟩

theorem internal_near {h p r m ρ : ℝ} (hh : 0 < h) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) (hhr : h < r) (hrm : r < m)
    (hm : m ≤ endpointRadius h (1-p)) (hρ : r/(m-r) ≤ ρ) :
    LocalInterval h p r Real.pi ρ := by
  have H := near_lobe_receipt (α := 0) hh hp (by linarith : 0 ≤ 1-p)
    (by ring : p+(1-p)=1) hhr hrm hm
  have he := (div_le_iff₀ H.2.1).mp (H.2.2.trans hρ)
  have ha := endpointAngle_pos h (1-p)
  refine ⟨Real.pi-Real.arcsin (h/r),Real.pi-endpointAngle h (1-p),
    by linarith [H.2.1],?_,?_,?_⟩
  · nlinarith [H.2.1]
  · nlinarith
  · intro α φ hφ
    exact (near_lobe_receipt (α := α) hh hp (by linarith : 0 ≤ 1-p)
      (by ring : p+(1-p)=1) hhr hrm hm).1 ⟨φ,hφ,rfl⟩

/-- Low cone or lobe, far label; no eligibility is needed for the far cap. -/
theorem low_positive_far {h p r : ℝ} (hh : 0 < h) (hhmax : h ≤ 1/5)
    (hp : 1/2 ≤ p) (hp1 : p ≤ 1) (hr : 0 < r) (hrmax : r < 2/5)
    (hM : 2/5 ≤ endpointRadius h p) :
    LocalInterval h p r 0 (max (1/4) (r/(2/5-r))) := by
  by_cases hhr : h < r
  · exact internal_far hh (by linarith) hp1 hhr hrmax hM (le_max_right _ _)
  · have hc := low_far_cone_cap hh hhmax hp (by linarith : 0 ≤ 1-p)
      (by ring : p+(1-p)=1)
    have hc' : endpointAngle h p ≤ (1/4)*(endpointAngle h (p-1)-endpointAngle h p) := by
      rw [show p-1 = -(1-p) by ring,endpointAngle_neg]
      linarith
    exact (cone_far hh hr (le_of_not_gt hhr) (by norm_num) hc').mono (le_max_left _ _)

/-- Low eligible near label uses the same cone, not a second reflected hull. -/
theorem low_positive_near {h p r : ℝ} (hh : 0 < h) (hhmax : h ≤ 1/5)
    (hp : 1/2 ≤ p) (hp1 : p ≤ 1) (hr : 0 < r) (hrmax : r < 2/5)
    (hM : 2/5 ≤ endpointRadius h p) (hN : 2/5 ≤ endpointRadius h (1-p)) :
    LocalInterval h p r Real.pi (max (1/4) (r/(2/5-r))) := by
  by_cases hhr : h < r
  · exact internal_near hh (by linarith) hp1 hhr hrmax hN (le_max_right _ _)
  · apply LocalInterval.mono (ρ := 1/4) _ (le_max_left _ _)
    have H := eligible_near_full_cone_receipt (α := 0) hh hhmax hp
      (by linarith : 0 ≤ 1-p) (by ring : p+(1-p)=1) hr (le_of_not_gt hhr) hM hN
    have hab : endpointAngle h p < Real.pi-endpointAngle h (1-p) := by
      have := (endpointAngle_strictAnti hh) (by linarith : p-1<p)
      rw [show p-1 = -(1-p) by ring,endpointAngle_neg] at this
      exact this
    refine ⟨endpointAngle h p,Real.pi-endpointAngle h (1-p),hab.le,?_,?_,?_⟩
    · linarith [endpointAngle_lt_pi h p]
    · linarith [H.2]
    · intro α φ hφ
      exact (eligible_near_full_cone_receipt (α := α) hh hhmax hp
        (by linarith : 0 ≤ 1-p) (by ring : p+(1-p)=1) hr (le_of_not_gt hhr) hM hN).1
        ⟨φ,hφ,rfl⟩

/-- Transfer an upper-side far witness to either original signed side. -/
theorem signed_far {h p r ρ : ℝ} (H : LocalInterval |h| p r 0 ρ) :
    LocalInterval h p r 0 ρ := by
  rcases le_total 0 h with hh | hh
  · simpa only [abs_of_nonneg hh] using H
  · have H' := H.neg
    simpa only [abs_of_nonpos hh,neg_neg,neg_zero] using H'

/-- The negative-side near anchor is shifted from -π to +π by a full turn. -/
theorem signed_near {h p r ρ : ℝ} (H : LocalInterval |h| p r Real.pi ρ) :
    LocalInterval h p r Real.pi ρ := by
  rcases le_total 0 h with hh | hh
  · simpa only [abs_of_nonneg hh] using H
  · have H' := H.neg.add_turn
    rw [show -Real.pi+2*Real.pi=Real.pi by ring] at H'
    simpa only [abs_of_nonpos hh,neg_neg] using H'

theorem endpointRadius_zero {p : ℝ} (hp : 0 ≤ p) : endpointRadius 0 p = p := by
  simp [endpointRadius,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

/-- Low far witness, including genuine zero-height singleton rays. -/
theorem low_far {h p r : ℝ} (hh : |h| ≤ 1/5) (hp : 1/2 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 < r) (hrmax : r < 2/5) (hM : 2/5 ≤ endpointRadius |h| p) :
    LocalInterval h p r 0 (max (1/4) (r/(2/5-r))) := by
  apply signed_far
  rcases (abs_nonneg h).eq_or_lt with hz | hz
  · rw [← hz]
    apply zero_far hr
    rw [← hz,endpointRadius_zero (by linarith : 0 ≤ p)] at hM
    linarith
  · exact low_positive_far hz hh hp hp1 hr hrmax hM

theorem low_near {h p r : ℝ} (hh : |h| ≤ 1/5) (hp : 1/2 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 < r) (hrmax : r < 2/5) (hM : 2/5 ≤ endpointRadius |h| p)
    (hN : 2/5 ≤ endpointRadius |h| (1-p)) :
    LocalInterval h p r Real.pi (max (1/4) (r/(2/5-r))) := by
  apply signed_near
  rcases (abs_nonneg h).eq_or_lt with hz | hz
  · rw [← hz]
    apply zero_near hr
    rw [← hz,endpointRadius_zero (by linarith : 0 ≤ 1-p)] at hN
    linarith
  · exact low_positive_near hz hh hp hp1 hr hrmax hM hN

/-- Single-far internal lobe bank, including the closed height seam. -/
theorem mid_far {h p r m : ℝ} (hh : |h| ≤ r) (hp : 1/2 ≤ p) (hp1 : p < 1)
    (hr : 0 < r) (hrm : r < m) (hM : m ≤ endpointRadius |h| p) :
    LocalInterval h p r 0 (r/(m-r)) := by
  apply signed_far
  rcases (abs_nonneg h).eq_or_lt with hz | hz
  · rw [← hz]
    apply zero_far hr
    rw [← hz,endpointRadius_zero (by linarith : 0 ≤ p)] at hM
    linarith
  · rcases hh.lt_or_eq with hh | hh
    · exact internal_far hz (by linarith) hp1.le hh hrm hM le_rfl
    · -- At r=h the entire first half-cone is physical, with the exact gap.
      have hlt : endpointAngle |h| p < Real.pi/2 := by
        unfold endpointAngle
        have := Real.arctan_pos.mpr (div_pos (by linarith : 0<p) hz)
        linarith
      have hgap : endpointAngle |h| p ≤ r/(m-r)*(Real.pi/2-endpointAngle |h| p) := by
        have hs := Real.mul_le_sin (endpointAngle_pos |h| p).le
          (endpointAngle_le_half hz (by linarith : 0 ≤ p))
        rw [endpointAngle_sin hz] at hs
        have hRp := endpointRadius_pos (x := p) hz
        have hs' := (le_div_iff₀ hRp).mp hs
        have hs'' := mul_le_mul_of_nonneg_right hs' Real.pi_pos.le
        have heq : (2/Real.pi*endpointAngle |h| p*endpointRadius |h| p)*Real.pi =
            2*endpointAngle |h| p*endpointRadius |h| p := by
          field_simp
        rw [heq] at hs''
        have hs''' := hs''.trans_eq (congrArg (fun z : ℝ => z*Real.pi) hh)
        have hmp := mul_le_mul_of_nonneg_left hM (endpointAngle_pos |h| p).le
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (sub_pos.mpr hrm)).mpr
        nlinarith
      refine ⟨endpointAngle |h| p,Real.pi/2,hlt.le,by linarith,?_,?_⟩
      · have : 0 ≤ r/(m-r) := div_nonneg hr.le (sub_pos.mpr hrm).le
        have := mul_nonneg this (sub_nonneg.mpr hlt.le)
        linarith [Real.pi_pos]
      · intro α φ hφ
        apply (full_cone_iff hz hr (by linarith)
          ⟨(endpointAngle_pos |h| p).le.trans hφ.1,by linarith [hφ.2,Real.pi_pos]⟩).mpr
        refine ⟨hφ.1,?_⟩
        rw [show p-1 = -(1-p) by ring,endpointAngle_neg]
        linarith [endpointAngle_le_half hz (by linarith : 0 ≤ 1-p),hφ.2]

end
end StarKakeyaLower.OneTenth.SectionBounds
