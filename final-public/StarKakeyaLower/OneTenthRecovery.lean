import StarKakeyaLower.TriangleArea

/-!
# Open-cover preparation for the one-tenth proof

This file proves genuine geometric/topological reductions. The open-cover
lower-bound implication is explicitly conditional; no low-bank estimate is
assumed to be a theorem about Kakeya sets.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace StarKakeyaLower.OneTenth
noncomputable section

/-- A fixed compact square parameterizes the entire filled triangle. -/
def trianglePoint (o a b : Plane) (st : ℝ × ℝ) : Plane :=
  (1-st.1) • o + st.1 • ((1-st.2) • a + st.2 • b)

def parameterSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

theorem parameterSquare_isCompact : IsCompact parameterSquare :=
  isCompact_Icc.prod isCompact_Icc

theorem triangleHull_eq_square_image (o : Plane) (n : UnitNeedle) :
    n.triangleHull o = trianglePoint o n.left n.right '' parameterSquare := by
  ext y
  simp only [UnitNeedle.triangleHull, UnitNeedle.carrier, mem_iUnion]
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [segment_eq_image] at hx hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨(s,t), ⟨hs,ht⟩, rfl⟩
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
    refine ⟨(1-t) • n.left + t • n.right, ?_, ?_⟩
    · rw [segment_eq_image]
      exact ⟨t, ht, rfl⟩
    · rw [segment_eq_image]
      exact ⟨s, hs, rfl⟩

/-- Admissible endpoint pairs form an open set: the whole triangle, not merely
its three vertices, must lie in the open cover. -/
def admissibleEndpoints (o : Plane) (G : Set Plane) : Set (Plane × Plane) :=
  {ab | ∀ st ∈ parameterSquare, trianglePoint o ab.1 ab.2 st ∈ G}

theorem isOpen_admissibleEndpoints (o : Plane) {G : Set Plane} (hG : IsOpen G) :
    IsOpen (admissibleEndpoints o G) := by
  rw [isOpen_iff_mem_nhds]
  intro ab hab
  apply parameterSquare_isCompact.eventually_forall_of_forall_eventually
  intro st hst
  have hc : Continuous (fun p : (Plane × Plane) × (ℝ × ℝ) =>
      trianglePoint o p.1.1 p.1.2 p.2) := by
    unfold trianglePoint
    fun_prop
  exact hc.continuousAt.preimage_mem_nhds (hG.mem_nhds (hab st hst))

theorem triangleHull_subset_iff_admissible (o : Plane) (n : UnitNeedle) (G : Set Plane) :
    n.triangleHull o ⊆ G ↔ (n.left,n.right) ∈ admissibleEndpoints o G := by
  rw [triangleHull_eq_square_image]
  exact image_subset_iff

/-- Post-recovery high-height branch. The ambient open set need not be star
shaped, and the needle need not belong to the original selector. -/
theorem one_tenth_le_of_triangle_height {G : Set Plane} {o : Plane} (n : UnitNeedle)
    (hsub : n.triangleHull o ⊆ G) (hh : (1/5 : ℝ) ≤ n.height o) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure G := by
  calc
    ENNReal.ofReal (1/10 : ℝ) ≤ ENNReal.ofReal (n.height o / 2) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ volume.toOuterMeasure (n.triangleHull o) := triangleAreaBridge o n
    _ ≤ volume.toOuterMeasure G := measure_mono hsub

/-- The original-selector high branch has no unproved area bridge. -/
theorem one_tenth_le_of_selected_height {E : Set Plane} (K : StarShapedKakeya E)
    {θ : Direction} (hh : (1/5 : ℝ) ≤ (K.needleFamily θ).height K.center) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure E :=
  one_tenth_le_of_triangle_height (K.needleFamily θ) (K.triangleHull_subset θ) hh

/-- An outer-regularity reduction, NOT an unconditional Kakeya theorem.
The open-cover bound is an explicit remaining premise. -/
theorem one_tenth_outer_of_open_covers (E : Set Plane)
    (h : ∀ G : Set Plane, E ⊆ G → IsOpen G →
      ENNReal.ofReal (1/10 : ℝ) ≤ volume G) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure E := by
  rw [Measure.toOuterMeasure_apply, E.measure_eq_iInf_isOpen volume]
  exact le_iInf fun G => le_iInf fun hEG => le_iInf fun hG => h G hEG hG

/-- Any continuous family of endpoint pairs inherits the proved open-cover
stability. This is a useful interface for midpoint-fixed angular families. -/
theorem isOpen_admissible_parameter {X : Type*} [TopologicalSpace X]
    (o : Plane) {G : Set Plane} (hG : IsOpen G) (a b : X → Plane)
    (ha : Continuous a) (hb : Continuous b) :
    IsOpen {t | ∀ st ∈ parameterSquare, trianglePoint o (a t) (b t) st ∈ G} :=
  (isOpen_admissibleEndpoints o hG).preimage (ha.prodMk hb)

/-- Compactness supplies finitely many *families*, not finitely many directions
or triangles. No measurable selector is postulated in this theorem. -/
theorem finite_admissible_families {X ι : Type*} [TopologicalSpace X]
    (S : Set X) (hS : IsCompact S) (o : Plane) {G : Set Plane} (hG : IsOpen G)
    (a b : ι → X → Plane) (ha : ∀ i, Continuous (a i)) (hb : ∀ i, Continuous (b i))
    (hcover : ∀ t ∈ S, ∃ i, ∀ st ∈ parameterSquare,
      trianglePoint o (a i t) (b i t) st ∈ G) :
    ∃ I : Finset ι, ∀ t ∈ S, ∃ i ∈ I, ∀ st ∈ parameterSquare,
      trianglePoint o (a i t) (b i t) st ∈ G := by
  classical
  let U : ι → Set X := fun i =>
    {t | ∀ st ∈ parameterSquare, trianglePoint o (a i t) (b i t) st ∈ G}
  obtain ⟨I, hI⟩ := hS.elim_finite_subcover U
    (fun i => isOpen_admissible_parameter o hG (a i) (b i) (ha i) (hb i))
    (by intro t ht; simpa [U] using hcover t ht)
  refine ⟨I, ?_⟩
  intro t ht
  simpa [U] using hI ht

/-- The orientation witness can use the specified real representative, rather
than only some unspecified lift of the projective direction. -/
theorem hasDirection_at_real (n : UnitNeedle) (t : ℝ)
    (h : n.HasDirection (t : Direction)) :
    ∃ c : ℝ, |c| = 1 ∧ n.right - n.left = c • angleVector t := by
  obtain ⟨u, hu, c, _hc, hd⟩ := h
  have hz : ((u-t : ℝ) : Direction) = 0 := by
    rw [AddCircle.coe_sub, hu, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff Real.pi).mp hz
  have hut : u = t + k * Real.pi := by
    simp only [zsmul_eq_mul] at hk
    linarith
  have hv : angleVector u = ((-1 : ℝ)^k) • angleVector t := by
    rw [hut]
    ext i
    fin_cases i <;>
      simp [angleVector, Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi]
  have heq : n.right - n.left = (c * (-1 : ℝ)^k) • angleVector t := by
    rw [hd, hv, smul_smul]
  refine ⟨c * (-1 : ℝ)^k, ?_, heq⟩
  have hn : ‖n.right - n.left‖ = 1 := by
    rw [← dist_eq_norm, dist_comm]
    exact n.unit_length
  simpa [heq, norm_smul, Real.norm_eq_abs] using hn

/-- A signed midpoint frame; its sign is fixed within each continuous family. -/
structure MidpointFrame where
  midpoint : Plane
  sign : ℝ
  abs_sign : |sign| = 1

namespace MidpointFrame

def left (F : MidpointFrame) (t : ℝ) : Plane :=
  F.midpoint - (1/2 : ℝ) • (F.sign • angleVector t)
def right (F : MidpointFrame) (t : ℝ) : Plane :=
  F.midpoint + (1/2 : ℝ) • (F.sign • angleVector t)

theorem right_sub_left (F : MidpointFrame) (t : ℝ) :
    F.right t - F.left t = F.sign • angleVector t := by
  unfold left right
  module

def needle (F : MidpointFrame) (t : ℝ) : UnitNeedle where
  left := F.left t
  right := F.right t
  unit_length := by
    rw [dist_comm, dist_eq_norm, right_sub_left, norm_smul, Real.norm_eq_abs,
      F.abs_sign, norm_angleVector, mul_one]

theorem needle_hasDirection (F : MidpointFrame) (t : ℝ) :
    (F.needle t).HasDirection (t : Direction) := by
  refine ⟨t, rfl, F.sign, ?_, F.right_sub_left t⟩
  intro h
  simpa [h] using F.abs_sign

theorem continuous_angleVector : Continuous angleVector := by
  unfold angleVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem continuous_left (F : MidpointFrame) : Continuous F.left := by
  unfold left
  exact continuous_const.sub (continuous_const.smul (continuous_const.smul continuous_angleVector))

theorem continuous_right (F : MidpointFrame) : Continuous F.right := by
  unfold right
  exact continuous_const.add (continuous_const.smul (continuous_const.smul continuous_angleVector))

end MidpointFrame

/-- Every original unit needle admits a midpoint-fixed frame at any real lift
of its projective direction. No regularity of the original choice is used. -/
theorem exists_midpointFrame (n : UnitNeedle) (t : ℝ)
    (h : n.HasDirection (t : Direction)) :
    ∃ F : MidpointFrame, (F.needle t).left = n.left ∧ (F.needle t).right = n.right := by
  obtain ⟨c, hc, hd⟩ := hasDirection_at_real n t h
  refine ⟨⟨(1/2 : ℝ) • (n.left+n.right), c, hc⟩, ?_, ?_⟩
  · change (1/2 : ℝ) • (n.left+n.right) - (1/2 : ℝ) • (c • angleVector t) = n.left
    rw [← hd]
    module
  · change (1/2 : ℝ) • (n.left+n.right) + (1/2 : ℝ) • (c • angleVector t) = n.right
    rw [← hd]
    module

/-- The actual Kakeya hypothesis supplies a finite collection of continuous
midpoint-fixed families covering every angle in [0,π] inside an arbitrary open
superset. This is not a finite-direction assumption. -/
theorem finite_midpoint_recovery {E G : Set Plane} (K : StarShapedKakeya E)
    (hEG : E ⊆ G) (hG : IsOpen G) :
    ∃ I : Finset MidpointFrame, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      ∃ F ∈ I, (F.needle t).triangleHull K.center ⊆ G := by
  classical
  have hcover : ∀ t ∈ Icc (0 : ℝ) Real.pi, ∃ F : MidpointFrame,
      ∀ st ∈ parameterSquare, trianglePoint K.center (F.left t) (F.right t) st ∈ G := by
    intro t _ht
    let n := K.needleFamily (t : Direction)
    obtain ⟨F, hleft, hright⟩ := exists_midpointFrame n t (K.needleFamily_hasDirection _)
    refine ⟨F, ?_⟩
    have hsub : (F.needle t).triangleHull K.center ⊆ G := by
      rw [triangleHull_eq_square_image, hleft, hright, ← triangleHull_eq_square_image]
      exact (K.triangleHull_subset (t : Direction)).trans hEG
    exact (triangleHull_subset_iff_admissible K.center (F.needle t) G).mp hsub
  obtain ⟨I, hI⟩ := finite_admissible_families (Icc (0 : ℝ) Real.pi) isCompact_Icc
    K.center hG MidpointFrame.left MidpointFrame.right
    MidpointFrame.continuous_left MidpointFrame.continuous_right hcover
  refine ⟨I, ?_⟩
  intro t ht
  obtain ⟨F, hF, hgood⟩ := hI t ht
  exact ⟨F, hF, (triangleHull_subset_iff_admissible K.center (F.needle t) G).mpr hgood⟩

open Classical in
/-- First-admissible-family selector. Its tests concern whole triangles. -/
def selectFrame (o : Plane) (G : Set Plane) (fallback : MidpointFrame) :
    List MidpointFrame → ℝ → MidpointFrame
  | [], _ => fallback
  | F :: Fs, t => if (F.left t, F.right t) ∈ admissibleEndpoints o G then F
      else selectFrame o G fallback Fs t

theorem selectFrame_mem (o : Plane) (G : Set Plane) (fallback : MidpointFrame)
    (Fs : List MidpointFrame) (t : ℝ) :
    selectFrame o G fallback Fs t ∈ fallback :: Fs := by
  classical
  induction Fs with
  | nil => simp [selectFrame]
  | cons F Fs ih =>
    simp only [selectFrame]
    split_ifs
    · simp
    · simpa only [List.mem_cons] using (by
        rcases List.mem_cons.mp ih with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h) :
        selectFrame o G fallback Fs t = fallback ∨
          selectFrame o G fallback Fs t = F ∨ selectFrame o G fallback Fs t ∈ Fs)

theorem selectFrame_good (o : Plane) (G : Set Plane) (fallback : MidpointFrame)
    (Fs : List MidpointFrame) (t : ℝ)
    (h : ∃ F ∈ Fs, (F.left t, F.right t) ∈ admissibleEndpoints o G) :
    ((selectFrame o G fallback Fs t).left t,
      (selectFrame o G fallback Fs t).right t) ∈ admissibleEndpoints o G := by
  classical
  induction Fs with
  | nil => simpa using h
  | cons F Fs ih =>
    simp only [selectFrame]
    split_ifs with hF
    · exact hF
    · apply ih
      obtain ⟨J, hJ, hgood⟩ := h
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact (hF hgood).elim
      · exact ⟨J, hJ, hgood⟩

theorem measurable_selectFrame_endpoints (o : Plane) {G : Set Plane} (hG : IsOpen G)
    (fallback : MidpointFrame) (Fs : List MidpointFrame) :
    Measurable (fun t => (selectFrame o G fallback Fs t).left t) ∧
      Measurable (fun t => (selectFrame o G fallback Fs t).right t) := by
  classical
  induction Fs with
  | nil => exact ⟨fallback.continuous_left.measurable, fallback.continuous_right.measurable⟩
  | cons F Fs ih =>
    have htest : MeasurableSet {t | (F.left t,F.right t) ∈ admissibleEndpoints o G} :=
      ((isOpen_admissibleEndpoints o hG).preimage
        (F.continuous_left.prodMk F.continuous_right)).measurableSet
    constructor
    · convert Measurable.ite htest F.continuous_left.measurable ih.1 using 1
      funext t
      simp only [selectFrame]
      split_ifs <;> rfl
      all_goals exact fun _ => Classical.propDecidable _
    · convert Measurable.ite htest F.continuous_right.measurable ih.2 using 1
      funext t
      simp only [selectFrame]
      split_ifs <;> rfl
      all_goals exact fun _ => Classical.propDecidable _

/-- Borel endpoints and a finite-valued midpoint are recovered from the literal
arbitrary-set Kakeya contract inside any open cover. The triangles remain a
continuum indexed by all real angles in [0,π]. -/
theorem measurable_midpoint_recovery {E G : Set Plane} (K : StarShapedKakeya E)
    (hEG : E ⊆ G) (hG : IsOpen G) :
    ∃ F : ℝ → MidpointFrame,
      (Set.range (fun t => (F t).midpoint)).Finite ∧
      Measurable (fun t => (F t).left t) ∧
      Measurable (fun t => (F t).right t) ∧
      ∀ t ∈ Icc (0 : ℝ) Real.pi,
        ((F t).needle t).HasDirection (t : Direction) ∧
        ((F t).needle t).triangleHull K.center ⊆ G := by
  classical
  obtain ⟨I,hI⟩ := finite_midpoint_recovery K hEG hG
  let fallback : MidpointFrame := ⟨0,1,by norm_num⟩
  let F : ℝ → MidpointFrame := selectFrame K.center G fallback I.toList
  have hm := measurable_selectFrame_endpoints K.center hG fallback I.toList
  refine ⟨F, ?_, hm.1, hm.2, ?_⟩
  · apply ((List.finite_toSet (fallback :: I.toList)).image MidpointFrame.midpoint).subset
    rintro _ ⟨t,rfl⟩
    exact ⟨F t, selectFrame_mem K.center G fallback I.toList t, rfl⟩
  · intro t ht
    refine ⟨(F t).needle_hasDirection t, ?_⟩
    apply (triangleHull_subset_iff_admissible K.center ((F t).needle t) G).mpr
    apply selectFrame_good
    obtain ⟨J,hJ,hgood⟩ := hI t ht
    exact ⟨J, by simpa using hJ,
      (triangleHull_subset_iff_admissible K.center (J.needle t) G).mp hgood⟩

end
end StarKakeyaLower.OneTenth
