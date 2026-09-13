import StarKakeyaLower.OneTenthCircleLifts

/-!
# Eligible endpoint anchors: the source-once circle receipt

Labels are the disjoint sum of all far directions and eligible near directions.
The actual target is ONE union of closed arcs on `AddCircle (2π)`. In particular,
the two labels of a full cone may carry identical intervals; they are not paid
twice. Triangle-specific construction of those arcs is a downstream obligation.
-/

open Set MeasureTheory

namespace StarKakeyaLower.OneTenth
noncomputable section

open Classical in
/-- A real representative of a Borel chosen physical lift. -/
def selectedAngle (A : Set ℝ) (t : ℝ) : ℝ := if t ∈ A then t else Real.pi+t

/-- All far labels plus exactly the eligible near labels. -/
abbrev EligibleLabel (V B : Set ℝ) := V ⊕ B

/-- The near anchor is the opposite physical lift, not a second copy of the
chosen far anchor. -/
def eligibleAngle (V B A : Set ℝ) : EligibleLabel V B → ℝ :=
  Sum.elim (fun t => selectedAngle A t) (fun t => selectedAngle Aᶜ t)

theorem chosenLift_eq_range (V A : Set ℝ) :
    chosenLift V A = Set.range (fun t : V => (selectedAngle A t : PolarAngle)) := by
  classical
  ext q
  constructor
  · rintro (⟨t,ht,hq⟩ | ⟨t,ht,hq⟩)
    · exact ⟨⟨t,ht.1⟩, by simpa [selectedAngle, ht.2] using hq⟩
    · exact ⟨⟨t,ht.1⟩, by simpa [selectedAngle, ht.2] using hq⟩
  · rintro ⟨t,rfl⟩
    by_cases ht : (t : ℝ) ∈ A
    · exact Or.inl ⟨t, ⟨t.property,ht⟩, by simp [selectedAngle,ht]⟩
    · exact Or.inr ⟨t, ⟨t.property,ht⟩, by simp [selectedAngle,ht]⟩

theorem eligibleAngle_range (V B A : Set ℝ) :
    Set.range (fun i => (eligibleAngle V B A i : PolarAngle)) =
      chosenLift V A ∪ oppositeLift B A := by
  rw [oppositeLift_eq_chosen, chosenLift_eq_range, chosenLift_eq_range]
  ext q
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl t => exact Or.inl ⟨t,hi⟩
    | inr t => exact Or.inr ⟨t,hi⟩
  · rintro (⟨t,ht⟩ | ⟨t,ht⟩)
    · exact ⟨Sum.inl t,ht⟩
    · exact ⟨Sum.inr t,ht⟩

/-- Dependency-ready eligible-anchor circle theorem. The only nontrivial
geometric inputs are real bounds placing each ideal anchor within the allowed
extension of its actual interval. No angular/area inequality is a hypothesis.
No regularity or positive-length assumption is imposed on the arc family. -/
theorem eligible_circle_union_receipt {V B A : Set ℝ}
    (hV : MeasurableSet V) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (hchart : V ⊆ Ioc 0 Real.pi) (hBV : B ⊆ V)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : EligibleLabel V B → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hleft : ∀ i, a i - ρ*(b i-a i) ≤ eligibleAngle V B A i)
    (hright : ∀ i, eligibleAngle V B A i ≤ b i + ρ*(b i-a i)) :
    volume ((fun t : ℝ => (t : ProjectiveDirection)) '' V) +
      volume ((fun t : ℝ => (t : ProjectiveDirection)) '' B) ≤
        ENNReal.ofReal (1+2*ρ) * volume.toOuterMeasure (⋃ i, polarArc (a i) (b i)) := by
  rw [← eligible_lift_length hV hB hA hchart hBV, ← eligibleAngle_range]
  exact physical_anchor_receipt ρ hρ a b (eligibleAngle V B A)
    (⋃ i, polarArc (a i) (b i)) hab hleft hright (fun i => subset_iUnion (fun j => polarArc (a j) (b j)) i)

/-- Quotient physical section, defined using an actual real polar-point witness.
The existential lift does not identify antipodal points. -/
def physicalSection (W : Set CoordinatePlane) (r : ℝ) : Set PolarAngle :=
  {q | ∃ θ : ℝ, (θ : PolarAngle) = q ∧ polarPoint r θ ∈ W}

/-- The existential quotient definition is exactly the ordinary polar section
at every real representative; full-turn changes do not change the point. -/
@[simp] theorem mem_physicalSection_coe (W : Set CoordinatePlane) (r θ : ℝ) :
    (θ : PolarAngle) ∈ physicalSection W r ↔ polarPoint r θ ∈ W := by
  constructor
  · rintro ⟨φ,hφ,hw⟩
    rwa [polarPoint_eq_of_polar_coe_eq hφ] at hw
  · intro h
    exact ⟨θ,rfl,h⟩

/-- An interval of real polar points gives a literal closed quotient arc in the
physical section, including the singleton and both endpoints. -/
theorem polarArc_subset_physicalSection {W : Set CoordinatePlane} {r a b : ℝ}
    (h : ∀ θ ∈ Icc a b, polarPoint r θ ∈ W) :
    polarArc a b ⊆ physicalSection W r := by
  rw [polarArc, closedInterval_eq_image]
  rintro q ⟨θ,hθ,hq⟩
  exact ⟨θ,hq,h θ hθ⟩

/-- The same receipt for an actual fixed-radius section. To apply this to the
integrated-low proof one must construct the full cone/lobes in each actual
triangle and verify `hpoints`, `hleft`, `hright`; they are not asserted here. -/
theorem eligible_physical_section_receipt {V B A : Set ℝ}
    (hV : MeasurableSet V) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (hchart : V ⊆ Ioc 0 Real.pi) (hBV : B ⊆ V)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : EligibleLabel V B → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hleft : ∀ i, a i - ρ*(b i-a i) ≤ eligibleAngle V B A i)
    (hright : ∀ i, eligibleAngle V B A i ≤ b i + ρ*(b i-a i))
    (W : Set CoordinatePlane) (r : ℝ)
    (hpoints : ∀ i θ, θ ∈ Icc (a i) (b i) → polarPoint r θ ∈ W) :
    volume ((fun t : ℝ => (t : ProjectiveDirection)) '' V) +
      volume ((fun t : ℝ => (t : ProjectiveDirection)) '' B) ≤
        ENNReal.ofReal (1+2*ρ) * volume.toOuterMeasure (physicalSection W r) := by
  exact (eligible_circle_union_receipt hV hB hA hchart hBV ρ hρ a b hab hleft hright).trans
    (mul_le_mul_left' (measure_mono (iUnion_subset fun i =>
      polarArc_subset_physicalSection (hpoints i))) _)

#print axioms eligible_circle_union_receipt
#print axioms eligible_physical_section_receipt

end
end StarKakeyaLower.OneTenth
