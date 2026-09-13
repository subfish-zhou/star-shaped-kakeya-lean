import StarKakeyaLower.OneTenthLobesCones
import StarKakeyaLower.OneTenthRecovery

/-! # Literal endpoint-to-star-triangle bridge

This bridge uses the Euclidean `Plane`, `UnitNeedle`, and `triangleHull` of the
original arbitrary-set Kakeya contract. The coordinate endpoints are equations,
not a hypothesis that an angular lobe belongs to a set. Signed height and the
entire unit interval are preserved. Translation is applied to every point.
-/
open Set
namespace StarKakeyaLower.OneTenth
noncomputable section

/-- The canonical two-coordinate map, based at the actual star centre. -/
def lobePlane (o : Plane) (z : CoordinatePlane) : Plane :=
  o + WithLp.toLp 2 ![z.1,z.2]

@[simp] theorem lobePlane_zero (o : Plane) (z : CoordinatePlane) :
    lobePlane o z 0 = o 0 + z.1 := rfl
@[simp] theorem lobePlane_one (o : Plane) (z : CoordinatePlane) :
    lobePlane o z 1 = o 1 + z.2 := rfl

/-- Exact set equality between the existing support triangle and the actual
UnitNeedle hull, with arbitrary signed height. -/
theorem triangleHull_eq_lobePlane_image (o : Plane) (n : UnitNeedle)
    (α h c : ℝ)
    (hl : n.left = lobePlane o (supportPoint α h (c-1/2)))
    (hr : n.right = lobePlane o (supportPoint α h (c+1/2))) :
    n.triangleHull o = lobePlane o '' supportNeedleTriangle α h c := by
  rw [triangleHull_eq_square_image]
  ext y
  constructor
  · rintro ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩
    refine ⟨scaleCoordinatePlane s (supportPoint α h (c-1/2+t)),
      ⟨s,hs,c-1/2+t,⟨by linarith [ht.1],by linarith [ht.2]⟩,rfl⟩,?_⟩
    ext i
    fin_cases i <;>
      simp [trianglePoint,hl,hr,lobePlane,supportPoint,scaleCoordinatePlane,
        addCoordinatePlane,unitDirection,unitNormal] <;> ring
  · rintro ⟨_,⟨s,hs,x,hx,rfl⟩,rfl⟩
    refine ⟨(s,x-(c-1/2)),⟨hs,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩,?_⟩
    ext i
    fin_cases i <;>
      simp [trianglePoint,hl,hr,lobePlane,supportPoint,scaleCoordinatePlane,
        addCoordinatePlane,unitDirection,unitNormal] <;> ring

/-- Set-level physical bridge for any proved coordinate section. -/
theorem physical_section_subset (o : Plane) (n : UnitNeedle) (α h c r : ℝ)
    (A : Set ℝ)
    (hl : n.left = lobePlane o (supportPoint α h (c-1/2)))
    (hr : n.right = lobePlane o (supportPoint α h (c+1/2)))
    (hA : (fun φ => polarPoint r (α+φ)) '' A ⊆ supportNeedleTriangle α h c) :
    (fun φ => lobePlane o (polarPoint r (α+φ))) '' A ⊆ n.triangleHull o := by
  rw [triangleHull_eq_lobePlane_image o n α h c hl hr]
  rintro _ ⟨φ,hφ,rfl⟩
  exact ⟨polarPoint r (α+φ),hA ⟨φ,hφ,rfl⟩,rfl⟩

/-- Physical far-lobe receipt. There is no assumed section/area inequality. -/
theorem physical_far_lobe_receipt (o : Plane) (n : UnitNeedle)
    {α h p m r R₀ : ℝ}
    (hl : n.left = lobePlane o (supportPoint α h (p-1)))
    (hr : n.right = lobePlane o (supportPoint α h p))
    (hh : 0 < h) (hp : 0 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1)
    (hhr : h < r) (hrR : r < R₀) (hR : R₀ ≤ endpointRadius h p) :
    (fun φ => lobePlane o (polarPoint r (α+φ))) ''
        Icc (endpointAngle h p) (Real.arcsin (h/r)) ⊆ n.triangleHull o ∧
      0 < Real.arcsin (h/r)-endpointAngle h p ∧
      endpointAngle h p / (Real.arcsin (h/r)-endpointAngle h p) ≤ r/(R₀-r) := by
  have H := far_lobe_receipt (α := α) hh hp hm hunit hhr hrR hR
  refine ⟨physical_section_subset o n α h (p-1/2) r _ ?_ ?_ H.1,H.2⟩
  · convert hl using 1 <;> congr 2 <;> ring
  · convert hr using 1 <;> congr 2 <;> ring

/-- Physical eligible-near receipt in the very same actual triangle. -/
theorem physical_near_lobe_receipt (o : Plane) (n : UnitNeedle)
    {α h p m r R₀ : ℝ}
    (hl : n.left = lobePlane o (supportPoint α h (-m)))
    (hr : n.right = lobePlane o (supportPoint α h p))
    (hh : 0 < h) (hp : 0 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1)
    (hhr : h < r) (hrR : r < R₀) (hR : R₀ ≤ endpointRadius h m) :
    (fun φ => lobePlane o (polarPoint r (α+φ))) ''
        Icc (Real.pi-Real.arcsin (h/r)) (Real.pi-endpointAngle h m) ⊆ n.triangleHull o ∧
      0 < Real.arcsin (h/r)-endpointAngle h m ∧
      endpointAngle h m / (Real.arcsin (h/r)-endpointAngle h m) ≤ r/(R₀-r) := by
  have H := near_lobe_receipt (α := α) hh hp hm hunit hhr hrR hR
  refine ⟨physical_section_subset o n α h (p-1/2) r _ ?_ ?_ H.1,H.2⟩
  · convert hl using 1 <;> congr 2 <;> linarith
  · convert hr using 1 <;> congr 2 <;> ring

/-- In particular the actual Kakeya star property puts every point of the
complete far lobe in E, not only the endpoints or base-circle intersections. -/
theorem selected_far_lobe_subset {E : Set Plane} (K : StarShapedKakeya E)
    (θ : Direction) {α h p m r R₀ : ℝ}
    (hl : (K.needleFamily θ).left = lobePlane K.center (supportPoint α h (p-1)))
    (hr : (K.needleFamily θ).right = lobePlane K.center (supportPoint α h p))
    (hh : 0 < h) (hp : 0 ≤ p) (hm : 0 ≤ m) (hunit : p+m=1)
    (hhr : h < r) (hrR : r < R₀) (hR : R₀ ≤ endpointRadius h p) :
    (fun φ => lobePlane K.center (polarPoint r (α+φ))) ''
      Icc (endpointAngle h p) (Real.arcsin (h/r)) ⊆ E :=
  (physical_far_lobe_receipt K.center (K.needleFamily θ)
    hl hr hh hp hm hunit hhr hrR hR).1.trans (K.triangleHull_subset θ)

/-- The coordinate map is injective; membership in a physical hull is exactly
membership in its support triangle, not just a one-way envelope estimate. -/
theorem lobePlane_injective (o : Plane) : Function.Injective (lobePlane o) := by
  intro z w H
  have h0 := congrArg (fun v : Plane => v 0) H
  have h1 := congrArg (fun v : Plane => v 1) H
  simp only [lobePlane_zero,lobePlane_one] at h0 h1
  ext <;> linarith

theorem mem_physical_triangle_iff (o : Plane) (n : UnitNeedle) (α h c : ℝ)
    (hl : n.left = lobePlane o (supportPoint α h (c-1/2)))
    (hr : n.right = lobePlane o (supportPoint α h (c+1/2))) (z : CoordinatePlane) :
    lobePlane o z ∈ n.triangleHull o ↔ z ∈ supportNeedleTriangle α h c := by
  rw [triangleHull_eq_lobePlane_image o n α h c hl hr]
  exact (lobePlane_injective o).mem_set_image

/-- Negative signed height: the original triangle is on the other side of its
base. The physical point uses α-φ, with no additional reflected triangle. -/
theorem physical_negative_section_iff (o : Plane) (n : UnitNeedle)
    {α h p r φ : ℝ}
    (hl : n.left = lobePlane o (supportPoint α (-h) (p-1)))
    (hr : n.right = lobePlane o (supportPoint α (-h) p))
    (hh : 0 < h) (hrpos : 0 < r) (hφ : φ ∈ Icc 0 Real.pi) :
    lobePlane o (polarPoint r (α-φ)) ∈ n.triangleHull o ↔
      φ ∈ Icc (endpointAngle h p) (endpointAngle h (p-1)) ∧ r*Real.sin φ ≤ h := by
  have hl' : n.left = lobePlane o (supportPoint α (-h) ((p-1/2)-1/2)) := by
    convert hl using 1 <;> congr 2 <;> ring
  have hr' : n.right = lobePlane o (supportPoint α (-h) ((p-1/2)+1/2)) := by
    convert hr using 1 <;> congr 2 <;> ring
  rw [mem_physical_triangle_iff o n α (-h) (p-1/2) hl' hr',signed_section_iff]
  exact entire_section_iff hh hrpos hφ

/-- Zero height survives the literal endpoint-to-UnitNeedle bridge. -/
theorem physical_zero_section_iff (o : Plane) (n : UnitNeedle)
    {α p r φ : ℝ}
    (hl : n.left = lobePlane o (supportPoint α 0 (p-1)))
    (hr : n.right = lobePlane o (supportPoint α 0 p))
    (hrpos : 0 < r) (hφ : φ ∈ Icc 0 Real.pi) :
    lobePlane o (polarPoint r (α+φ)) ∈ n.triangleHull o ↔
      (φ=0 ∧ r ≤ p) ∨ (φ=Real.pi ∧ r ≤ 1-p) := by
  have hl' : n.left = lobePlane o (supportPoint α 0 ((p-1/2)-1/2)) := by
    convert hl using 1 <;> congr 2 <;> ring
  have hr' : n.right = lobePlane o (supportPoint α 0 ((p-1/2)+1/2)) := by
    convert hr using 1 <;> congr 2 <;> ring
  rw [mem_physical_triangle_iff o n α 0 (p-1/2) hl' hr']
  exact zero_height_section_iff hrpos hφ

/-- Every directed actual unit needle admits the signed support coordinates
used above. The only alternatives are the two genuine lifts of its direction. -/
theorem exists_physical_support_coordinates (o : Plane) (n : UnitNeedle)
    (t : ℝ) (hd : n.HasDirection (t : Direction)) :
    ∃ α h c : ℝ, (α=t ∨ α=t+Real.pi) ∧
      n.left = lobePlane o (supportPoint α h (c-1/2)) ∧
      n.right = lobePlane o (supportPoint α h (c+1/2)) := by
  obtain ⟨s,hs,heq⟩ := hasDirection_at_real n t hd
  obtain ⟨α,hα,hv⟩ : ∃ α : ℝ, (α=t ∨ α=t+Real.pi) ∧
      n.right-n.left = angleVector α := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hs with hs | hs
    · refine ⟨t,Or.inl rfl,?_⟩
      simpa [hs] using heq
    · refine ⟨t+Real.pi,Or.inr rfl,?_⟩
      rw [heq,hs]
      ext i
      fin_cases i <;> simp [angleVector,Real.cos_add,Real.sin_add]
  let a := Real.cos α*(n.left 0-o 0)+Real.sin α*(n.left 1-o 1)
  let h := -Real.sin α*(n.left 0-o 0)+Real.cos α*(n.left 1-o 1)
  have h0 := congrArg (fun v : Plane => v 0) hv
  have h1 := congrArg (fun v : Plane => v 1) hv
  simp [angleVector] at h0 h1
  refine ⟨α,h,a+1/2,hα,?_,?_⟩
  · ext i
    fin_cases i <;>
      simp [lobePlane,supportPoint,scaleCoordinatePlane,addCoordinatePlane,
        unitDirection,unitNormal,a,h]
    · linear_combination -(n.left 0-o 0)*(Real.cos_sq_add_sin_sq α)
    · linear_combination -(n.left 1-o 1)*(Real.cos_sq_add_sin_sq α)
  · ext i
    fin_cases i <;>
      simp [lobePlane,supportPoint,scaleCoordinatePlane,addCoordinatePlane,
        unitDirection,unitNormal,a,h]
    · linear_combination h0-(n.left 0-o 0)*(Real.cos_sq_add_sin_sq α)
    · linear_combination h1-(n.left 1-o 1)*(Real.cos_sq_add_sin_sq α)

#print axioms exists_physical_support_coordinates
#print axioms physical_negative_section_iff
#print axioms physical_zero_section_iff
#print axioms triangleHull_eq_lobePlane_image
#print axioms physical_far_lobe_receipt
#print axioms physical_near_lobe_receipt
#print axioms selected_far_lobe_subset
end
end StarKakeyaLower.OneTenth
