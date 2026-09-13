import StarKakeyaLower.EndpointCapacityUniversal
import StarKakeyaLower.PolarOuterMeasure

/-!
# Radial-superlevel layer-cake bridge

Selected triangle unions are radially down-closed about the origin.  Therefore
a direction represented outside radius `t` is represented on every lower
positive circle.  This converts strict radial-superlevel outer bounds into the
fixed-radius `angleOuter` minorants consumed by the existing outer-polar
integral theorem.
-/

open Set MeasureTheory Real
open scoped ENNReal BigOperators

namespace StarKakeyaLower

noncomputable section

/-- Closure under contraction toward the origin. -/
def RadiallyDownClosed (E : Set CoordinatePlane) : Prop :=
  ∀ ⦃z⦄, z ∈ E → ∀ ⦃lam : ℝ⦄, lam ∈ Icc (0 : ℝ) 1 →
    scaleCoordinatePlane lam z ∈ E

/-- Radial down-closure is Mathlib star-convexity about zero. -/
theorem RadiallyDownClosed.starConvex_zero
    {E : Set CoordinatePlane} (hE : RadiallyDownClosed E) :
    StarConvex ℝ 0 E := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have h := hE hz ⟨hb, hb1⟩
  simpa [scaleCoordinatePlane] using h

/-- Each literal support triangle is radially down-closed. -/
theorem DirectionNeedle.radiallyDownClosed_triangle
    {d : ProjectiveDirection} (N : DirectionNeedle d) :
    RadiallyDownClosed N.triangle := by
  rintro z ⟨lam0, hlam0, x, hx, rfl⟩ lam hlam
  refine ⟨lam * lam0, ⟨mul_nonneg hlam.1 hlam0.1, ?_⟩, x, hx, ?_⟩
  · exact (mul_le_mul hlam.2 hlam0.2 hlam0.1 zero_le_one).trans (by norm_num)
  · ext <;> simp [scaleCoordinatePlane] <;> ring

/-- An arbitrary selected union of literal support triangles is radially
 down-closed; no regularity of the selector or direction set is used. -/
theorem radiallyDownClosed_directionTriangleUnion
    (N : ∀ d, DirectionNeedle d) (A : Set ProjectiveDirection) :
    RadiallyDownClosed (directionTriangleUnion N A) := by
  intro z hz lam hlam
  simp only [directionTriangleUnion, mem_iUnion] at hz ⊢
  rcases hz with ⟨d, hz⟩
  exact ⟨d, (N d.1).radiallyDownClosed_triangle hz hlam⟩

/-- The canonical exact selected triangle union is radially down-closed. -/
theorem StarShapedKakeya.radiallyDownClosed_selectedTriangleUnion
    {E : Set Plane} (K : StarShapedKakeya E) :
    RadiallyDownClosed
      (directionTriangleUnion (universalPositiveNeedle K) Set.univ) :=
  radiallyDownClosed_directionTriangleUnion _ _

/-- Standard-library formulation of radial down-closure. -/
theorem StarShapedKakeya.starConvex_zero_selectedTriangleUnion
    {E : Set Plane} (K : StarShapedKakeya E) :
    StarConvex ℝ 0
      (directionTriangleUnion (universalPositiveNeedle K) Set.univ) :=
  K.radiallyDownClosed_selectedTriangleUnion.starConvex_zero

/-- A strict radial superlevel at `t` injects into the fixed angular section at
any lower positive radius `s`. -/
theorem radialSuperlevelOuter_le_angleOuter
    {E : Set CoordinatePlane} (hE : RadiallyDownClosed E)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    radialSuperlevelOuter E t ≤ angleOuter E s := by
  apply OuterMeasure.mono
  intro theta htheta
  rcases htheta with ⟨hcut, alpha, rho, halpha, htrho, hp⟩
  refine ⟨hcut, ?_⟩
  have hrho : 0 < rho := hs.trans (hst.trans_lt htrho)
  have hratio : s / rho ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hs.le hrho.le
    · exact (div_le_one hrho).2 (hst.trans_lt htrho).le
  have hscaled := hE hp hratio
  have heq : scaleCoordinatePlane (s / rho) (polarPoint rho alpha) =
      polarPoint s alpha := by
    ext <;> simp [scaleCoordinatePlane, polarPoint, unitDirection] <;> field_simp
  rw [heq] at hscaled
  have hangle : polarPoint s theta = polarPoint s alpha :=
    polarPoint_eq_of_polar_coe_eq halpha.symm
  rw [hangle]
  exact hscaled

/-- Canonical selected-triangle specialization. -/
theorem StarShapedKakeya.selectedTriangleUnion_radialSuperlevelOuter_le_angleOuter
    {E : Set Plane} (K : StarShapedKakeya E)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    radialSuperlevelOuter
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) t ≤
      angleOuter
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) s :=
  radialSuperlevelOuter_le_angleOuter
    K.radiallyDownClosed_selectedTriangleUnion hs hst

/-- Finite disjoint step-function layer cake.  On cell `cell i`, the step height
is the strict radial-superlevel outer mass at the higher radius `t i`.  The
cells themselves need not be measurable. -/
theorem finiteStep_lintegral_le_outerMeasure
    {ι : Type*}
    (E : Set CoordinatePlane) (hE : RadiallyDownClosed E)
    (I : Finset ι) (cell : ι → Set ℝ) (t : ι → ℝ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (cell i) (cell j))
    (hwindow : ∀ i ∈ I, ∀ s ∈ cell i, 0 < s ∧ s < t i)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ s in Icc a b, ENNReal.ofReal s *
      (∑ i ∈ I, (cell i).indicator
        (fun _ => radialSuperlevelOuter E (t i)) s)) ≤
      volume.toOuterMeasure E := by
  classical
  apply lintegral_le_outerMeasure_of_le_angleOuter E ha
  intro s hsab
  by_cases hex : ∃ i ∈ I, s ∈ cell i
  · rcases hex with ⟨i, hiI, hsi⟩
    have hsum :
        (∑ j ∈ I, (cell j).indicator
          (fun _ => radialSuperlevelOuter E (t j)) s) =
        radialSuperlevelOuter E (t i) := by
      rw [Finset.sum_eq_single i]
      · simp [hsi]
      · intro j hjI hji
        have hnot : s ∉ cell j := by
          intro hsj
          exact Set.disjoint_left.1 (hdisj i hiI j hjI (Ne.symm hji)) hsi hsj
        simp [hnot]
      · exact fun h => (h hiI).elim
    rw [hsum]
    exact radialSuperlevelOuter_le_angleOuter hE
      (hwindow i hiI s hsi).1 (hwindow i hiI s hsi).2.le
  · have hnone : ∀ i ∈ I, s ∉ cell i := by
      intro i hiI hsi
      exact hex ⟨i, hiI, hsi⟩
    have hsum :
        (∑ i ∈ I, (cell i).indicator
          (fun _ => radialSuperlevelOuter E (t i)) s) = 0 := by
      apply Finset.sum_eq_zero
      intro i hiI
      simp [hnone i hiI]
    rw [hsum]
    exact bot_le

/-- Finite-step layer cake for the exact canonical selected triangle union. -/
theorem StarShapedKakeya.selectedTriangleUnion_finiteStep_lintegral_le
    {E : Set Plane} (K : StarShapedKakeya E)
    {ι : Type*}
    (I : Finset ι) (cell : ι → Set ℝ) (t : ι → ℝ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (cell i) (cell j))
    (hwindow : ∀ i ∈ I, ∀ s ∈ cell i, 0 < s ∧ s < t i)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ s in Icc a b, ENNReal.ofReal s *
      (∑ i ∈ I, (cell i).indicator (fun _ =>
        radialSuperlevelOuter
          (directionTriangleUnion (universalPositiveNeedle K) Set.univ) (t i)) s)) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) :=
  finiteStep_lintegral_le_outerMeasure _
    K.radiallyDownClosed_selectedTriangleUnion I cell t hdisj hwindow ha

end

end StarKakeyaLower
