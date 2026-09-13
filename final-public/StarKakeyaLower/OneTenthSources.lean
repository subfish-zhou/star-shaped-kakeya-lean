import StarKakeyaLower.OneTenthRecovery
import StarKakeyaLower.OneTenthCircleReceipt

/-! # Borel physical sources recovered in an arbitrary open cover

The midpoint is an actual Euclidean `Plane` point. Norms below are Euclidean,
never the product sup norm. The centre `o` is retained explicitly. No radius
cap is imposed on the original set, and no area estimate is an assumption.
-/
open Set MeasureTheory
namespace StarKakeyaLower.OneTenth.Sources
noncomputable section

/-- One right-closed representative per projective direction. -/
def chart : Set ℝ := Ioc 0 Real.pi

/-- Unsigned, canonical endpoints of the recovered midpoint. -/
def minus (c : ℝ → Plane) (q : ℝ) : Plane := c q - (1/2 : ℝ) • angleVector q
def plus (c : ℝ → Plane) (q : ℝ) : Plane := c q + (1/2 : ℝ) • angleVector q

def needle (c : ℝ → Plane) (q : ℝ) : UnitNeedle :=
  (MidpointFrame.mk (c q) 1 (by norm_num)).needle q

@[simp] theorem needle_left (c : ℝ → Plane) (q : ℝ) :
    (needle c q).left = minus c q := by simp [needle, MidpointFrame.needle, MidpointFrame.left, minus]
@[simp] theorem needle_right (c : ℝ → Plane) (q : ℝ) :
    (needle c q).right = plus c q := by simp [needle, MidpointFrame.needle, MidpointFrame.right, plus]

theorem plus_sub_minus (c : ℝ → Plane) (q : ℝ) : plus c q - minus c q = angleVector q := by
  unfold plus minus
  module

theorem unit_length (c : ℝ → Plane) (q : ℝ) : dist (minus c q) (plus c q) = 1 := by
  simpa using (needle c q).unit_length

theorem hasDirection (c : ℝ → Plane) (q : ℝ) :
    (needle c q).HasDirection (q : Direction) :=
  MidpointFrame.needle_hasDirection _ q

def triangle (o : Plane) (c : ℝ → Plane) (q : ℝ) : Set Plane :=
  (needle c q).triangleHull o

/-- Forgetting the old orientation only exchanges endpoints, not triangles. -/
theorem frame_triangle_eq (o : Plane) (F : MidpointFrame) (q : ℝ) :
    triangle o (fun _ => F.midpoint) q = (F.needle q).triangleHull o := by
  have hs := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp F.abs_sign
  rcases hs with hs | hs
  · simp [triangle, UnitNeedle.triangleHull, UnitNeedle.carrier, needle,
      MidpointFrame.needle, MidpointFrame.left, MidpointFrame.right, hs]
  · have hl : F.left q = plus (fun _ => F.midpoint) q := by
      simp [MidpointFrame.left, plus, hs]
    have hr : F.right q = minus (fun _ => F.midpoint) q := by
      simp [MidpointFrame.right, minus, hs, sub_eq_add_neg]
    simp only [triangle, UnitNeedle.triangleHull, UnitNeedle.carrier,
      needle_left, needle_right, MidpointFrame.needle]
    rw [hl, hr, segment_symm ℝ (plus _ q) (minus _ q)]

theorem measurable_minus {c : ℝ → Plane} (hc : Measurable c) : Measurable (minus c) :=
  hc.sub (measurable_const.smul MidpointFrame.continuous_angleVector.measurable)
theorem measurable_plus {c : ℝ → Plane} (hc : Measurable c) : Measurable (plus c) :=
  hc.add (measurable_const.smul MidpointFrame.continuous_angleVector.measurable)

/-- The recovered finite-valued midpoint really is Borel; endpoint signs are
not assumed measurable, and need not be. -/
theorem borel_midpoint_recovery {E G : Set Plane} (K : StarShapedKakeya E)
    (hEG : E ⊆ G) (hG : IsOpen G) :
    ∃ c : ℝ → Plane, Measurable c ∧ (range c).Finite ∧
      ∀ q ∈ chart, (needle c q).HasDirection (q : Direction) ∧ triangle K.center c q ⊆ G := by
  obtain ⟨F, hfinite, hl, hr, hgood⟩ := measurable_midpoint_recovery K hEG hG
  have heq : (fun q => (F q).midpoint) =
      (fun q => (1/2 : ℝ) • ((F q).left q + (F q).right q)) := by
    funext q
    unfold MidpointFrame.left MidpointFrame.right
    module
  refine ⟨fun q => (F q).midpoint, ?_, hfinite, ?_⟩
  · rw [heq]
    exact measurable_const.smul (hl.add hr)
  · intro q hq
    refine ⟨hasDirection _ q, ?_⟩
    have h := (hgood q ⟨le_of_lt hq.1, hq.2⟩).2
    exact (frame_triangle_eq K.center (F q) q) ▸ h

/-- Signed longitudinal midpoint coordinate and signed normal height. -/
def longitudinal (o : Plane) (c : ℝ → Plane) (q : ℝ) : ℝ :=
  (c q - o) 0 * Real.cos q + (c q - o) 1 * Real.sin q
def signedHeight (o : Plane) (c : ℝ → Plane) (q : ℝ) : ℝ :=
  -(c q - o) 0 * Real.sin q + (c q - o) 1 * Real.cos q

/-- Actual endpoint Euclidean radii; N is NOT distance to a support line. -/
def M (o : Plane) (c : ℝ → Plane) (q : ℝ) : ℝ :=
  max ‖minus c q - o‖ ‖plus c q - o‖
def N (o : Plane) (c : ℝ → Plane) (q : ℝ) : ℝ :=
  min ‖minus c q - o‖ ‖plus c q - o‖

theorem measurable_longitudinal (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    Measurable (longitudinal o c) := by
  unfold longitudinal
  fun_prop

theorem measurable_signedHeight (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    Measurable (signedHeight o c) := by
  unfold signedHeight
  fun_prop

theorem measurable_M (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : Measurable (M o c) :=
  ((measurable_minus hc).sub measurable_const).norm.max
    ((measurable_plus hc).sub measurable_const).norm

theorem measurable_N (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : Measurable (N o c) :=
  ((measurable_minus hc).sub measurable_const).norm.min
    ((measurable_plus hc).sub measurable_const).norm

/-- Tie-positive Borel first physical lift. -/
def A (o : Plane) (c : ℝ → Plane) : Set ℝ := {q | 0 ≤ longitudinal o c q}
def farAngle (o : Plane) (c : ℝ → Plane) := selectedAngle (A o c)
open Classical in
def farEndpoint (o : Plane) (c : ℝ → Plane) (q : ℝ) : Plane :=
  if q ∈ A o c then plus c q else minus c q
open Classical in
def nearEndpoint (o : Plane) (c : ℝ → Plane) (q : ℝ) : Plane :=
  if q ∈ A o c then minus c q else plus c q
open Classical in
def farHeight (o : Plane) (c : ℝ → Plane) (q : ℝ) : ℝ :=
  if q ∈ A o c then signedHeight o c q else -signedHeight o c q

def x (o : Plane) (c : ℝ → Plane) (q : ℝ) : ℝ := 1/2 + |longitudinal o c q|

theorem measurableSet_A (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : MeasurableSet (A o c) :=
  measurableSet_le measurable_const (measurable_longitudinal o hc)

theorem measurable_farAngle (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    Measurable (farAngle o c) := by
  classical
  exact Measurable.ite (measurableSet_A o hc) measurable_id (measurable_const.add measurable_id)

theorem measurable_farEndpoint (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    Measurable (farEndpoint o c) := by
  classical
  exact Measurable.ite (measurableSet_A o hc) (measurable_plus hc) (measurable_minus hc)

theorem measurable_nearEndpoint (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    Measurable (nearEndpoint o c) := by
  classical
  exact Measurable.ite (measurableSet_A o hc) (measurable_minus hc) (measurable_plus hc)

theorem measurable_farHeight (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    Measurable (farHeight o c) := by
  classical
  exact Measurable.ite (measurableSet_A o hc) (measurable_signedHeight o hc)
    (measurable_signedHeight o hc).neg

theorem measurable_x (o : Plane) {c : ℝ → Plane} (hc : Measurable c) : Measurable (x o c) :=
  measurable_const.add (measurable_longitudinal o hc).abs

theorem M_add_N (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    M o c q + N o c q = ‖minus c q-o‖ + ‖plus c q-o‖ := max_add_min _ _

theorem one_le_M_add_N (o : Plane) (c : ℝ → Plane) (q : ℝ) : 1 ≤ M o c q + N o c q := by
  rw [M_add_N, ← unit_length c q]
  have h := dist_triangle (minus c q) o (plus c q)
  rw [dist_comm o (plus c q)] at h
  simpa [dist_eq_norm] using h

theorem half_le_M (o : Plane) (c : ℝ → Plane) (q : ℝ) : (1/2 : ℝ) ≤ M o c q := by
  have h := one_le_M_add_N o c q
  have hnm : N o c q ≤ M o c q := (min_le_left _ _).trans (le_max_left _ _)
  linarith

/-- Finite-valued recovery yields a family-dependent radius bound globally in
q. This is a conclusion about the recovered family, never a cap on E. -/
theorem finite_midpoints_radius_bound (o : Plane) (c : ℝ → Plane) (hc : (range c).Finite) :
    ∃ R : ℝ, ∀ q, M o c q ≤ R := by
  obtain ⟨R, hR⟩ := (hc.image (fun p => ‖p-o‖)).bddAbove
  refine ⟨R+1/2, fun q => ?_⟩
  have hq : ‖c q-o‖ ≤ R := hR ⟨c q, mem_range_self q, rfl⟩
  have hhalf : ‖(1/2 : ℝ) • angleVector q‖ = 1/2 := by
    rw [norm_smul, norm_angleVector, Real.norm_eq_abs]
    norm_num
  apply max_le
  · have he : minus c q-o = (c q-o) - (1/2 : ℝ) • angleVector q := by unfold minus; module
    rw [he]
    exact (norm_sub_le _ _).trans (by rw [hhalf]; linarith)
  · have he : plus c q-o = (c q-o) + (1/2 : ℝ) • angleVector q := by unfold plus; module
    rw [he]
    exact (norm_add_le _ _).trans (by rw [hhalf]; linarith)

end
end StarKakeyaLower.OneTenth.Sources
