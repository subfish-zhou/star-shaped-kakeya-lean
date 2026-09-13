import Mathlib

/-!
# Greedy residual-height kernel

This file isolates the order/real-analysis step used after a geometric greedy
selection.  It does not construct the selected sequence or formalize any
outer-measure statement.  Its purpose is to make the formerly implicit
zero-supremum stopping branch explicit.
-/

namespace StarKakeyaLower

open Filter Set

section GreedyResidual

variable {ι : Type*} (height : ι → ℝ) (remaining : ℕ → Set ι)

/-- The directions which survive every deletion stage. -/
def greedyResidual : Set ι := ⋂ n, remaining n

/-- A finite stage whose remaining heights have supremum zero leaves only
height-zero directions.  The statement is deliberately phrased using the
actual upper-bound property needed by the greedy construction, so it also
covers an empty remaining set. -/
theorem residual_height_eq_zero_of_finite_stop
    (height_nonneg : ∀ x, 0 ≤ height x) (n : ℕ)
    (stage_sup_zero : ∀ x ∈ remaining n, height x ≤ 0)
    {x : ι} (hx : x ∈ greedyResidual remaining) : height x = 0 := by
  apply le_antisymm
  · exact stage_sup_zero x (mem_iInter.mp hx n)
  · exact height_nonneg x

/-- Infinite-selection branch: if every survivor is bounded by every selected
height (up to a fixed positive greedy factor), and selected heights tend to
zero, every residual height is zero.  This is the pure real/order core of the
usual `sup = 0` conclusion. -/
theorem residual_height_eq_zero_of_tendsto
    (height_nonneg : ∀ x, 0 ≤ height x)
    {selectedHeight : ℕ → ℝ} {m : ℝ} (hm : 0 < m)
    (greedy_bound : ∀ n x, x ∈ greedyResidual remaining →
      m * height x ≤ selectedHeight n)
    (selected_tendsto : Tendsto selectedHeight atTop (nhds 0))
    {x : ι} (hx : x ∈ greedyResidual remaining) : height x = 0 := by
  have hle : m * height x ≤ 0 :=
    ge_of_tendsto selected_tendsto (Eventually.of_forall fun n => greedy_bound n x hx)
  have : height x ≤ 0 := by nlinarith
  exact le_antisymm this (height_nonneg x)

/-- Set-level form of the finite zero-supremum stopping branch. -/
theorem height_image_residual_eq_singleton_of_finite_stop
    (height_nonneg : ∀ x, 0 ≤ height x) (n : ℕ)
    (stage_sup_zero : ∀ x ∈ remaining n, height x ≤ 0)
    (residual_nonempty : (greedyResidual remaining).Nonempty) :
    height '' greedyResidual remaining = ({0} : Set ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr
      (residual_height_eq_zero_of_finite_stop height remaining height_nonneg n
        stage_sup_zero hx)
  · intro hy
    obtain ⟨x, hx⟩ := residual_nonempty
    refine ⟨x, hx, ?_⟩
    simpa only [Set.mem_singleton_iff.mp hy] using
      (residual_height_eq_zero_of_finite_stop height remaining height_nonneg n
        stage_sup_zero hx)

/-- Set-level form of the infinite-selection branch; in particular the
residual supremum is literally the supremum of `{0}` whenever a survivor
exists. -/
theorem height_image_residual_eq_singleton_of_tendsto
    (height_nonneg : ∀ x, 0 ≤ height x)
    {selectedHeight : ℕ → ℝ} {m : ℝ} (hm : 0 < m)
    (greedy_bound : ∀ n x, x ∈ greedyResidual remaining →
      m * height x ≤ selectedHeight n)
    (selected_tendsto : Tendsto selectedHeight atTop (nhds 0))
    (residual_nonempty : (greedyResidual remaining).Nonempty) :
    height '' greedyResidual remaining = ({0} : Set ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr
      (residual_height_eq_zero_of_tendsto height remaining height_nonneg hm
        greedy_bound selected_tendsto hx)
  · intro hy
    obtain ⟨x, hx⟩ := residual_nonempty
    refine ⟨x, hx, ?_⟩
    simpa only [Set.mem_singleton_iff.mp hy] using
      (residual_height_eq_zero_of_tendsto height remaining height_nonneg hm
        greedy_bound selected_tendsto hx)

/-- Literal `sSup = 0` corollary for the finite zero-supremum stop. -/
theorem sSup_residual_height_eq_zero_of_finite_stop
    (height_nonneg : ∀ x, 0 ≤ height x) (n : ℕ)
    (stage_sup_zero : ∀ x ∈ remaining n, height x ≤ 0)
    (residual_nonempty : (greedyResidual remaining).Nonempty) :
    sSup (height '' greedyResidual remaining) = 0 := by
  rw [height_image_residual_eq_singleton_of_finite_stop height remaining height_nonneg n
    stage_sup_zero residual_nonempty]
  exact csSup_singleton 0

/-- Literal `sSup = 0` corollary for the infinite branch. -/
theorem sSup_residual_height_eq_zero_of_tendsto
    (height_nonneg : ∀ x, 0 ≤ height x)
    {selectedHeight : ℕ → ℝ} {m : ℝ} (hm : 0 < m)
    (greedy_bound : ∀ n x, x ∈ greedyResidual remaining →
      m * height x ≤ selectedHeight n)
    (selected_tendsto : Tendsto selectedHeight atTop (nhds 0))
    (residual_nonempty : (greedyResidual remaining).Nonempty) :
    sSup (height '' greedyResidual remaining) = 0 := by
  rw [height_image_residual_eq_singleton_of_tendsto height remaining height_nonneg hm
    greedy_bound selected_tendsto residual_nonempty]
  exact csSup_singleton 0

end GreedyResidual

end StarKakeyaLower
