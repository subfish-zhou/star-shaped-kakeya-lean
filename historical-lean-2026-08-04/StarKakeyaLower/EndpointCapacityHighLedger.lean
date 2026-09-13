import StarKakeyaLower.EndpointCapacityHighGeometry
import StarKakeyaLower.EndpointCapacityWitness32Data

/-!
# Frozen high-tail ledgers for the 141/2000 witness

The `k`-th high class uses nearest-radius band `(A_k,B_k]` and radial ledger
`[B_k,R_k]`.  These ledgers have strict gaps between them.
-/

open Set

namespace StarKakeyaLower
namespace Witness141

noncomputable section

/-- Lower nearest-radius cut of high class `k`. -/
def highA (k : ℕ) : ℝ := eta + (k : ℝ) / 2

/-- Upper nearest-radius cut of high class `k`. -/
def highB (k : ℕ) : ℝ := highA k + 1 / 2

/-- Rational lower bound for the first high outer radius. -/
def highRadiusLower : ℝ := 5049 / 5000

/-- Uniform certified lower width of every high ledger. -/
def highWidthLower : ℝ := highRadiusLower - highB 0

/-- Uniform lower bound for `u / (R + u)` on the high ledgers. -/
def highFactorLower : ℝ :=
  (eta + 1 / 2) / (2 * eta + 3 / 2)

/-- Frozen crude high-ledger payment lower bound. -/
def highPaymentLower : ℝ :=
  highFactorLower * highWidthLower ^ 2 / 2

/-- The rational first-radius lower bound is strictly below the exact square. -/
theorem highRadiusLower_sq_lt_one_add_eta_sq :
    highRadiusLower ^ 2 < 1 + eta ^ 2 := by
  norm_num [highRadiusLower, eta]

/-- The crude frozen high payment already exceeds the common coefficient. -/
theorem common_lt_highPaymentLower : common < highPaymentLower := by
  norm_num [highPaymentLower, highFactorLower, highWidthLower,
    highRadiusLower, highB, highA, eta, common]

/-- Outer radius forced by the exact foot-outside geometry. -/
def highOuterRadius (k : ℕ) : ℝ :=
  Real.sqrt (highA k ^ 2 + 1 +
    2 * Real.sqrt (highA k ^ 2 - eta ^ 2))

/-- Closed high radial ledger. -/
def highLedger (k : ℕ) : Set ℝ :=
  Icc (highB k) (highOuterRadius k)

/-- High nearest-radius class `(A_k,B_k]`. -/
def highClass {E : Set Plane} (K : StarShapedKakeya E) (k : ℕ) :
    Set ProjectiveDirection :=
  endpointCapacityBandClass K (highA k) (highB k)

/-- Every direction in high class `k` is eligible for the fixed window ending at
`highOuterRadius k`, at every radial level in its ledger, provided all selected
heights are below `eta`. -/
theorem highClass_subset_windowDirections
    {E : Set Plane} (K : StarShapedKakeya E)
    (hheight : ∀ d, (universalPositiveNeedle K d).height < eta)
    (k : ℕ) {u : ℝ} (hu : u ∈ highLedger k) :
    highClass K k ⊆
      endpointCapacityWindowDirections K u (highOuterRadius k) := by
  intro d hd
  let N := universalPositiveNeedle K d
  have hetaPos : 0 < eta := by norm_num [eta]
  have heta0 : 0 ≤ eta := hetaPos.le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hApos : 0 < highA k := by
    unfold highA
    nlinarith [hetaPos]
  have hAa : eta ≤ highA k := by
    unfold highA
    nlinarith
  have hB0 : 0 ≤ highB k := by
    unfold highB
    nlinarith [hApos]
  have hinner : N.nearestRadiusSq ≤ u ^ 2 := by
    have hBu : highB k ≤ u := hu.1
    have hsq : highB k ^ 2 ≤ u ^ 2 := by nlinarith
    exact hd.2.trans hsq
  have hrad : 0 ≤ highA k ^ 2 - eta ^ 2 := by
    nlinarith [hetaPos, hApos, hAa]
  have houtSq : highOuterRadius k ^ 2 =
      highA k ^ 2 + 1 + 2 * Real.sqrt (highA k ^ 2 - eta ^ 2) := by
    rw [highOuterRadius, Real.sq_sqrt]
    positivity
  have hfar := N.high_foot_outside_sq
    (universalPositiveNeedle_height_nonneg K d) (hheight d)
    heta0 hAa hd.1
  exact ⟨hinner, by rw [houtSq]; exact hfar.le⟩

@[simp] theorem eta_pos : 0 < eta := by
  norm_num [eta]

private theorem eta_lt_three_quarters : eta < (3 : ℝ) / 4 := by
  norm_num [eta]

@[simp] theorem highA_pos (k : ℕ) : 0 < highA k := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  unfold highA
  nlinarith [eta_pos]

/-- Every high ledger has positive width. -/
theorem highB_lt_highOuterRadius (k : ℕ) :
    highB k < highOuterRadius k := by
  let x : ℝ := (k : ℝ) / 2
  have hx : 0 ≤ x := by positivity
  have hinner : 0 ≤ highA k ^ 2 - eta ^ 2 := by
    rw [show highA k = eta + x by rfl]
    nlinarith [eta_pos]
  have hsqrt_lower : x ≤ Real.sqrt (highA k ^ 2 - eta ^ 2) := by
    rw [Real.le_sqrt hx hinner]
    rw [show highA k = eta + x by rfl]
    nlinarith [eta_pos]
  have hB : 0 ≤ highB k := by
    unfold highB
    nlinarith [highA_pos k]
  have hlin : highA k < (3 : ℝ) / 4 +
      2 * Real.sqrt (highA k ^ 2 - eta ^ 2) := by
    have hAx : highA k = eta + x := rfl
    rw [hAx] at hsqrt_lower ⊢
    nlinarith [eta_lt_three_quarters]
  rw [highOuterRadius, Real.lt_sqrt hB]
  unfold highB
  nlinarith

/-- The `k`-th ledger ends strictly before the next one begins. -/
theorem highOuterRadius_lt_next_highB (k : ℕ) :
    highOuterRadius k < highB (k + 1) := by
  have hA : 0 < highA k := highA_pos k
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos eta_pos
  have hs : Real.sqrt (highA k ^ 2 - eta ^ 2) < highA k := by
    rw [Real.sqrt_lt' hA]
    nlinarith
  have hout : highOuterRadius k < highA k + 1 := by
    rw [highOuterRadius, Real.sqrt_lt' (by positivity : 0 < highA k + 1)]
    nlinarith
  have hnext : highB (k + 1) = highA k + 1 := by
    simp [highB, highA, Nat.cast_add]
    ring
  rwa [hnext]

/-- The closed high ledgers are pairwise disjoint. -/
theorem highLedger_pairwise_disjoint {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (highLedger k) (highLedger l) := by
  rw [highLedger, highLedger, Set.disjoint_left]
  intro z hzk hzl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hsucc : k + 1 ≤ l := hlt
    have hBmono : highB (k + 1) ≤ highB l := by
      have hc : ((k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hsucc
      unfold highB highA
      nlinarith
    have hgap := highOuterRadius_lt_next_highB k
    exact (not_lt_of_ge hzl.1)
      (lt_of_le_of_lt hzk.2 (lt_of_lt_of_le hgap hBmono))
  · have hsucc : l + 1 ≤ k := hgt
    have hBmono : highB (l + 1) ≤ highB k := by
      have hc : ((l + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hsucc
      unfold highB highA
      nlinarith
    have hgap := highOuterRadius_lt_next_highB l
    exact (not_lt_of_ge hzk.1)
      (lt_of_le_of_lt hzl.2 (lt_of_lt_of_le hgap hBmono))

/-- Set-indexed pairwise disjointness of all high ledgers. -/
theorem highLedgers_pairwise :
    Set.Pairwise (Set.univ : Set ℕ)
      (fun k l => Disjoint (highLedger k) (highLedger l)) := by
  intro k _ l _ hkl
  exact highLedger_pairwise_disjoint hkl

/-- The first high ledger starts strictly after the low schedule ends. -/
theorem low_high_radial_separation :
    switch ⟨32, by omega⟩ < highB 0 := by
  norm_num [switch, highB, highA, eta]

end
end Witness141
end StarKakeyaLower
