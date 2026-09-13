import StarKakeyaLower.EndpointCapacityFractionalCover
import StarKakeyaLower.EndpointCapacityLeftLimit
import StarKakeyaLower.EndpointCapacityWitness32Arithmetic

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace StarKakeyaLower.Witness141

noncomputable section

/-- The concrete 32 low atoms: one initial interval and 31 half-open bands. -/
def lowClass {E : Set Plane} (K : StarShapedKakeya E) (j : Fin 32) :
    Set ProjectiveDirection :=
  if h : j.1 = 0 then endpointCapacityInitialClass K (b j)
  else endpointCapacityBandClass K (b ⟨j.1 - 1, by omega⟩) (b j)

/-- The frozen upper cuts are strictly increasing. -/
theorem b_strictMono : StrictMono b := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  case «1» =>
    change (3859 / 100000 : ℝ) < 11831 / 250000
    norm_num

private theorem b_sq_strictMono : StrictMono (fun j => (b j) ^ 2) := by
  intro i j hij
  have hi := b_pos i
  have hj := b_pos j
  have h := b_strictMono hij
  nlinarith

private theorem lowClass_mem_iff {E : Set Plane} (K : StarShapedKakeya E)
    (j : Fin 32) (theta : ProjectiveDirection) :
    theta ∈ lowClass K j ↔
      (if h : j.1 = 0 then
        (universalPositiveNeedle K theta).nearestRadiusSq ≤ (b j) ^ 2
      else
        (b ⟨j.1 - 1, by omega⟩) ^ 2 <
            (universalPositiveNeedle K theta).nearestRadiusSq ∧
          (universalPositiveNeedle K theta).nearestRadiusSq ≤ (b j) ^ 2) := by
  simp only [lowClass]
  split <;> rfl

private theorem lowClass_disjoint_of_lt {E : Set Plane} (K : StarShapedKakeya E)
    {i j : Fin 32} (hlt : i < j) : Disjoint (lowClass K i) (lowClass K j) := by
  rw [Set.disjoint_left]
  intro theta hi hj
  rw [lowClass_mem_iff] at hi hj
  have hj0 : j.1 ≠ 0 := by omega
  simp only [hj0, ↓reduceDIte] at hj
  have hpred : i ≤ (⟨j.1 - 1, by omega⟩ : Fin 32) := by
    exact Fin.mk_le_mk.mpr (by omega)
  have hsquare : (b i) ^ 2 ≤ (b ⟨j.1 - 1, by omega⟩) ^ 2 :=
    b_sq_strictMono.monotone hpred
  split at hi
  · exact (not_lt_of_ge (hi.trans hsquare)) hj.1
  · exact (not_lt_of_ge (hi.2.trans hsquare)) hj.1

/-- The 32 low atoms are pairwise disjoint, without measurability assumptions. -/
theorem lowClass_pairwiseDisjoint {E : Set Plane} (K : StarShapedKakeya E) :
    (Set.univ : Set (Fin 32)).PairwiseDisjoint (lowClass K) := by
  intro i _ j _ hij
  change Disjoint (lowClass K i) (lowClass K j)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact lowClass_disjoint_of_lt K hlt
  · exact (lowClass_disjoint_of_lt K hgt).symm

/-- Exact exhaustion of the low nearest-radius region by the 32 atoms. -/
theorem iUnion_lowClass {E : Set Plane} (K : StarShapedKakeya E) :
    (⋃ j : Fin 32, lowClass K j) =
      {theta | (universalPositiveNeedle K theta).nearestRadiusSq ≤ eta ^ 2} := by
  ext theta
  constructor
  · intro h
    simp only [mem_iUnion] at h
    obtain ⟨j, hj⟩ := h
    rw [lowClass_mem_iff] at hj
    have hbe := b_le_eta j
    have hsq : (b j) ^ 2 ≤ eta ^ 2 := by
      have := b_pos j
      have heta : 0 < eta := by norm_num [eta]
      nlinarith
    split at hj
    · exact hj.trans hsq
    · exact hj.2.trans hsq
  · intro htheta
    let x := (universalPositiveNeedle K theta).nearestRadiusSq
    have hex : ∃ n : ℕ, ∃ hn : n < 32, x ≤ (b ⟨n, hn⟩) ^ 2 := by
      refine ⟨31, by omega, ?_⟩
      rw [b_last]
      simpa [x] using htheta
    let n := Nat.find hex
    have hnData := Nat.find_spec hex
    obtain ⟨hn32, hnx⟩ := hnData
    let j : Fin 32 := ⟨n, hn32⟩
    simp only [mem_iUnion]
    refine ⟨j, ?_⟩
    rw [lowClass_mem_iff]
    by_cases hn0 : n = 0
    · rw [dif_pos (by simpa [j] using hn0)]
      simpa [x, j, n] using hnx
    · simp only [j, hn0, ↓reduceDIte]
      refine ⟨?_, hnx⟩
      have hnot : ¬ x ≤ (b ⟨n - 1, by omega⟩) ^ 2 := by
        intro hx
        exact Nat.find_min hex (by omega) ⟨by omega, hx⟩
      exact lt_of_not_ge hnot

/-- At radius `r`, retain exactly those low atoms whose frozen upper cut and
unit-chord outer-radius budget make them eligible for window `i`. -/
def lowEligible {E : Set Plane} (K : StarShapedKakeya E)
    (i : Fin 32) (r : ℝ) : Set ProjectiveDirection :=
  ⋃ j : Fin 32, ⋃ (_ : b j ≤ r ∧
      outerRadius i ^ 2 ≤ classLower j ^ 2 + 1 / 4), lowClass K j

private theorem lowClass_subset_window_of_budget {E : Set Plane}
    (K : StarShapedKakeya E) (j : Fin 32) {r R : ℝ}
    (hbr : b j ≤ r) (hbudget : R ^ 2 ≤ classLower j ^ 2 + 1 / 4) :
    lowClass K j ⊆ endpointCapacityWindowDirections K r R := by
  by_cases hj0 : j.1 = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    simpa [lowClass, classLower] using
      endpointCapacityInitialClass_subset_windowDirections K
        (b_pos (0 : Fin 32)).le hbr (by simpa [classLower] using hbudget)
  · simpa [lowClass, classLower, hj0, add_comm] using
      endpointCapacityBandClass_subset_windowDirections K
        (b_pos j).le hbr hbudget

/-- Every dynamically eligible low union is accepted by the concrete frozen
fixed window. -/
theorem lowEligible_subset_windowDirections {E : Set Plane}
    (K : StarShapedKakeya E) (i : Fin 32) (r : ℝ) :
    lowEligible K i r ⊆
      endpointCapacityWindowDirections K r (outerRadius i) := by
  intro theta htheta
  simp only [lowEligible, mem_iUnion] at htheta
  obtain ⟨j, htheta⟩ := htheta
  obtain ⟨hbudget, hj⟩ := htheta
  exact lowClass_subset_window_of_budget K j hbudget.1 hbudget.2 hj

/-- Per-radial-window lower bound supplied by the production left-limit theorem. -/
theorem lowEligible_fixedWindow_leftLim {E : Set Plane}
    (K : StarShapedKakeya E) (i : Fin 32) (r : ℝ)
    (hr : 0 < r) (hrR : r < outerRadius i) :
    ENNReal.ofReal ((outerRadius i - r) / (outerRadius i + r)) *
        volume (lowEligible K i r) ≤
      (radialSuperlevelOuter
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r := by
  calc
    _ ≤ ENNReal.ofReal ((outerRadius i - r) / (outerRadius i + r)) *
        volume (endpointCapacityWindowDirections K r (outerRadius i)) :=
      mul_le_mul_right (measure_mono (lowEligible_subset_windowDirections K i r)) _
    _ ≤ _ := K.endpointCapacity_fixedWindow_leftLim r (outerRadius i) hr hrR

/-- Nat-labelled form required by the production fractional-cover lemma. -/
def lowAtom {E : Set Plane} (K : StarShapedKakeya E) (j : ℕ) :
    Set ProjectiveDirection :=
  if h : j < 32 then lowClass K ⟨j, h⟩ else ∅

private theorem lowAtom_pairwiseDisjoint {E : Set Plane}
    (K : StarShapedKakeya E) :
    (Finset.range 32 : Set ℕ).PairwiseDisjoint (lowAtom K) := by
  intro i hi j hj hij
  have hi32 := Finset.mem_range.1 hi
  have hj32 := Finset.mem_range.1 hj
  change Disjoint (lowAtom K i) (lowAtom K j)
  unfold lowAtom
  rw [dif_pos hi32, dif_pos hj32]
  exact lowClass_pairwiseDisjoint K (Set.mem_univ _) (Set.mem_univ _)
    (fun h => hij (Fin.ext_iff.1 h))

private theorem iUnion_lowAtom_range {E : Set Plane}
    (K : StarShapedKakeya E) :
    (⋃ j ∈ Finset.range 32, lowAtom K j) = ⋃ j : Fin 32, lowClass K j := by
  ext theta
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hj, htheta⟩
    have hj32 := Finset.mem_range.1 hj
    exact ⟨⟨j, hj32⟩, by simpa [lowAtom, hj32] using htheta⟩
  · rintro ⟨j, htheta⟩
    exact ⟨j.1, Finset.mem_range.2 j.2, by simpa [lowAtom, j.2] using htheta⟩

/-- Abstract finite ledger before the final planar layer-cake step.  Keeping this
local-integral form is essential when low and high ledgers are combined: their
disjoint radial supports must pay planar outer measure only once. -/
theorem finiteLowLedger_to_lintegral
    {E : Set Plane} (K : StarShapedKakeya E)
    {κ : Type*} (I : Finset κ) (S : κ → Finset ℕ)
    (d : κ → NNReal) (c : NNReal)
    (hS : ∀ k ∈ I, S k ⊆ Finset.range 32)
    (hcover : ∀ j ∈ Finset.range 32,
      c ≤ ∑ k ∈ I.filter (fun k => j ∈ S k), d k)
    (hweighted :
      ∑ k ∈ I, (d k : ENNReal) *
          volume (⋃ j ∈ S k, lowAtom K j) ≤
        ∫⁻ r in Icc (b 0) (switch 32), ENNReal.ofReal r *
          (radialSuperlevelOuter
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r) :
    (c : ENNReal) * volume (⋃ j : Fin 32, lowClass K j) ≤
      ∫⁻ r in Icc (b 0) (switch 32), ENNReal.ofReal r *
        (radialSuperlevelOuter
          (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r := by
  rw [← iUnion_lowAtom_range K]
  exact (measure_biUnion_atoms_le_weighted_classes volume (lowAtom K) 32
    I S d c hS (lowAtom_pairwiseDisjoint K) hcover (by simp)).trans hweighted

/-- Abstract finite ledger: this is the exact remaining schedule interface.
`S k` records which disjoint low atoms are paid in ledger row `k`; `d k` is
its nonnegative integrated window weight.  The sole analytic interface
`hweighted` says that the integrated fixed-window bounds dominate those rows. -/
theorem finiteLowLedger_to_outer
    {E : Set Plane} (K : StarShapedKakeya E)
    {κ : Type*} (I : Finset κ) (S : κ → Finset ℕ)
    (d : κ → NNReal) (c : NNReal)
    (hS : ∀ k ∈ I, S k ⊆ Finset.range 32)
    (hcover : ∀ j ∈ Finset.range 32,
      c ≤ ∑ k ∈ I.filter (fun k => j ∈ S k), d k)
    (hweighted :
      ∑ k ∈ I, (d k : ENNReal) *
          volume (⋃ j ∈ S k, lowAtom K j) ≤
        ∫⁻ r in Icc (b 0) (switch 32), ENNReal.ofReal r *
          (radialSuperlevelOuter
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r) :
    (c : ENNReal) * volume (⋃ j : Fin 32, lowClass K j) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
  rw [← iUnion_lowAtom_range K]
  calc
    _ ≤ ∑ k ∈ I, (d k : ENNReal) * volume (⋃ j ∈ S k, lowAtom K j) :=
      measure_biUnion_atoms_le_weighted_classes volume (lowAtom K) 32 I S d c
        hS (lowAtom_pairwiseDisjoint K) hcover (by simp)
    _ ≤ ∫⁻ r in Icc (b 0) (switch 32), ENNReal.ofReal r *
          (radialSuperlevelOuter
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r :=
      hweighted
    _ ≤ _ := K.selectedTriangleUnion_leftLim_lintegral_le (b_pos 0)

/-- The concrete coefficient used by the 141/2000 witness. -/
def commonNN : NNReal := ⟨common, by norm_num [common]⟩

/-- Concrete low aggregate theorem.  The only remaining 32-row schedule
interfaces are the finite coverage ledger and its integrated-window estimate. -/
theorem common_mul_lowUnion_le_outer
    {E : Set Plane} (K : StarShapedKakeya E)
    {κ : Type*} (I : Finset κ) (S : κ → Finset ℕ)
    (d : κ → NNReal)
    (hS : ∀ k ∈ I, S k ⊆ Finset.range 32)
    (hcover : ∀ j ∈ Finset.range 32,
      commonNN ≤ ∑ k ∈ I.filter (fun k => j ∈ S k), d k)
    (hweighted :
      ∑ k ∈ I, (d k : ENNReal) *
          volume (⋃ j ∈ S k, lowAtom K j) ≤
        ∫⁻ r in Icc (b 0) (switch 32), ENNReal.ofReal r *
          (radialSuperlevelOuter
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r) :
    ENNReal.ofReal common * volume (⋃ j : Fin 32, lowClass K j) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num [common])]
  exact finiteLowLedger_to_outer K I S d commonNN hS hcover hweighted

end
end StarKakeyaLower.Witness141
