import StarKakeyaLower.OneTenthSectionBoundsLowBank
import StarKakeyaLower.OneTenthHighTailSupports

/-! Actual source partition and once-only physical radial ledger. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.GlobalAssembly
noncomputable section
open Sources SectionBounds

/-- L, F, D0, D1, ... without changing any source boundary. -/
def sourceCut (o : Plane) (c : ℝ → Plane) : ℕ → Set ℝ
  | 0 => L o c
  | 1 => F o c
  | n+2 => D o c n

/-- The physical support assigned to each actual source. -/
def radialSupport : ℕ → Set ℝ
  | 0 => Ioo 0 (1/2)
  | 1 => Ico (1/2) (4/5)
  | 2 => Ico (4/5) (6/5)
  | n+3 => highTailDyadicSupport n

theorem measurableSet_sourceCut (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (n : ℕ) : MeasurableSet (sourceCut o c n) := by
  rcases n with _ | _ | n
  · exact measurableSet_L o hc
  · exact measurableSet_F o hc
  · exact measurableSet_D o hc n

theorem sourceCut_subset_chart (o : Plane) (c : ℝ → Plane) (n : ℕ) :
    sourceCut o c n ⊆ chart := by
  rcases n with _ | _ | n <;> exact inter_subset_left

theorem pairwise_disjoint_sourceCut (o : Plane) (c : ℝ → Plane) :
    Pairwise (fun n k => Disjoint (sourceCut o c n) (sourceCut o c k)) := by
  intro n k h
  rcases n with _ | _ | n <;> rcases k with _ | _ | k
  · exact (h rfl).elim
  · exact disjoint_L_F o c
  · exact disjoint_L_D o c k
  · exact (disjoint_L_F o c).symm
  · exact (h rfl).elim
  · exact disjoint_F_D o c k
  · exact (disjoint_L_D o c n).symm
  · exact (disjoint_F_D o c n).symm
  · exact pairwise_disjoint_D o c (by omega)

theorem sourceCut_partition (o : Plane) (c : ℝ → Plane) :
    (⋃ n, sourceCut o c n) = chart := by
  apply Subset.antisymm
  · exact iUnion_subset (sourceCut_subset_chart o c)
  · intro q hq
    rw [← direction_partition o c] at hq
    rcases hq with (hL | hF) | hD
    · exact mem_iUnion.mpr ⟨0,hL⟩
    · exact mem_iUnion.mpr ⟨1,hF⟩
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hD
      exact mem_iUnion.mpr ⟨n+2,hn⟩

/-- Total actual direction mass is pi, with Haar/chart normalization proved. -/
theorem sourceCut_mass_sum (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    (∑' n, mass (sourceCut o c n)) = ENNReal.ofReal Real.pi := by
  simp_rw [mass_eq_volume (measurableSet_sourceCut o hc _) (sourceCut_subset_chart o c _)]
  rw [← measure_iUnion (pairwise_disjoint_sourceCut o c) (measurableSet_sourceCut o hc),
    sourceCut_partition]
  simp [chart]

theorem measurableSet_radialSupport (n : ℕ) : MeasurableSet (radialSupport n) := by
  rcases n with _ | _ | _ | n
  · exact measurableSet_Ioo
  · exact measurableSet_Ico
  · exact measurableSet_Ico
  · exact measurableSet_highTailDyadicSupport n

theorem pairwise_disjoint_radialSupport :
    Pairwise (fun n k => Disjoint (radialSupport n) (radialSupport k)) := by
  intro n k h
  rcases n with _ | _ | _ | n <;> rcases k with _ | _ | _ | k
  · exact (h rfl).elim
  · exact disjoint_left.mpr (by intro r hr hs; exact not_lt_of_ge hs.1 hr.2)
  · exact disjoint_left.mpr (by intro r hr hs; linarith [hr.2,hs.1])
  · exact (highTailDyadicSupport_disjoint_low k).symm
  · exact disjoint_left.mpr (by intro r hr hs; exact not_lt_of_ge hr.1 hs.2)
  · exact (h rfl).elim
  · exact disjoint_left.mpr (by intro r hr hs; exact not_lt_of_ge hs.1 hr.2)
  · exact (highTailDyadicSupport_disjoint_F k).symm
  · exact disjoint_left.mpr (by intro r hr hs; linarith [hr.1,hs.2])
  · exact disjoint_left.mpr (by intro r hr hs; exact not_lt_of_ge hr.1 hs.2)
  · exact (h rfl).elim
  · exact (highTailDyadicSupport_disjoint_D0 k).symm
  · exact highTailDyadicSupport_disjoint_low n
  · exact highTailDyadicSupport_disjoint_F n
  · exact highTailDyadicSupport_disjoint_D0 n
  · exact pairwise_disjoint_highTailDyadicSupport (by omega)

/-- Unconditional actual support assembly; never adds independent area bounds. -/
theorem actual_banks_sum_le_volume (o : Plane) {G : Set Plane} (hG : IsOpen G) :
    (∑' n, radialBank (centeredCoordinateEnvelope o G) (radialSupport n)) ≤ volume G :=
  centered_disjoint_radialBank_sum_le_volume o hG radialSupport
    measurableSet_radialSupport pairwise_disjoint_radialSupport

/-- The three already proved low banks fill exactly the assigned low support. -/
theorem low_banks_eq (W : Set CoordinatePlane) :
    radialBank W (Ioo 0 (1/5 : ℝ)) + radialBank W (Ico (1/5 : ℝ) (7/20)) +
      radialBank W (Ico (7/20 : ℝ) (1/2)) = radialBank W (radialSupport 0) := by
  have hd : Disjoint (Ioo (0 : ℝ) (1/5)) (Ico (1/5 : ℝ) (7/20)) :=
    disjoint_left.mpr (by intro r hr hs; exact not_lt_of_ge hs.1 hr.2)
  have hd' : Disjoint (Ioo (0 : ℝ) (1/5) ∪ Ico (1/5 : ℝ) (7/20))
      (Ico (7/20 : ℝ) (1/2)) := by
    apply disjoint_left.mpr
    intro r hr hs
    rcases hr with hr | hr <;> linarith [hr.2,hs.1]
  rw [← radialBank_union W measurableSet_Ico hd, ← radialBank_union W measurableSet_Ico hd']
  congr 1
  ext r
  simp only [radialSupport, mem_union, mem_Ioo, mem_Ico]
  constructor
  · rintro ((h | h) | h) <;> constructor <;> linarith [h.1,h.2]
  · intro h
    by_cases h1 : r < 1/5
    · exact Or.inl (Or.inl ⟨h.1,h1⟩)
    · by_cases h2 : r < 7/20
      · exact Or.inl (Or.inr ⟨le_of_not_gt h1,h2⟩)
      · exact Or.inr ⟨le_of_not_gt h2,h.2⟩

/-- Safe conversion uses finite Haar mass; no real conversion of volume G. -/
theorem ofReal_mul_mass (a : ℝ) (V : Set ℝ) :
    ENNReal.ofReal (a*(mass V).toReal) = ENNReal.ofReal a * mass V := by
  rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (mass_ne_top V)]

theorem actual_low_bank_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ chart, triangle o c q ⊆ G)
    (hh : ∀ q ∈ chart, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal (1/(10*Real.pi)) * mass (sourceCut o c 0) ≤
      radialBank (centeredCoordinateEnvelope o G) (radialSupport 0) := by
  have H := low_radial_price o hc (measurableSet_L o hc) Subset.rfl G hG
    (fun q hq => htri q hq.1) (fun q hq => hh q hq.1)
  rw [low_banks_eq, ofReal_mul_mass] at H
  exact (mul_le_mul_right' (ENNReal.ofReal_le_ofReal lowCoefficient_gt_target.le) _).trans H

/-- Uniform target prices of the actual source partition sum to exactly 1/10. -/
theorem target_prices_sum (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    (∑' n, ENNReal.ofReal (1/(10*Real.pi)) * mass (sourceCut o c n)) =
      ENNReal.ofReal (1/10 : ℝ) := by
  rw [ENNReal.tsum_mul_left, sourceCut_mass_sum o hc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end
end StarKakeyaLower.OneTenth.GlobalAssembly
