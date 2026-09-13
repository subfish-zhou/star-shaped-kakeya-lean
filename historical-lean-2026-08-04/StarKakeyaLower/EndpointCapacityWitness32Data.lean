import StarKakeyaLower.EndpointCapacityClasses
import StarKakeyaLower.EndpointCapacityLogBound

/-!
# Frozen 32-segment endpoint-capacity witness data

These are literal rational values.  The external JSON/Python files are only
generators and audit aids; every property used downstream is proved again by
Lean.
-/

namespace StarKakeyaLower
namespace Witness141

noncomputable section

def eta : ℝ := 141046 / 1000000

def target : ℝ := 141 / 2000

def common : ℝ := 22447 / 1000000

def piLower : ℝ := 333 / 106

/-- Low-class upper cuts. -/
def b : Fin 32 → ℝ := ![
    (13613/500000 : ℝ),
    (3859/100000 : ℝ),
    (11831/250000 : ℝ),
    (27341/500000 : ℝ),
    (61151/1000000 : ℝ),
    (66981/1000000 : ℝ),
    (72321/1000000 : ℝ),
    (38633/500000 : ℝ),
    (20471/250000 : ℝ),
    (3449/40000 : ℝ),
    (90323/1000000 : ℝ),
    (1472/15625 : ℝ),
    (979/10000 : ℝ),
    (101419/1000000 : ℝ),
    (52389/500000 : ℝ),
    (107987/1000000 : ℝ),
    (55529/500000 : ℝ),
    (28499/250000 : ℝ),
    (116807/1000000 : ℝ),
    (14937/125000 : ℝ),
    (61033/500000 : ℝ),
    (124519/1000000 : ℝ),
    (63427/500000 : ℝ),
    (129071/1000000 : ℝ),
    (65583/500000 : ℝ),
    (26627/200000 : ℝ),
    (134969/1000000 : ℝ),
    (8541/62500 : ℝ),
    (69087/500000 : ℝ),
    (139487/1000000 : ℝ),
    (140523/1000000 : ℝ),
    (70523/500000 : ℝ)]

/-- Outer radii of the 32 fixed windows. -/
def outerRadius : Fin 32 → ℝ := ![
    (1/2 : ℝ),
    (25037/50000 : ℝ),
    (250743/500000 : ℝ),
    (251117/500000 : ℝ),
    (502981/1000000 : ℝ),
    (20149/40000 : ℝ),
    (252233/500000 : ℝ),
    (505203/1000000 : ℝ),
    (252967/500000 : ℝ),
    (25333/50000 : ℝ),
    (25369/50000 : ℝ),
    (127023/250000 : ℝ),
    (508797/1000000 : ℝ),
    (254747/500000 : ℝ),
    (255091/500000 : ℝ),
    (25543/50000 : ℝ),
    (63941/125000 : ℝ),
    (102437/200000 : ℝ),
    (51283/100000 : ℝ),
    (256731/500000 : ℝ),
    (514081/1000000 : ℝ),
    (128671/250000 : ℝ),
    (515271/1000000 : ℝ),
    (515841/1000000 : ℝ),
    (51639/100000 : ℝ),
    (258459/500000 : ℝ),
    (517421/1000000 : ℝ),
    (64737/125000 : ℝ),
    (259169/500000 : ℝ),
    (25937/50000 : ℝ),
    (129773/250000 : ℝ),
    (519371/1000000 : ℝ)]

/-- Radial switch points, including both endpoints. -/
def switch : Fin 33 → ℝ := ![
    (13613/500000 : ℝ),
    (169921/500000 : ℝ),
    (344933/1000000 : ℝ),
    (349939/1000000 : ℝ),
    (44361/125000 : ℝ),
    (179897/500000 : ℝ),
    (364671/1000000 : ℝ),
    (184763/500000 : ℝ),
    (11699/31250 : ℝ),
    (94801/250000 : ℝ),
    (9601/25000 : ℝ),
    (388883/1000000 : ℝ),
    (19687/50000 : ℝ),
    (79723/200000 : ℝ),
    (403517/1000000 : ℝ),
    (102113/250000 : ℝ),
    (103357/250000 : ℝ),
    (418453/1000000 : ℝ),
    (423537/1000000 : ℝ),
    (42869/100000 : ℝ),
    (433923/1000000 : ℝ),
    (439251/1000000 : ℝ),
    (444691/1000000 : ℝ),
    (56283/125000 : ℝ),
    (91199/200000 : ℝ),
    (461917/1000000 : ℝ),
    (18723/40000 : ℝ),
    (474531/1000000 : ℝ),
    (3851/8000 : ℝ),
    (30547/62500 : ℝ),
    (19877/40000 : ℝ),
    (63309/125000 : ℝ),
    (519371/1000000 : ℝ)]

/-- Lower cut of class `j`, with zero for the initial class. -/
def classLower (j : Fin 32) : ℝ :=
  if h : j.1 = 0 then 0 else b ⟨j.1 - 1, by omega⟩

@[simp] theorem b_last : b ⟨31, by omega⟩ = eta := by
  norm_num [b, eta]

@[simp] theorem switch_zero : switch 0 = b 0 := by
  norm_num [switch, b]

/-- All class upper cuts are positive. -/
theorem b_pos (j : Fin 32) : 0 < b j := by
  fin_cases j <;> norm_num [b]

/-- Every frozen class cut lies below the final cutoff. -/
theorem b_le_eta (j : Fin 32) : b j ≤ eta := by
  fin_cases j <;> norm_num [b, eta]

/-- Every window stays below its outer radius. -/
theorem switch_succ_le_outerRadius (j : Fin 32) :
    switch ⟨j.1 + 1, by omega⟩ ≤ outerRadius j := by
  fin_cases j <;> norm_num [switch, outerRadius]

/-- Frozen unit-chord geometry budget `R_j² ≤ 1/4 + a_j²`. -/
theorem outerRadius_sq_le_quarter_add_classLower_sq (j : Fin 32) :
    outerRadius j ^ 2 ≤ 1 / 4 + classLower j ^ 2 := by
  fin_cases j <;> norm_num [outerRadius, classLower, b]

/-- The final target is below the height branch. -/
theorem target_lt_eta_half : target < eta / 2 := by
  norm_num [target, eta]

/-- The rational lower bound used in the final comparison is below `π`. -/
theorem piLower_lt_pi : piLower < Real.pi := by
  have h : piLower < (3.14159265358979323846 : ℝ) := by
    norm_num [piLower]
  exact h.trans Real.pi_gt_d20

/-- The certified common payment times the rational lower bound for `π`
exceeds the target. -/
theorem target_lt_common_mul_piLower : target < common * piLower := by
  norm_num [target, common, piLower]

/-- The common coefficient times the true projective mass exceeds the target. -/
theorem target_lt_common_mul_pi : target < common * Real.pi := by
  exact target_lt_common_mul_piLower.trans
    (mul_lt_mul_of_pos_left piLower_lt_pi (by norm_num [common]))

/-- ENNReal form of the final projective-mass comparison. -/
theorem ofReal_target_lt_common_mul_projectiveVolume :
    ENNReal.ofReal target <
      ENNReal.ofReal common *
        MeasureTheory.volume (Set.univ : Set ProjectiveDirection) := by
  rw [show MeasureTheory.volume (Set.univ : Set ProjectiveDirection) =
      ENNReal.ofReal Real.pi by
    simp [ProjectiveDirection, AddCircle.measure_univ],
    ← ENNReal.ofReal_mul (by norm_num [common])]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by norm_num [common]) Real.pi_pos)).2 target_lt_common_mul_pi

end
end Witness141
end StarKakeyaLower
