import StarKakeyaLower.OneTenth

/-! Fresh public-import audit: unconditional outer area and boundary controls. -/
open Set MeasureTheory Real
open scoped ENNReal
open StarKakeyaLower StarKakeyaLower.OneTenth
open Sources SectionBounds GlobalAssembly

#check @StarShapedKakeya.one_tenth_le_outerArea
#print StarShapedKakeya
#print UnitNeedle
#print UnitNeedle.HasDirection
#print UnitNeedle.carrier
#print axioms StarShapedKakeya.one_tenth_le_outerArea
#check @actual_bank_price
#check @small_height_one_tenth
#check @open_cover_one_tenth
#print axioms tail_bounded_kernel_lower
#print axioms actual_tail_radial_price
#print axioms actual_tail_bank_price
#print axioms actual_F_bank_price
#print axioms actual_D0_bank_price
#print axioms actual_bank_price
#print axioms small_height_one_tenth
#print axioms open_cover_one_tenth

example {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure E := K.one_tenth_le_outerArea

#check @sourceCut_mass_sum
#check @target_prices_sum
#check @actual_banks_sum_le_volume
#check @actual_low_bank_price
#print axioms sourceCut_mass_sum
#print axioms target_prices_sum
#print axioms pairwise_disjoint_sourceCut
#print axioms pairwise_disjoint_radialSupport
#print axioms actual_banks_sum_le_volume
#print axioms low_banks_eq
#print axioms ofReal_mul_mass
#print axioms actual_low_bank_price

example (o : Plane) (c : ℝ → Plane) {q : ℝ} (hq : q ∈ chart)
    (he : M o c q = 99/100) : q ∉ sourceCut o c 0 ∧ q ∈ sourceCut o c 1 := by
  norm_num [sourceCut,L,F,hq,he]
example (o : Plane) (c : ℝ → Plane) {q : ℝ} (hq : q ∈ chart)
    (he : M o c q = 8/5) : q ∉ sourceCut o c 1 ∧ q ∈ sourceCut o c 2 := by
  norm_num [sourceCut,F,D,dyadicScale,hq,he]
example (o : Plane) (c : ℝ → Plane) {q : ℝ} (hq : q ∈ chart)
    (he : M o c q = 16/5) : q ∉ sourceCut o c 2 ∧ q ∈ sourceCut o c 3 := by
  norm_num [sourceCut,D,dyadicScale,hq,he]
example : (1/2 : ℝ) ∉ radialSupport 0 ∧ (1/2 : ℝ) ∈ radialSupport 1 := by
  norm_num [radialSupport]
example : (4/5 : ℝ) ∉ radialSupport 1 ∧ (4/5 : ℝ) ∈ radialSupport 2 := by
  norm_num [radialSupport]
example : (6/5 : ℝ) ∉ radialSupport 2 := by norm_num [radialSupport]
example : radialSupport 3 = Ico (8/5 : ℝ) (12/5) := highTailDyadicSupport_first
example : (0 : ℝ) ∉ radialSupport 0 := by simp [radialSupport]
example : (ENNReal.ofReal (1/10 : ℝ)) ≤ (⊤ : ℝ≥0∞) := le_top
example (o : Plane) {c : ℝ → Plane} (hc : Measurable c) :
    (∑' n, ENNReal.ofReal (1/(10*Real.pi)*(mass (sourceCut o c n)).toReal)) =
      ENNReal.ofReal (1/10 : ℝ) := by
  simp_rw [ofReal_mul_mass]
  exact target_prices_sum o hc
