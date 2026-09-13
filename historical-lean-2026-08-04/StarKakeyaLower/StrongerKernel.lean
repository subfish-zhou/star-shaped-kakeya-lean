import Mathlib

/-!
# Exact kernel for the stronger `100 * π / 5599` paper certificate

This file formalizes the fixed rational parameters and the exact margins used
by the stronger certificate.  The transcendental inequalities which justify the
stored integral and arcsine bounds, and the geometric/outer-measure assembly,
are separate layers; this file does not state the universal Kakeya theorem,
which is `StarKakeyaLower.universal_strong_lower_bound` in `UniversalAssembly`.
-/

namespace StarKakeyaLower

noncomputable section

def strongTarget : ℝ := 100 / 5599

def strongA : ℝ := 1123 / 10000

def strongRLambda : ℝ := 581 / 2500

def strongR₀ : ℝ := 2453 / 5000

def strongP : ℝ := 83301 / 100000

def strongLambda : ℝ := 2582 / 3783

def strongK : ℝ := 12262791 / 12265000

def strongILower : ℝ :=
  22793357350571006116275623711763 /
    1064174925446566790615478200000000

def strongILowerMutation : ℝ :=
  498758910510792926599557794477899793 /
    23295486737725095717716052500200000000

def strongF₀ : ℝ :=
  (1 / 2) * strongR₀ * (2 * strongR₀ - 1) ^ 2

def strongCaseI (integralLower : ℝ) : ℝ :=
  strongP * strongK * integralLower + strongF₀ / 4

def strongR₁Lower : ℝ := 185813 / 100000

def strongCaseIIX : ℝ := strongA / (strongR₁Lower - 1)

def strongSqrtLower : ℝ := 9914 / 10000

def strongArcsinUpper : ℝ :=
  strongCaseIIX
    + strongCaseIIX ^ 3 /
      (3 * strongSqrtLower * (1 + strongSqrtLower))

def strongCaseIIThreshold : ℝ :=
  (1 - strongP) * strongA / (8 * strongTarget)

def strongPiUpper : ℝ :=
  314159265358979323847 / 100000000000000000000

/-- The radical occurring in the fixed geometric parameter `d`. -/
def strongRadicand : ℝ :=
  4 * strongRLambda ^ 2 * (1 + strongA ^ 2) - strongA ^ 2

/-- The actual (not merely rationally enclosed) fixed `d`. -/
def strongD : ℝ :=
  strongA * (1 - Real.sqrt strongRadicand) / (2 * (1 + strongA ^ 2))

/-- The radicand and denominator occurring in `strongR₁`. -/
def strongR₁Radicand : ℝ := strongRLambda ^ 2 - strongD ^ 2

def strongR₁Denominator : ℝ := 1 - 2 * Real.sqrt strongR₁Radicand

/-- The actual geometric radius and exterior cutoff. -/
def strongR₁ : ℝ := Real.sqrt (1 + 4 * strongD ^ 2) / strongR₁Denominator

def strongRho : ℝ := strongR₁ - 1

/-- Arithmetic domain certificate for the one fixed stronger parameter tuple.
It contains only numerical/radical facts proved in this file.  In particular,
it deliberately contains no endpoint-containment or outer-measure field: those
geometric statements are proved in their own modules and are assembled by
`StarKakeyaLower.universal_strong_lower_bound`. -/
structure StrongParameterDomain where
  r₀_ge_three_twentieths : (3 / 20 : ℝ) ≤ strongR₀
  a_pos : 0 < strongA
  a_lt_rLambda : strongA < strongRLambda
  rLambda_lt_r₀ : strongRLambda < strongR₀
  r₀_lt_half : strongR₀ < 1 / 2
  p_pos : 0 < strongP
  p_lt_one : strongP < 1
  lambda_pos : 0 < strongLambda
  lambda_lt_one : strongLambda < 1
  affine_identity :
    strongLambda * strongA + (1 - strongLambda) * strongR₀ = strongRLambda
  radicand_nonneg : 0 ≤ strongRadicand
  radicand_lt_one : strongRadicand < 1
  d_pos : 0 < strongD
  d_lt_half_a : strongD < strongA / 2
  d_gt_rational_lower : (302738 / 10000000 : ℝ) < strongD
  d_lt_rational_upper : strongD < 302739 / 10000000
  r₁_radicand_nonneg : 0 ≤ strongR₁Radicand
  r₁_radicand_lt_quarter : strongR₁Radicand < (1 / 2 : ℝ) ^ 2
  r₁_denominator_pos : 0 < strongR₁Denominator
  r₁_gt_rational_lower : strongR₁Lower < strongR₁
  rho_gt_half : 1 / 2 < strongRho
  rho_gt_a : strongA < strongRho
  r₁_gt_inv_rho : 1 / strongRho < strongR₁

theorem strong_lambda_affine_identity :
    strongLambda * strongA + (1 - strongLambda) * strongR₀ =
      strongRLambda := by
  norm_num [strongLambda, strongA, strongR₀, strongRLambda]

theorem strong_target_strictly_improves_pi56 :
    (1 / 56 : ℝ) < strongTarget := by
  norm_num [strongTarget]

theorem strong_k_exact :
    1 - strongF₀ / (2 * strongR₀ ^ 2) = strongK := by
  norm_num [strongF₀, strongR₀, strongK]

theorem strong_caseI_margin_exact :
    strongCaseI strongILower - strongTarget =
      139158989937085958631189100903645702101397 /
        664352167944649011863150962260700000000000000000 := by
  norm_num [
    strongCaseI,
    strongILower,
    strongTarget,
    strongP,
    strongK,
    strongF₀,
    strongR₀
  ]

theorem strong_caseI_strict :
    strongTarget < strongCaseI strongILower := by
  have h := strong_caseI_margin_exact
  have hpos :
      (0 : ℝ) <
        139158989937085958631189100903645702101397 /
          664352167944649011863150962260700000000000000000 := by
    norm_num
  linarith

theorem strong_caseI_mutation_margin_exact :
    strongCaseI strongILowerMutation - strongTarget =
      -(102307073124674754126774830746397279660372227033 /
        14543104472264293417969377841271107700000000000000000) := by
  norm_num [
    strongCaseI,
    strongILowerMutation,
    strongTarget,
    strongP,
    strongK,
    strongF₀,
    strongR₀
  ]

theorem strong_caseI_mutation_fails :
    strongCaseI strongILowerMutation < strongTarget := by
  have h := strong_caseI_mutation_margin_exact
  have hpos :
      (0 : ℝ) <
        102307073124674754126774830746397279660372227033 /
          14543104472264293417969377841271107700000000000000000 := by
    norm_num
  linarith

theorem strong_caseII_x_exact :
    strongCaseIIX = 11230 / 85813 := by
  norm_num [strongCaseIIX, strongA, strongR₁Lower]

theorem strong_caseII_sqrt_square_margin :
    strongSqrtLower ^ 2 < 1 - strongCaseIIX ^ 2 := by
  norm_num [
    strongSqrtLower,
    strongCaseIIX,
    strongA,
    strongR₁Lower
  ]

theorem strong_caseII_margin_exact :
    strongCaseIIThreshold - strongArcsinUpper =
      227923075074420651443585972857 /
        74854501574905182351967200000000000 := by
  norm_num [
    strongCaseIIThreshold,
    strongArcsinUpper,
    strongCaseIIX,
    strongSqrtLower,
    strongA,
    strongR₁Lower,
    strongP,
    strongTarget
  ]

theorem strong_caseII_strict :
    strongArcsinUpper < strongCaseIIThreshold := by
  have h := strong_caseII_margin_exact
  have hpos :
      (0 : ℝ) <
        227923075074420651443585972857 /
          74854501574905182351967200000000000 := by
    norm_num
  linarith

theorem strong_height_rational_margin_exact :
    strongA / (2 * strongPiUpper) - strongTarget =
      22458464102067615300 /
        1758977726744925234219353 := by
  norm_num [strongA, strongPiUpper, strongTarget]

theorem strong_basic_parameter_domain :
    (3 / 20 : ℝ) ≤ strongR₀ ∧ 0 < strongA ∧
      strongA < strongRLambda ∧ strongRLambda < strongR₀ ∧
      strongR₀ < 1 / 2 ∧ 0 < strongP ∧ strongP < 1 ∧
      0 < strongLambda ∧ strongLambda < 1 := by
  norm_num [strongR₀, strongA, strongRLambda, strongP, strongLambda]

theorem strong_radicand_domain :
    0 ≤ strongRadicand ∧ strongRadicand < 1 := by
  norm_num [strongRadicand, strongRLambda, strongA]

theorem strong_d_domain : 0 < strongD ∧ strongD < strongA / 2 := by
  obtain ⟨hQ0, hQ1⟩ := strong_radicand_domain
  have hs0 : 0 ≤ Real.sqrt strongRadicand := Real.sqrt_nonneg _
  have hs1 : Real.sqrt strongRadicand < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using hQ1
  have ha : 0 < strongA := by norm_num [strongA]
  have hbase : 0 < 1 + strongA ^ 2 := by positivity
  constructor
  · rw [strongD]
    exact div_pos (mul_pos ha (sub_pos.mpr hs1)) (by positivity)
  · rw [strongD]
    have hratio :
        (1 - Real.sqrt strongRadicand) / (1 + strongA ^ 2) < 1 := by
      apply (div_lt_iff₀ hbase).2
      nlinarith [sq_nonneg strongA]
    have hid :
        strongA * (1 - Real.sqrt strongRadicand) / (2 * (1 + strongA ^ 2)) =
          strongA / 2 * ((1 - Real.sqrt strongRadicand) / (1 + strongA ^ 2)) := by
      field_simp
    rw [hid]
    nlinarith

theorem strong_d_rational_bounds :
    (302738 / 10000000 : ℝ) < strongD ∧
      strongD < 302739 / 10000000 := by
  obtain ⟨hQ0, hQ1⟩ := strong_radicand_domain
  let dl : ℝ := 302738 / 10000000
  let du : ℝ := 302739 / 10000000
  let cl : ℝ := 1 - dl * (2 * (1 + strongA ^ 2)) / strongA
  let cu : ℝ := 1 - du * (2 * (1 + strongA ^ 2)) / strongA
  have hcl0 : 0 ≤ cl := by norm_num [cl, dl, strongA]
  have hcu0 : 0 ≤ cu := by norm_num [cu, du, strongA]
  have hs_lt_cl : Real.sqrt strongRadicand < cl := by
    apply (Real.sqrt_lt hQ0 hcl0).2
    norm_num [strongRadicand, strongRLambda, strongA, cl, dl]
  have hcu_lt_s : cu < Real.sqrt strongRadicand := by
    apply (Real.lt_sqrt hcu0).2
    norm_num [strongRadicand, strongRLambda, strongA, cu, du]
  have ha : 0 < strongA := by norm_num [strongA]
  have hden : 0 < 2 * (1 + strongA ^ 2) := by positivity
  constructor
  · rw [strongD]
    apply (lt_div_iff₀ hden).2
    dsimp [cl, dl] at hs_lt_cl ⊢
    norm_num [strongA] at hs_lt_cl ⊢
    nlinarith
  · rw [strongD]
    apply (div_lt_iff₀ hden).2
    dsimp [cu, du] at hcu_lt_s ⊢
    norm_num [strongA] at hcu_lt_s ⊢
    nlinarith

theorem strong_r₁_radicand_nonneg : 0 ≤ strongR₁Radicand := by
  obtain ⟨hd0, hdA⟩ := strong_d_domain
  have har : strongA / 2 < strongRLambda := by
    norm_num [strongA, strongRLambda]
  rw [strongR₁Radicand]
  nlinarith

theorem strong_r₁_radicand_lt_quarter :
    strongR₁Radicand < (1 / 2 : ℝ) ^ 2 := by
  have hrlsq : strongRLambda ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    norm_num [strongRLambda]
  rw [strongR₁Radicand]
  nlinarith [sq_nonneg strongD]

theorem strong_r₁_denominator_pos : 0 < strongR₁Denominator := by
  have hx0 := strong_r₁_radicand_nonneg
  have hslt : Real.sqrt strongR₁Radicand < 1 / 2 := by
    exact (Real.sqrt_lt' (by norm_num)).2 strong_r₁_radicand_lt_quarter
  rw [strongR₁Denominator]
  linarith

theorem strong_r₁_gt_rational_lower : strongR₁Lower < strongR₁ := by
  let dl : ℝ := 302738 / 10000000
  let du : ℝ := 302739 / 10000000
  let numLower : ℝ := 1001831 / 1000000
  let t : ℝ := (1 - numLower / strongR₁Lower) / 2
  obtain ⟨hdlow, hdup⟩ := strong_d_rational_bounds
  have ht0 : 0 ≤ t := by norm_num [t, numLower, strongR₁Lower]
  have hd_sq_upper : strongD ^ 2 < du ^ 2 := by
    dsimp [du] at hdup ⊢
    have hd0 := strong_d_domain.1
    nlinarith
  have hbase : t ^ 2 < strongRLambda ^ 2 - du ^ 2 := by
    norm_num [t, numLower, strongR₁Lower, strongRLambda, du]
  have htx : t ^ 2 < strongR₁Radicand := by
    rw [strongR₁Radicand]
    linarith
  have htsqrt : t < Real.sqrt strongR₁Radicand :=
    (Real.lt_sqrt ht0).2 htx
  have hden_lt : strongR₁Lower * strongR₁Denominator < numLower := by
    rw [strongR₁Denominator]
    dsimp [t] at htsqrt
    have hRpos : 0 < strongR₁Lower := by norm_num [strongR₁Lower]
    norm_num [numLower, strongR₁Lower] at htsqrt ⊢
    nlinarith
  have hd_sq_lower : dl ^ 2 < strongD ^ 2 := by
    dsimp [dl] at hdlow ⊢
    nlinarith [strong_d_domain.1]
  have hnum_sq : numLower ^ 2 < 1 + 4 * strongD ^ 2 := by
    have : numLower ^ 2 < 1 + 4 * dl ^ 2 := by
      norm_num [numLower, dl]
    nlinarith
  have hnum : numLower < Real.sqrt (1 + 4 * strongD ^ 2) := by
    apply (Real.lt_sqrt (by norm_num [numLower])).2
    exact hnum_sq
  rw [strongR₁]
  exact (lt_div_iff₀ strong_r₁_denominator_pos).2 (lt_trans hden_lt hnum)

theorem strong_rho_domains :
    1 / 2 < strongRho ∧ strongA < strongRho ∧ 1 / strongRho < strongR₁ := by
  have hR := strong_r₁_gt_rational_lower
  have hhalf : (3 / 2 : ℝ) < strongR₁Lower := by norm_num [strongR₁Lower]
  have hrho : 0 < strongRho := by rw [strongRho]; linarith
  have hrhohalf : (1 / 2 : ℝ) < strongRho := by rw [strongRho]; linarith
  have hrhoa : strongA < strongRho := by
    rw [strongRho]
    norm_num [strongR₁Lower, strongA] at hR ⊢
    linarith
  refine ⟨hrhohalf, hrhoa, ?_⟩
  apply (div_lt_iff₀ hrho).2
  rw [strongRho]
  have hmargin : (1 : ℝ) < strongR₁Lower * (strongR₁Lower - 1) := by
    norm_num [strongR₁Lower]
  nlinarith [sq_nonneg (strongR₁ - strongR₁Lower)]

def strongParameterDomain : StrongParameterDomain := by
  obtain ⟨hr0, ha, harl, hrlr0, hr0h, hp, hp1, hl, hl1⟩ :=
    strong_basic_parameter_domain
  obtain ⟨hQ0, hQ1⟩ := strong_radicand_domain
  obtain ⟨hd0, hdA⟩ := strong_d_domain
  obtain ⟨hdLower, hdUpper⟩ := strong_d_rational_bounds
  obtain ⟨hrhohalf, hrhoa, hRinv⟩ := strong_rho_domains
  exact
    { r₀_ge_three_twentieths := hr0
      a_pos := ha
      a_lt_rLambda := harl
      rLambda_lt_r₀ := hrlr0
      r₀_lt_half := hr0h
      p_pos := hp
      p_lt_one := hp1
      lambda_pos := hl
      lambda_lt_one := hl1
      affine_identity := strong_lambda_affine_identity
      radicand_nonneg := hQ0
      radicand_lt_one := hQ1
      d_pos := hd0
      d_lt_half_a := hdA
      d_gt_rational_lower := hdLower
      d_lt_rational_upper := hdUpper
      r₁_radicand_nonneg := strong_r₁_radicand_nonneg
      r₁_radicand_lt_quarter := strong_r₁_radicand_lt_quarter
      r₁_denominator_pos := strong_r₁_denominator_pos
      r₁_gt_rational_lower := strong_r₁_gt_rational_lower
      rho_gt_half := hrhohalf
      rho_gt_a := hrhoa
      r₁_gt_inv_rho := hRinv }

end

end StarKakeyaLower
