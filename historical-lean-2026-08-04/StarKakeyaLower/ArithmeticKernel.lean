import Mathlib

/-!
# Exact arithmetic kernel for the proposed `π / 56` lower bound

This file formalizes only fixed-rational identities and strict rational
residuals.  It does not formalize the alternating-series remainder, radical
monotonicity, inverse-trigonometric estimates, Li's geometric containment, or
the outer-measure iteration.
-/

namespace StarKakeyaLower

noncomputable section

def a : ℝ := 9 / 80

def r₀ : ℝ := 49 / 100

def rLambda : ℝ := 6 / 25

def lambda : ℝ := 100 / 151

def p : ℝ := 59 / 70

def f (r : ℝ) : ℝ := (1 / 2) * r * (2 * r - 1) ^ 2

def k : ℝ := 1 - f r₀ / (2 * r₀ ^ 2)

def gLeft : ℝ := (1 + 2 * rLambda) / (1 - 2 * rLambda)

def logX : ℝ := 25 / 74

def logUpper7 : ℝ :=
  logX
    - logX ^ 2 / 2
    + logX ^ 3 / 3
    - logX ^ 4 / 4
    + logX ^ 5 / 5
    - logX ^ 6 / 6
    + logX ^ 7 / 7

def logUpper5 : ℝ :=
  logX
    - logX ^ 2 / 2
    + logX ^ 3 / 3
    - logX ^ 4 / 4
    + logX ^ 5 / 5

def integralLower7 : ℝ := 1973083 / 11840000 - logUpper7 / 2

def integralLower5 : ℝ := 1973083 / 11840000 - logUpper5 / 2

def qLower : ℝ := k * (a / 2) ^ 2

def caseILower (integralLower : ℝ) : ℝ :=
  (p * k * integralLower + f r₀ / 4) / (1 - qLower)

def caseIIX : ℝ := 23571 / 191120

def arcsinRationalUpper : ℝ :=
  caseIIX + caseIIX ^ 3 / (3 * (99 / 100) * (199 / 100))

def thirdBranchX₀ : ℝ := 2 * rLambda

def atanUpper5 : ℝ :=
  thirdBranchX₀ - thirdBranchX₀ ^ 3 / 3 + thirdBranchX₀ ^ 5 / 5

theorem rLambda_affine_identity :
    lambda * a + (1 - lambda) * r₀ = rLambda := by
  norm_num [lambda, a, r₀, rLambda]

theorem gLeft_exact : gLeft = 37 / 13 := by
  norm_num [gLeft, rLambda]

theorem f_r₀_exact : f r₀ = 49 / 500000 := by
  norm_num [f, r₀]

theorem k_exact : k = 4899 / 4900 := by
  norm_num [k, f, r₀]

theorem qLower_exact : qLower = 396819 / 125440000 := by
  norm_num [qLower, k, f, r₀, a]

theorem integralLower7_exact :
    integralLower7 = 4488983109805129 / 212647404777920000 := by
  norm_num [integralLower7, logUpper7, logX]

theorem caseI_seven_margin_exact :
    caseILower integralLower7 - 1 / 56 =
      7536287922839272197 / 581658610855562523577000 := by
  norm_num [
    caseILower,
    integralLower7,
    logUpper7,
    logX,
    p,
    k,
    f,
    r₀,
    qLower,
    a
  ]

theorem caseI_seven_strict :
    1 / 56 < caseILower integralLower7 := by
  have h := caseI_seven_margin_exact
  have hpos :
      (0 : ℝ) < 7536287922839272197 / 581658610855562523577000 := by norm_num
  linarith

theorem caseI_five_negative_control_exact :
    caseILower integralLower5 - 1 / 56 =
      -(3730000102620341 / 60696922764850519000) := by
  norm_num [
    caseILower,
    integralLower5,
    logUpper5,
    logX,
    p,
    k,
    f,
    r₀,
    qLower,
    a
  ]

theorem caseI_five_negative_control :
    caseILower integralLower5 < 1 / 56 := by
  have h := caseI_five_negative_control_exact
  have hpos :
      (0 : ℝ) < 3730000102620341 / 60696922764850519000 := by norm_num
  linarith

theorem caseII_rational_margin_exact :
    99 / 800 - arcsinRationalUpper =
      19428249412827 / 191017952148742400 := by
  norm_num [arcsinRationalUpper, caseIIX]

theorem caseII_rational_strict :
    arcsinRationalUpper < 99 / 800 := by
  have h := caseII_rational_margin_exact
  have hpos : (0 : ℝ) < 19428249412827 / 191017952148742400 := by norm_num
  linarith

theorem caseII_sqrt_square_margin :
    (99 / 100 : ℝ) ^ 2 < 1 - caseIIX ^ 2 := by
  norm_num [caseIIX]

theorem thirdBranch_x₀_exact : thirdBranchX₀ = 12 / 25 := by
  norm_num [thirdBranchX₀, rLambda]

theorem thirdBranch_base_margin_exact :
    (11 / 74) * (157 / 50) - atanUpper5 =
      133869739 / 7226562500 := by
  norm_num [atanUpper5, thirdBranchX₀, rLambda]

theorem thirdBranch_base_rational_strict :
    atanUpper5 < (11 / 74) * (157 / 50) := by
  have h := thirdBranch_base_margin_exact
  have hpos : (0 : ℝ) < 133869739 / 7226562500 := by norm_num
  linarith

theorem derivative_ratio_square_completion (x : ℝ) :
    3 * x ^ 2 - 2 * x + 1 =
      3 * (x - 1 / 3) ^ 2 + 2 / 3 := by
  ring

theorem derivative_ratio_positive (x : ℝ) :
    0 < 3 * x ^ 2 - 2 * x + 1 := by
  rw [derivative_ratio_square_completion]
  positivity

end

end StarKakeyaLower
