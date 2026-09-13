import Mathlib

/-!
# Exact non-iterative `π / 56` certificate kernel

The candidate in this file avoids Li's iterative Remark 4.1.  The proved
statements are exact rational identities and inequalities, plus the elementary
height comparison using Mathlib's rigorous bound on `Real.pi`.

The atan/log remainder theorems, branch monotonicity, radical comparisons and
geometric-measure assembly are separate layers.
-/

namespace StarKakeyaLower

noncomputable section

def altA : ℝ := 449 / 4000

def altRLambda : ℝ := 13 / 56

def altR₀ : ℝ := 49 / 100

def altP : ℝ := 333 / 400

def altLambda : ℝ := 7220 / 10577

def altGConst : ℝ := (1 + 2 * altRLambda) / (1 - 2 * altRLambda)

def altSwitchLeft : ℝ := 2241 / 10000

def altSwitchRight : ℝ := 2353 / 10000

def altGRight : ℝ :=
  (1 + 2 * altSwitchRight) / (1 - 2 * altSwitchRight)

def altLogX : ℝ :=
  (1 + 2 * altR₀) / (1 + 2 * altSwitchRight) - 1

def altLogUpper9 : ℝ :=
  altLogX
    - altLogX ^ 2 / 2
    + altLogX ^ 3 / 3
    - altLogX ^ 4 / 4
    + altLogX ^ 5 / 5
    - altLogX ^ 6 / 6
    + altLogX ^ 7 / 7
    - altLogX ^ 8 / 8
    + altLogX ^ 9 / 9

def altLogUpper7 : ℝ :=
  altLogX
    - altLogX ^ 2 / 2
    + altLogX ^ 3 / 3
    - altLogX ^ 4 / 4
    + altLogX ^ 5 / 5
    - altLogX ^ 6 / 6
    + altLogX ^ 7 / 7

def altILeft : ℝ :=
  (altSwitchLeft ^ 2 - altA ^ 2) / (2 * altGConst)

def altIMiddle : ℝ :=
  (altSwitchRight ^ 2 - altSwitchLeft ^ 2) / (2 * altGRight)

def altIRight (logUpper : ℝ) : ℝ :=
  ((-altR₀ ^ 2 / 2 + altR₀)
      - (-altSwitchRight ^ 2 / 2 + altSwitchRight))
    - logUpper / 2

def altILower9 : ℝ := altILeft + altIMiddle + altIRight altLogUpper9

def altILower7 : ℝ := altILeft + altIMiddle + altIRight altLogUpper7

def altK : ℝ :=
  1 - ((1 / 2) * altR₀ * (2 * altR₀ - 1) ^ 2) / (2 * altR₀ ^ 2)

def altCaseI (integralLower : ℝ) : ℝ :=
  altP * altK * integralLower
    + ((1 / 2) * altR₀ * (2 * altR₀ - 1) ^ 2) / 4

def altR₁Lower : ℝ := 18563 / 10000

def altCaseIIX : ℝ := altA / (altR₁Lower - 1)

def altCaseIIThreshold : ℝ := 7 * (1 - altP) * altA

def altCaseIIArcsinUpper : ℝ :=
  altCaseIIX + altCaseIIX ^ 3 / (3 * (99 / 100) * (199 / 100))

theorem alt_rLambda_affine_identity :
    altLambda * altA + (1 - altLambda) * altR₀ = altRLambda := by
  norm_num [altLambda, altA, altR₀, altRLambda]

theorem alt_gConst_exact : altGConst = 41 / 15 := by
  norm_num [altGConst, altRLambda]

theorem alt_logX_exact : altLogX = 283 / 817 := by
  norm_num [altLogX, altR₀, altSwitchRight]

theorem alt_iLower9_exact :
    altILower9 =
      2393594915164504298667197428312219853 /
        111709895934537651989183224893600000000 := by
  norm_num [
    altILower9,
    altILeft,
    altIMiddle,
    altIRight,
    altLogUpper9,
    altLogX,
    altA,
    altR₀,
    altRLambda,
    altGConst,
    altGRight,
    altSwitchLeft,
    altSwitchRight
  ]

theorem alt_caseI_margin_exact :
    altCaseI altILower9 - 1 / 56 =
      116569153710187543639191405603945643017 /
        72983798677231265966266373597152000000000000 := by
  rw [alt_iLower9_exact]
  norm_num [
    altCaseI,
    altK,
    altP,
    altR₀
  ]

theorem alt_caseI_strict : 1 / 56 < altCaseI altILower9 := by
  have hmargin := alt_caseI_margin_exact
  have hpositive :
      (0 : ℝ) <
        116569153710187543639191405603945643017 /
          72983798677231265966266373597152000000000000 := by
    norm_num
  linarith

theorem alt_caseI_seven_negative_control_exact :
    altCaseI altILower7 - 1 / 56 =
      -(641269113124626808494726855865047 /
        109340826106844106743731168000000000000) := by
  norm_num [
    altCaseI,
    altILower7,
    altILeft,
    altIMiddle,
    altIRight,
    altLogUpper7,
    altLogX,
    altK,
    altA,
    altP,
    altR₀,
    altRLambda,
    altGConst,
    altGRight,
    altSwitchLeft,
    altSwitchRight
  ]

theorem alt_caseI_seven_negative_control :
    altCaseI altILower7 < 1 / 56 := by
  have hmargin := alt_caseI_seven_negative_control_exact
  have hpositive :
      (0 : ℝ) <
        641269113124626808494726855865047 /
          109340826106844106743731168000000000000 := by
    norm_num
  linarith

theorem alt_caseII_x_exact : altCaseIIX = 2245 / 17126 := by
  norm_num [altCaseIIX, altA, altR₁Lower]

theorem alt_caseII_sqrt_square_margin :
    (99 / 100 : ℝ) ^ 2 < 1 - altCaseIIX ^ 2 := by
  norm_num [altCaseIIX, altA, altR₁Lower]

theorem alt_caseII_threshold_exact :
    altCaseIIThreshold = 210581 / 1600000 := by
  norm_num [altCaseIIThreshold, altP, altA]

theorem alt_caseII_margin_exact :
    altCaseIIThreshold - altCaseIIArcsinUpper =
      8595227380165644121 / 59375508286970145600000 := by
  norm_num [
    altCaseIIThreshold,
    altCaseIIArcsinUpper,
    altCaseIIX,
    altA,
    altP,
    altR₁Lower
  ]

theorem alt_caseII_rational_strict :
    altCaseIIArcsinUpper < altCaseIIThreshold := by
  have hmargin := alt_caseII_margin_exact
  have hpositive :
      (0 : ℝ) <
        8595227380165644121 / 59375508286970145600000 := by
    norm_num
  linarith

theorem alt_height_pi_rational_margin :
    28 * altA - 22 / 7 = 1 / 7000 := by
  norm_num [altA]

theorem alt_height_strict :
    Real.pi / 56 < altA / 2 := by
  have hpi : Real.pi < (3143 / 1000 : ℝ) := by
    exact lt_trans Real.pi_lt_d4 (by norm_num)
  norm_num [altA] at hpi ⊢
  linarith

end

end StarKakeyaLower
