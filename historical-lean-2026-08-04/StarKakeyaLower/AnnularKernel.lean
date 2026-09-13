import Mathlib

/-!
# Exact numeric kernel for the joint inner/outer annular certificate

This module fixes the production parameter tuple of `spikes/001-joint-inner-outer/PROOF.md`
(Hypothesis A) and discharges Hypothesis B of that note by kernel-checked
arithmetic.

Everything here is arithmetic over `ℝ`: the rational data, the three radicals
`√Q`, `√(r_λ² - d²)`, `√(1 + 4d²)`, and narrow two-sided *rational* enclosures
for each of them, for `d`, for `R₁` and for `ρ = R₁ - 1`.  No decimal
evaluation, no `native_decide` and no interval-arithmetic oracle is used: every
comparison between a radical and a rational is reduced to a squared rational
comparison by `Real.lt_sqrt` / `Real.sqrt_lt'`.

This module is a *sibling* of `StarKakeyaLower.StrongerKernel`; it neither
imports it nor reuses any of its constants.  It states no geometric theorem.

The interval certificate `spikes/001-joint-inner-outer/certify.py` computes the
same quantities with outward-rounded Arb intervals.  That certificate is
**outward evidence only**; the statements below are proofs, and they do not
depend on it.
-/

namespace StarKakeyaLower

noncomputable section

/-! ## `PROOF.md` Hypothesis A — the fixed rational data -/

/-- The target coefficient `T`: the theorem to be reached is `π T`. -/
def annTarget : ℝ := 131 / 6250

/-- The height cap `h₀`. -/
def annA : ℝ := 13177 / 100000

/-- The interpolation radius `r_λ`. -/
def annRLambda : ℝ := 10227 / 50000

/-- The Carathéodory splitting radius `r₀`. -/
def annR₀ : ℝ := 999 / 2000

/-- The greedy multiplier loss `ε_δ`. -/
def annEps : ℝ := 1 / 10 ^ 10

/-- The greedy multiplier `m = 1 - ε_δ`. -/
def annM : ℝ := 1 - annEps

/-- The interpolation weight `λ = (r₀ - r_λ) / (r₀ - h₀)`. -/
def annLambda : ℝ := 29496 / 36773

/-! ## `PROOF.md` Hypothesis A — the derived radicals -/

/-- The radicand `Q = 4 r_λ² (1 + h₀²) - h₀²`. -/
def annRadicand : ℝ := 4 * annRLambda ^ 2 * (1 + annA ^ 2) - annA ^ 2

/-- The chord offset `d = h₀ (1 - √Q) / (2 (1 + h₀²))`. -/
def annD : ℝ := annA * (1 - Real.sqrt annRadicand) / (2 * (1 + annA ^ 2))

/-- The radicand `r_λ² - d²` of the `R₁` denominator. -/
def annR₁Radicand : ℝ := annRLambda ^ 2 - annD ^ 2

/-- The denominator `1 - 2 √(r_λ² - d²)` of `R₁`. -/
def annR₁Denominator : ℝ := 1 - 2 * Real.sqrt annR₁Radicand

/-- The confinement radius `R₁ = √(1 + 4 d²) / (1 - 2 √(r_λ² - d²))`. -/
def annR₁ : ℝ := Real.sqrt (1 + 4 * annD ^ 2) / annR₁Denominator

/-- The inner escape radius `ρ = R₁ - 1`. -/
def annRho : ℝ := annR₁ - 1

/-! ## Rational enclosure constants

Each pair below is a two-sided rational enclosure of the corresponding real
quantity.  They are *definitions*; the enclosure statements are the theorems of
the next section. -/

/-- Rational lower bound for `√Q`. -/
def annSqrtRadicandLower : ℝ := 39100998140 / 100000000000

/-- Rational upper bound for `√Q`. -/
def annSqrtRadicandUpper : ℝ := 39100998141 / 100000000000

/-- Rational lower bound for `d`. -/
def annDLower : ℝ := 3943852316 / 100000000000

/-- Rational upper bound for `d`. -/
def annDUpper : ℝ := 3943852317 / 100000000000

/-- Rational lower bound for `√(r_λ² - d²)`. -/
def annSqrtR₁RadicandLower : ℝ := 20070180490 / 100000000000

/-- Rational upper bound for `√(r_λ² - d²)`. -/
def annSqrtR₁RadicandUpper : ℝ := 20070180491 / 100000000000

/-- Rational lower bound for `√(1 + 4 d²)`. -/
def annSqrtNumeratorLower : ℝ := 100310597069 / 100000000000

/-- Rational upper bound for `√(1 + 4 d²)`. -/
def annSqrtNumeratorUpper : ℝ := 100310597070 / 100000000000

/-- Rational lower bound for `R₁`. -/
def annR₁Lower : ℝ := 1675763481 / 1000000000

/-- Rational upper bound for `R₁`. -/
def annR₁Upper : ℝ := 1675763482 / 1000000000

/-- Rational lower bound for `ρ`. -/
def annRhoLower : ℝ := 675763481 / 1000000000

/-- Rational upper bound for `ρ`. -/
def annRhoUpper : ℝ := 675763482 / 1000000000

/-! ## Exact rational identities -/

/-- `Q` is an exact rational; the enclosures below compare against this value. -/
theorem ann_radicand_eq :
    annRadicand = 955555034740470041 / 6250000000000000000 := by
  norm_num [annRadicand, annRLambda, annA]

/-- `PROOF.md` Hypothesis B: the interpolation identity
`λ h₀ + (1 - λ) r₀ = r_λ`, exactly. -/
theorem ann_lambda_affine_identity :
    annLambda * annA + (1 - annLambda) * annR₀ = annRLambda := by
  norm_num [annLambda, annA, annR₀, annRLambda]

/-- `m = 1 - ε_δ`, the shape in which the exterior greedy interface reads the
multiplier. -/
theorem annM_eq_one_sub_annEps : annM = 1 - annEps := rfl

/-- `ρ = R₁ - 1`, the shape in which the exterior greedy interface reads the
escape radius. -/
theorem annRho_eq_annR₁_sub_one : annRho = annR₁ - 1 := rfl

/-! ## Basic rational domain facts -/

theorem annTarget_pos : 0 < annTarget := by norm_num [annTarget]

theorem annEps_pos : 0 < annEps := by norm_num [annEps]

theorem annEps_lt_one : annEps < 1 := by norm_num [annEps]

theorem annM_pos : 0 < annM := by norm_num [annM, annEps]

theorem annM_lt_one : annM < 1 := by norm_num [annM, annEps]

theorem annA_pos : 0 < annA := by norm_num [annA]

theorem annA_lt_annRLambda : annA < annRLambda := by norm_num [annA, annRLambda]

theorem annRLambda_lt_annR₀ : annRLambda < annR₀ := by
  norm_num [annRLambda, annR₀]

theorem annR₀_pos : 0 < annR₀ := by norm_num [annR₀]

theorem annR₀_lt_half : annR₀ < 1 / 2 := by norm_num [annR₀]

theorem annR₀_ge_three_twentieths : (3 / 20 : ℝ) ≤ annR₀ := by norm_num [annR₀]

theorem annLambda_pos : 0 < annLambda := by norm_num [annLambda]

theorem annLambda_lt_one : annLambda < 1 := by norm_num [annLambda]

/-! ## The radical enclosures

Each radical is enclosed by comparing squares of rationals, so every step is
decided by `norm_num` on rational arithmetic; nothing is evaluated numerically
in floating point. -/

theorem ann_radicand_nonneg : 0 ≤ annRadicand := by
  rw [ann_radicand_eq]; norm_num

theorem ann_radicand_lt_one : annRadicand < 1 := by
  rw [ann_radicand_eq]; norm_num

theorem ann_sqrt_radicand_lower :
    annSqrtRadicandLower < Real.sqrt annRadicand := by
  refine (Real.lt_sqrt (by norm_num [annSqrtRadicandLower])).2 ?_
  rw [ann_radicand_eq]
  norm_num [annSqrtRadicandLower]

theorem ann_sqrt_radicand_upper :
    Real.sqrt annRadicand < annSqrtRadicandUpper := by
  refine (Real.sqrt_lt' (by norm_num [annSqrtRadicandUpper])).2 ?_
  rw [ann_radicand_eq]
  norm_num [annSqrtRadicandUpper]

/-- Narrow rational enclosure of the chord offset `d`. -/
theorem ann_d_lower : annDLower < annD := by
  have hs := ann_sqrt_radicand_upper
  have hden : (0 : ℝ) < 2 * (1 + annA ^ 2) := by positivity
  rw [annD, lt_div_iff₀ hden]
  simp only [annA, annDLower, annSqrtRadicandUpper] at hs ⊢
  nlinarith [hs]

/-- Narrow rational enclosure of the chord offset `d`. -/
theorem ann_d_upper : annD < annDUpper := by
  have hs := ann_sqrt_radicand_lower
  have hden : (0 : ℝ) < 2 * (1 + annA ^ 2) := by positivity
  rw [annD, div_lt_iff₀ hden]
  simp only [annA, annDUpper, annSqrtRadicandLower] at hs ⊢
  nlinarith [hs]

theorem annD_pos : 0 < annD := lt_trans (by norm_num [annDLower]) ann_d_lower

theorem annD_lt_half_annA : annD < annA / 2 :=
  lt_trans ann_d_upper (by norm_num [annDUpper, annA])

theorem ann_d_sq_lower : annDLower ^ 2 < annD ^ 2 := by
  have h := ann_d_lower
  have h0 : (0 : ℝ) < annDLower := by norm_num [annDLower]
  nlinarith

theorem ann_d_sq_upper : annD ^ 2 < annDUpper ^ 2 := by
  have h := ann_d_upper
  have h0 : (0 : ℝ) < annD := annD_pos
  nlinarith

theorem ann_r₁_radicand_pos : 0 < annR₁Radicand := by
  have h := ann_d_sq_upper
  rw [annR₁Radicand]
  simp only [annRLambda, annDUpper] at h ⊢
  nlinarith [h]

theorem ann_sqrt_r₁_radicand_lower :
    annSqrtR₁RadicandLower < Real.sqrt annR₁Radicand := by
  refine (Real.lt_sqrt (by norm_num [annSqrtR₁RadicandLower])).2 ?_
  have h := ann_d_sq_upper
  rw [annR₁Radicand]
  simp only [annRLambda, annDUpper, annSqrtR₁RadicandLower] at h ⊢
  nlinarith [h]

theorem ann_sqrt_r₁_radicand_upper :
    Real.sqrt annR₁Radicand < annSqrtR₁RadicandUpper := by
  refine (Real.sqrt_lt' (by norm_num [annSqrtR₁RadicandUpper])).2 ?_
  have h := ann_d_sq_lower
  rw [annR₁Radicand]
  simp only [annRLambda, annDLower, annSqrtR₁RadicandUpper] at h ⊢
  nlinarith [h]

theorem ann_r₁_denominator_pos : 0 < annR₁Denominator := by
  have h := ann_sqrt_r₁_radicand_upper
  rw [annR₁Denominator]
  simp only [annSqrtR₁RadicandUpper] at h
  linarith

theorem ann_r₁_denominator_lower :
    1 - 2 * annSqrtR₁RadicandUpper < annR₁Denominator := by
  have h := ann_sqrt_r₁_radicand_upper
  rw [annR₁Denominator]
  linarith

theorem ann_r₁_denominator_upper :
    annR₁Denominator < 1 - 2 * annSqrtR₁RadicandLower := by
  have h := ann_sqrt_r₁_radicand_lower
  rw [annR₁Denominator]
  linarith

theorem ann_sqrt_numerator_lower :
    annSqrtNumeratorLower < Real.sqrt (1 + 4 * annD ^ 2) := by
  refine (Real.lt_sqrt (by norm_num [annSqrtNumeratorLower])).2 ?_
  have h := ann_d_sq_lower
  simp only [annDLower, annSqrtNumeratorLower] at h ⊢
  nlinarith [h]

theorem ann_sqrt_numerator_upper :
    Real.sqrt (1 + 4 * annD ^ 2) < annSqrtNumeratorUpper := by
  refine (Real.sqrt_lt' (by norm_num [annSqrtNumeratorUpper])).2 ?_
  have h := ann_d_sq_upper
  simp only [annDUpper, annSqrtNumeratorUpper] at h ⊢
  nlinarith [h]

/-- Narrow rational enclosure of the confinement radius `R₁`. -/
theorem ann_r₁_lower : annR₁Lower < annR₁ := by
  have hden := ann_r₁_denominator_pos
  have hdenup := ann_r₁_denominator_upper
  have hnum := ann_sqrt_numerator_lower
  rw [annR₁, lt_div_iff₀ hden]
  have hbound : annR₁Lower * annR₁Denominator <
      annR₁Lower * (1 - 2 * annSqrtR₁RadicandLower) := by
    have h0 : (0 : ℝ) < annR₁Lower := by norm_num [annR₁Lower]
    exact mul_lt_mul_of_pos_left hdenup h0
  have hfinal : annR₁Lower * (1 - 2 * annSqrtR₁RadicandLower) ≤
      annSqrtNumeratorLower := by
    norm_num [annR₁Lower, annSqrtR₁RadicandLower, annSqrtNumeratorLower]
  linarith

/-- Narrow rational enclosure of the confinement radius `R₁`. -/
theorem ann_r₁_upper : annR₁ < annR₁Upper := by
  have hden := ann_r₁_denominator_pos
  have hdenlow := ann_r₁_denominator_lower
  have hnum := ann_sqrt_numerator_upper
  rw [annR₁, div_lt_iff₀ hden]
  have hbound : annR₁Upper * (1 - 2 * annSqrtR₁RadicandUpper) <
      annR₁Upper * annR₁Denominator := by
    have h0 : (0 : ℝ) < annR₁Upper := by norm_num [annR₁Upper]
    exact mul_lt_mul_of_pos_left hdenlow h0
  have hfinal : annSqrtNumeratorUpper ≤
      annR₁Upper * (1 - 2 * annSqrtR₁RadicandUpper) := by
    norm_num [annR₁Upper, annSqrtR₁RadicandUpper, annSqrtNumeratorUpper]
  linarith

theorem ann_one_lt_r₁ : 1 < annR₁ :=
  lt_trans (by norm_num [annR₁Lower]) ann_r₁_lower

theorem annR₁_pos : 0 < annR₁ := lt_trans (by norm_num) ann_one_lt_r₁

/-- Narrow rational enclosure of the escape radius `ρ`. -/
theorem ann_rho_lower : annRhoLower < annRho := by
  have h := ann_r₁_lower
  rw [annRho]
  simp only [annR₁Lower] at h
  simp only [annRhoLower]
  linarith

/-- Narrow rational enclosure of the escape radius `ρ`. -/
theorem ann_rho_upper : annRho < annRhoUpper := by
  have h := ann_r₁_upper
  rw [annRho]
  simp only [annR₁Upper] at h
  simp only [annRhoUpper]
  linarith

theorem annRho_pos : 0 < annRho := lt_trans (by norm_num [annRhoLower]) ann_rho_lower

theorem annR₀_lt_annRho : annR₀ < annRho :=
  lt_trans (by norm_num [annR₀, annRhoLower]) ann_rho_lower

theorem annA_lt_annRho : annA < annRho :=
  lt_trans (by norm_num [annA, annRhoLower]) ann_rho_lower

/-- The scaled escape hypothesis `h₀ < m ρ` of `PROOF.md` Hypothesis B. -/
theorem annA_lt_annM_mul_annRho : annA < annM * annRho := by
  have h := ann_rho_lower
  have hm : annM = 1 - annEps := rfl
  have : annM * annRhoLower ≤ annM * annRho := by
    exact mul_le_mul_of_nonneg_left h.le annM_pos.le
  refine lt_of_lt_of_le ?_ this
  rw [hm]
  norm_num [annA, annEps, annRhoLower]

theorem annM_mul_annRho_pos : 0 < annM * annRho := mul_pos annM_pos annRho_pos

theorem ann_arg_rho_pos : 0 < annA / annRho := div_pos annA_pos annRho_pos

theorem ann_arg_rho_lt_one : annA / annRho < 1 :=
  (div_lt_one annRho_pos).2 annA_lt_annRho

theorem ann_arg_m_rho_pos : 0 < annA / (annM * annRho) :=
  div_pos annA_pos annM_mul_annRho_pos

theorem ann_arg_m_rho_lt_one : annA / (annM * annRho) < 1 :=
  (div_lt_one annM_mul_annRho_pos).2 annA_lt_annM_mul_annRho

/-! ## `PROOF.md` Hypothesis B as a structure -/

/-- **`PROOF.md` Hypothesis B (domain conditions) for the production tuple**,
together with the derived positivity facts (`ε_δ`, `m`, `r₀`, `R₁`, `ρ`, `T`)
that the Python gate list of `certify.py` leaves implicit.

The order relations `h₀ < r_λ < r₀` are *strict* here, which strengthens the
non-strict `h₀ ≤ r_λ ≤ r₀` of the note and matches the `domain_order_*` gates
of `certify.py`.  The structure contains no geometric or measure-theoretic
field: it is purely the numeric domain. -/
structure AnnularParameterDomain where
  target_pos : 0 < annTarget
  eps_pos : 0 < annEps
  eps_lt_one : annEps < 1
  m_pos : 0 < annM
  m_lt_one : annM < 1
  m_eq : annM = 1 - annEps
  a_pos : 0 < annA
  a_lt_rLambda : annA < annRLambda
  rLambda_lt_r₀ : annRLambda < annR₀
  r₀_pos : 0 < annR₀
  r₀_lt_half : annR₀ < 1 / 2
  r₀_ge_three_twentieths : (3 / 20 : ℝ) ≤ annR₀
  lambda_pos : 0 < annLambda
  lambda_lt_one : annLambda < 1
  affine_identity : annLambda * annA + (1 - annLambda) * annR₀ = annRLambda
  radicand_nonneg : 0 ≤ annRadicand
  radicand_lt_one : annRadicand < 1
  d_pos : 0 < annD
  d_lt_half_a : annD < annA / 2
  r₁_radicand_pos : 0 < annR₁Radicand
  r₁_denominator_pos : 0 < annR₁Denominator
  r₁_pos : 0 < annR₁
  one_lt_r₁ : 1 < annR₁
  rho_eq : annRho = annR₁ - 1
  rho_pos : 0 < annRho
  rho_gt_r₀ : annR₀ < annRho
  a_lt_m_rho : annA < annM * annRho
  arg_rho_pos : 0 < annA / annRho
  arg_rho_lt_one : annA / annRho < 1
  arg_m_rho_pos : 0 < annA / (annM * annRho)
  arg_m_rho_lt_one : annA / (annM * annRho) < 1
  d_rational_enclosure : annDLower < annD ∧ annD < annDUpper
  r₁_rational_enclosure : annR₁Lower < annR₁ ∧ annR₁ < annR₁Upper
  rho_rational_enclosure : annRhoLower < annRho ∧ annRho < annRhoUpper

/-- **The production Hypothesis B certificate.**  Every field is proved above by
exact rational arithmetic and squared-rational radical comparisons. -/
def annularParameterDomain : AnnularParameterDomain where
  target_pos := annTarget_pos
  eps_pos := annEps_pos
  eps_lt_one := annEps_lt_one
  m_pos := annM_pos
  m_lt_one := annM_lt_one
  m_eq := annM_eq_one_sub_annEps
  a_pos := annA_pos
  a_lt_rLambda := annA_lt_annRLambda
  rLambda_lt_r₀ := annRLambda_lt_annR₀
  r₀_pos := annR₀_pos
  r₀_lt_half := annR₀_lt_half
  r₀_ge_three_twentieths := annR₀_ge_three_twentieths
  lambda_pos := annLambda_pos
  lambda_lt_one := annLambda_lt_one
  affine_identity := ann_lambda_affine_identity
  radicand_nonneg := ann_radicand_nonneg
  radicand_lt_one := ann_radicand_lt_one
  d_pos := annD_pos
  d_lt_half_a := annD_lt_half_annA
  r₁_radicand_pos := ann_r₁_radicand_pos
  r₁_denominator_pos := ann_r₁_denominator_pos
  r₁_pos := annR₁_pos
  one_lt_r₁ := ann_one_lt_r₁
  rho_eq := annRho_eq_annR₁_sub_one
  rho_pos := annRho_pos
  rho_gt_r₀ := annR₀_lt_annRho
  a_lt_m_rho := annA_lt_annM_mul_annRho
  arg_rho_pos := ann_arg_rho_pos
  arg_rho_lt_one := ann_arg_rho_lt_one
  arg_m_rho_pos := ann_arg_m_rho_pos
  arg_m_rho_lt_one := ann_arg_m_rho_lt_one
  d_rational_enclosure := ⟨ann_d_lower, ann_d_upper⟩
  r₁_rational_enclosure := ⟨ann_r₁_lower, ann_r₁_upper⟩
  rho_rational_enclosure := ⟨ann_rho_lower, ann_rho_upper⟩

end

end StarKakeyaLower
