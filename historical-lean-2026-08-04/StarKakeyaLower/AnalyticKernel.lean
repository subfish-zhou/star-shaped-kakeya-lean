import StarKakeyaLower.NonIterativeKernel

/-!
# Analytic kernel for the non-iterative Case I bound

This file replaces the external nine-term logarithm estimate by a theorem
proved from Mathlib's positive series for `Real.log (1 + x)`.  A three-term
partial sum plus a geometric tail already leaves a positive exact margin.

The remaining Case I interfaces are the branch-dominance theorem for `g` and
the calculus identity equating the radial integral with `altILowerExact`.
-/

open scoped BigOperators

namespace StarKakeyaLower

noncomputable section

def altLogZ : ℝ := 283 / 1917

def altLogGeomUpper : ℝ :=
  2 * altLogZ
    + 2 * altLogZ ^ 3 / 3
    + 2 * altLogZ ^ 5 / 5
    + 2 * altLogZ ^ 7 / (1 - altLogZ ^ 2)

def altIRightGeom : ℝ :=
  ((-altR₀ ^ 2 / 2 + altR₀)
      - (-altSwitchRight ^ 2 / 2 + altSwitchRight))
    - altLogGeomUpper / 2

def altILowerGeom : ℝ := altILeft + altIMiddle + altIRightGeom

def altIRightExact : ℝ :=
  ((-altR₀ ^ 2 / 2 + altR₀)
      - (-altSwitchRight ^ 2 / 2 + altSwitchRight))
    - Real.log (1 + altLogX) / 2

def altILowerExact : ℝ := altILeft + altIMiddle + altIRightExact

theorem alt_log_geom_upper :
    Real.log (1 + altLogX) ≤ altLogGeomUpper := by
  rw [alt_logX_exact]
  have hx : 0 ≤ (283 / 817 : ℝ) := by norm_num
  have hz :
      (283 / 817 : ℝ) / (283 / 817 + 2) = altLogZ := by
    norm_num [altLogZ]
  have hsum := Real.hasSum_log_one_add hx
  rw [hz] at hsum
  let term : ℕ → ℝ :=
    fun k =>
      2 * (1 / (2 * (k : ℝ) + 1)) * altLogZ ^ (2 * k + 1)
  change HasSum term (Real.log (1 + (283 / 817 : ℝ))) at hsum
  have hsplit := hsum.summable.sum_add_tsum_nat_add 3
  rw [hsum.tsum_eq] at hsplit
  have hz0 : 0 ≤ altLogZ := by norm_num [altLogZ]
  have hz1 : altLogZ < 1 := by norm_num [altLogZ]
  have htailPointwise :
      ∀ n : ℕ,
        term (n + 3) ≤
          2 * altLogZ ^ 7 * (altLogZ ^ 2) ^ n := by
    intro n
    have hden :
        (1 : ℝ) / (2 * ((n + 3 : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num [Nat.cast_add]
      positivity
    calc
      term (n + 3)
          ≤ 2 * altLogZ ^ (2 * (n + 3) + 1) := by
            dsimp [term]
            apply mul_le_mul_of_nonneg_right
            · nlinarith
            · positivity
      _ = 2 * altLogZ ^ 7 * (altLogZ ^ 2) ^ n := by
            rw [show 2 * (n + 3) + 1 = 7 + 2 * n by omega]
            simp only [pow_add, pow_mul]
            ring
  have htermTail : Summable (fun n : ℕ => term (n + 3)) := by
    simpa only [Function.comp_apply] using
      hsum.summable.comp_injective (i := fun n : ℕ => n + 3) (by
        intro m n h
        exact Nat.add_right_cancel h)
  have hzsq : ‖altLogZ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg altLogZ)]
    nlinarith [sq_nonneg (altLogZ - 1)]
  have hgeom :
      Summable (fun n : ℕ =>
        2 * altLogZ ^ 7 * (altLogZ ^ 2) ^ n) :=
    (summable_geometric_of_norm_lt_one hzsq).mul_left _
  have htail :
      ∑' n : ℕ, term (n + 3) ≤
        2 * altLogZ ^ 7 / (1 - altLogZ ^ 2) := by
    calc
      ∑' n : ℕ, term (n + 3)
          ≤ ∑' n : ℕ,
              2 * altLogZ ^ 7 * (altLogZ ^ 2) ^ n :=
            htermTail.tsum_le_tsum htailPointwise hgeom
      _ = 2 * altLogZ ^ 7 / (1 - altLogZ ^ 2) := by
            rw [
              tsum_mul_left,
              tsum_geometric_of_lt_one (sq_nonneg altLogZ)
            ]
            · rw [div_eq_mul_inv]
            · nlinarith [sq_nonneg (altLogZ - 1)]
  rw [← hsplit]
  change
    (∑ i ∈ Finset.range 3, term i)
        + ∑' i : ℕ, term (i + 3) ≤ altLogGeomUpper
  calc
    (∑ i ∈ Finset.range 3, term i)
          + ∑' i : ℕ, term (i + 3)
        ≤ (∑ i ∈ Finset.range 3, term i)
          + 2 * altLogZ ^ 7 / (1 - altLogZ ^ 2) :=
          add_le_add_right htail _
    _ = altLogGeomUpper := by
          norm_num [
            term,
            altLogGeomUpper,
            Finset.sum_range_succ
          ]
          ring

theorem alt_iLower_geom_le_exact :
    altILowerGeom ≤ altILowerExact := by
  have hlog := alt_log_geom_upper
  dsimp [
    altILowerGeom,
    altILowerExact,
    altIRightGeom,
    altIRightExact
  ]
  linarith

theorem alt_caseI_geom_margin_exact :
    altCaseI altILowerGeom - 1 / 56 =
      9903508366951835577422590421 /
        7802487979617077230176000000000000 := by
  norm_num [
    altCaseI,
    altILowerGeom,
    altILeft,
    altIMiddle,
    altIRightGeom,
    altLogGeomUpper,
    altLogZ,
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

theorem alt_caseI_geom_strict :
    1 / 56 < altCaseI altILowerGeom := by
  have hmargin := alt_caseI_geom_margin_exact
  have hpositive :
      (0 : ℝ) <
        9903508366951835577422590421 /
          7802487979617077230176000000000000 := by
    norm_num
  linarith

theorem alt_caseI_exactPrimitive_strict :
    1 / 56 < altCaseI altILowerExact := by
  have hmono :
      altCaseI altILowerGeom ≤ altCaseI altILowerExact := by
    have hk : 0 ≤ altP * altK := by
      norm_num [altP, altK, altR₀]
    dsimp [altCaseI]
    nlinarith [alt_iLower_geom_le_exact]
  exact alt_caseI_geom_strict.trans_le hmono

end

end StarKakeyaLower
