import StarKakeyaLower.AnnularKernel

/-!
# The two-active-segment radial integral certificate of the annular route (M6)

This module discharges the analytic half of the M6 obligations of the confined
branch, in exactly the shape the (closed) M5 interface
`universal_positive_confined_lower_bound_of_trace_containment` consumes:

* a concrete dilation loss `annPaperG` with `hg : 1 ≤ annPaperG r`,
* the measurability licence
  `AEMeasurable (fun r => ENNReal.ofReal (r / annPaperG r))
     (volume.restrict (Icc annA annR₀))`,
* the scalar radial lower bound in *lower Lebesgue* form,
  `ENNReal.ofReal annILower ≤ ∫⁻ r in Icc annA annR₀,
     ENNReal.ofReal (r / annPaperG r)`.

## Why the certificate is two-piece, and what is *not* claimed

For this parameter tuple the frozen entry
`annFrozenRatio = 35227/14773 = 2.38455…` is **hidden**: it is dominated on all
of `[annA, annR₀]` by the increasing large-angle entry, whose value already at
`r = annA` is `2.392472…`.  The maximum therefore switches exactly once, at
`r = 0.2352988169…`, from the large-angle branch to the interior branch.  The
three-piece cut of `CaseIStrongIntegral` is *not* ported: no lemma of this file
assumes the frozen branch is active anywhere.

Only *two* segments are retained,

* `[annA, annQL]` with `annQL = 23529/100000`, where `annPaperG` is the
  large-angle branch, and
* `[annQR, annR₀]` with `annQR = 2353/10000`, where `annPaperG` is the interior
  branch,

and the rational cuts `annQL < 0.2352988169… < annQR` *straddle* the switch.
The straddling gap `[annQL, annQR]` is deliberately **not** claimed to be
covered by either branch: it is retained as a third interval and then discarded
by nonnegativity of the integrand.  Consequently the certificate never asserts
that the two active intervals exhaust `[annA, annR₀]`.

That the switch happens once and is never re-crossed is proved, not assumed,
through the monotone comparison function

`annH x = π (6x-1) / (2 (1+2x)) - arctan (2x)`,

whose derivative `4π/(1+2x)^2 - 2/(1+4x^2)` is nonnegative for `0 ≤ x`.  Since
`annH r ≤ 0` is equivalent to "interior ≤ large" and `0 ≤ annH r` to
"large ≤ interior", monotonicity of `annH` plus its sign at the two rational
cuts pins the branch order on each retained segment and rules out a second
crossing.

## Rigour of the transcendental steps

Every transcendental quantity is enclosed by an *outward* rational bound:

* `arctan` from below by the even alternating partial sum `annAtanLower6`
  (six terms), which is a genuine lower bound by Leibniz;
* `arctan` from above through the quarter-turn identity
  `arctan x + arctan ((1-x)/(1+x)) = π/4` applied to the rational reflected
  argument, so the upper bound is again a six-term partial sum;
* `π` by the twenty-digit rational enclosure `annPiLower < π < annPiUpper`;
* `log (1 + annLogX)` from above by three explicit terms of the odd series plus
  the *strengthened* geometric tail `2 z^7 / (7 (1 - z^2))`.  The crude tail
  `2 z^7 / (1 - z^2)` used by the earlier `π/56` route is a factor seven too
  large and does **not** leave a positive margin at the `2097/100000` target
  here; the `1/(2k+7) ≤ 1/7` refinement is load bearing.

No decimal literal, no floating point and no kernel-bypassing evaluation
tactic occurs anywhere: every closing step is an exact rational `norm_num`
computation on `ℚ`-valued literals.

The import closure is `StarKakeyaLower.AnnularKernel` — the independently
reviewed numeric kernel, which fixes the production parameter tuple and
discharges `PROOF.md` Hypothesis B — plus Mathlib.  Only the rational
parameters `annA`, `annR₀`, `annRLambda` and `annTarget` are read from it; no
radical, no enclosure constant and no domain field of the kernel is used here,
and this module introduces no parameter of its own beyond the two rational
branch cuts `annQL`, `annQR` and the stored segment bounds.  Neither
`StrongerKernel` nor `AnalyticBranches` nor `AnalyticKernel` is imported: the
handful of generic `arctan` facts that are needed are reproved here from
Mathlib directly, so no frozen witness constant enters the closure.
-/

open Set MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-! ## Generic `arctan` machinery

These two facts (Leibniz lower bounds for the arctangent series, and the
quarter-turn reflection) are completely generic.  They exist in
`StarKakeyaLower.AnalyticBranches`, but that module sits over the frozen
`π/56` kernel, so importing it would taint the closure of the annular route.
They are reproved here from Mathlib. -/

/-- The nonnegative coefficient of the alternating arctangent series. -/
def annAtanCoeff (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * n + 1)

theorem annAtanCoeff_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (annAtanCoeff x) := by
  apply antitone_nat_of_succ_le
  intro n
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hnum : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  dsimp [annAtanCoeff]
  apply div_le_div₀ hnum hpow (by positivity)
  norm_num [Nat.cast_add]

/-- Leibniz: an even partial sum of the alternating arctangent series is a
lower bound for `arctan`. -/
theorem ann_atan_even_partial_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * annAtanCoeff x i) ≤
      Real.arctan x := by
  have hseries := Real.hasSum_arctan (x := x) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have htend :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * annAtanCoeff x i)
        Filter.atTop (nhds (Real.arctan x)) := by
    simpa [annAtanCoeff, mul_div_assoc] using hseries.tendsto_sum_nat
  exact (annAtanCoeff_antitone hx0 hx1.le).alternating_series_le_tendsto htend k

/-- The quarter-turn reflection `arctan x + arctan ((1-x)/(1+x)) = π/4`. -/
theorem ann_arctan_quarter_turn {x : ℝ} (hx0 : 0 ≤ x) :
    Real.arctan x + Real.arctan ((1 - x) / (1 + x)) = Real.pi / 4 := by
  have hden : 1 + x ≠ 0 := by linarith
  have hmul : x * ((1 - x) / (1 + x)) < 1 := by
    rw [← mul_div_assoc, div_lt_one (by linarith)]
    nlinarith
  have hsquares : 1 + x ^ 2 ≠ 0 := by positivity
  have hfrac : (x + (1 - x) / (1 + x)) / (1 - x * ((1 - x) / (1 + x))) = 1 := by
    field_simp [hden, hsquares]
    rw [show x * (1 + x) + (1 - x) = 1 + x ^ 2 by ring]
    rw [show 1 + x - x * (1 - x) = 1 + x ^ 2 by ring]
    exact div_self hsquares
  rw [Real.arctan_add hmul, hfrac, Real.arctan_one]

/-- The explicit six-term even partial sum used by every `arctan` enclosure
below.  It is a lower bound for `arctan` on `[0, 1)`. -/
def annAtanLower6 (x : ℝ) : ℝ :=
  x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 + x ^ 9 / 9 - x ^ 11 / 11

theorem ann_atanLower6_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    annAtanLower6 x ≤ Real.arctan x := by
  have h := ann_atan_even_partial_lower hx0 hx1 3
  norm_num [annAtanCoeff, Finset.sum_range_succ] at h
  dsimp [annAtanLower6]
  linarith

/-- The matching upper bound: reflect and use the six-term lower bound on the
reflected (rational) argument. -/
theorem ann_arctan_le_of_reflect {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.arctan x ≤ Real.pi / 4 - annAtanLower6 ((1 - x) / (1 + x)) := by
  have hy0 : 0 ≤ (1 - x) / (1 + x) := by
    apply div_nonneg <;> linarith
  have hy1 : (1 - x) / (1 + x) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hlow := ann_atanLower6_le hy0 hy1
  have hturn := ann_arctan_quarter_turn hx0.le
  linarith

/-! ## The three branches, the paper maximum, and the rational cuts -/

/-- The interior dilation ratio `(1+2r)/(1-2r)`. -/
def annInteriorRatio (r : ℝ) : ℝ := (1 + 2 * r) / (1 - 2 * r)

/-- The frozen dilation ratio at `r = annRLambda`. -/
def annFrozenRatio : ℝ := (1 + 2 * annRLambda) / (1 - 2 * annRLambda)

/-- The large-angle dilation ratio `π / (π/2 - arctan (2r))`. -/
def annLargeAngleRatio (r : ℝ) : ℝ := Real.pi / (Real.pi / 2 - Real.arctan (2 * r))

/-- The paper's dilation loss `g` of equation (2.1): the pointwise maximum of
the three branches. -/
def annPaperG (r : ℝ) : ℝ :=
  max (annInteriorRatio r) (max annFrozenRatio (annLargeAngleRatio r))

/-- The stored scalar radial lower bound `I_lower = 0.02097`. -/
def annILower : ℝ := 2097 / 100000

/-- The left rational cut, strictly *below* the branch switch `0.2352988169…`. -/
def annQL : ℝ := 23529 / 100000

/-- The right rational cut, strictly *above* the branch switch. -/
def annQR : ℝ := 2353 / 10000

/-- Twenty-digit rational enclosure of `π` from below. -/
def annPiLower : ℝ := 314159265358979323846 / 10 ^ 20

/-- Twenty-digit rational enclosure of `π` from above. -/
def annPiUpper : ℝ := 314159265358979323847 / 10 ^ 20

theorem ann_pi_lower_lt : annPiLower < Real.pi := by
  have h := Real.pi_gt_d20
  norm_num [annPiLower] at h ⊢
  linarith

theorem ann_pi_lt_upper : Real.pi < annPiUpper := by
  have h := Real.pi_lt_d20
  norm_num [annPiUpper] at h ⊢
  linarith

theorem ann_pi_pos : 0 < Real.pi := Real.pi_pos

theorem annFrozenRatio_eq : annFrozenRatio = 35227 / 14773 := by
  norm_num [annFrozenRatio, annRLambda]

theorem annFrozenRatio_pos : 0 < annFrozenRatio := by
  rw [annFrozenRatio_eq]; norm_num

/-- The large-angle denominator is positive: `arctan < π/2` always. -/
theorem ann_largeAngle_den_pos (r : ℝ) : 0 < Real.pi / 2 - Real.arctan (2 * r) := by
  linarith [Real.arctan_lt_pi_div_two (2 * r)]

theorem annLargeAngleRatio_pos (r : ℝ) : 0 < annLargeAngleRatio r :=
  div_pos ann_pi_pos (ann_largeAngle_den_pos r)

/-- `g ≥ 1` everywhere, because the frozen entry alone already exceeds `1`.
This is the `hg` input of the M5 confined interface. -/
theorem one_le_annPaperG (r : ℝ) : 1 ≤ annPaperG r := by
  refine le_trans ?_ (le_max_of_le_right (le_max_left _ _))
  rw [annFrozenRatio_eq]; norm_num

theorem annPaperG_pos (r : ℝ) : 0 < annPaperG r :=
  lt_of_lt_of_le zero_lt_one (one_le_annPaperG r)

/-- `hg` in the exact shape of the M5 interface. -/
theorem one_le_annPaperG_on_Icc :
    ∀ r ∈ Icc annA annR₀, 1 ≤ annPaperG r := fun r _ => one_le_annPaperG r

/-! ## Continuity and the measurability licence -/

theorem ann_continuousAt_interiorRatio {r : ℝ} (hn : 1 - 2 * r ≠ 0) :
    ContinuousAt annInteriorRatio r := by
  change ContinuousAt (fun x : ℝ => (1 + 2 * x) / (1 - 2 * x)) r
  exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hn

theorem ann_den_ne_zero {r : ℝ} (hr : r ∈ Icc annA annR₀) : 1 - 2 * r ≠ 0 := by
  have := hr.2
  norm_num [annR₀] at this ⊢
  linarith

theorem ann_continuousOn_interiorRatio :
    ContinuousOn annInteriorRatio (Icc annA annR₀) := fun _ hr =>
  (ann_continuousAt_interiorRatio (ann_den_ne_zero hr)).continuousWithinAt

theorem ann_continuous_largeAngleRatio : Continuous annLargeAngleRatio := by
  apply continuous_const.div
  · exact continuous_const.sub
      (Real.continuous_arctan.comp (continuous_const.mul continuous_id))
  · intro r; exact (ann_largeAngle_den_pos r).ne'

theorem ann_continuousOn_paperG : ContinuousOn annPaperG (Icc annA annR₀) := by
  intro r hr
  apply ContinuousAt.continuousWithinAt
  exact (ann_continuousAt_interiorRatio (ann_den_ne_zero hr)).max
    (continuousAt_const.max ann_continuous_largeAngleRatio.continuousAt)

theorem ann_continuousOn_radial :
    ContinuousOn (fun r => r / annPaperG r) (Icc annA annR₀) := by
  exact continuousOn_id.div ann_continuousOn_paperG fun r _ => (annPaperG_pos r).ne'

/-- **The `hmeas` input of the M5 confined interface**, verbatim. -/
theorem ann_aemeasurable_ofReal_radial :
    AEMeasurable (fun r => ENNReal.ofReal (r / annPaperG r))
      (volume.restrict (Icc annA annR₀)) := by
  have h : AEMeasurable (fun r => r / annPaperG r)
      (volume.restrict (Icc annA annR₀)) :=
    (ann_continuousOn_radial.aemeasurable measurableSet_Icc)
  exact ENNReal.measurable_ofReal.comp_aemeasurable h

/-! ## The monotone branch comparison `annH`

`annH r ≤ 0` is *equivalent* to `annInteriorRatio r ≤ annLargeAngleRatio r`,
and `0 ≤ annH r` to the reverse comparison.  `annH` is monotone on `[0, ∞)`,
which is what forbids a second crossing. -/

def annH (x : ℝ) : ℝ :=
  Real.pi * (6 * x - 1) / (2 * (1 + 2 * x)) - Real.arctan (2 * x)

theorem ann_hasDerivAt_H {x : ℝ} (hx : 1 + 2 * x ≠ 0) :
    HasDerivAt annH (4 * Real.pi / (1 + 2 * x) ^ 2 - 2 / (1 + 4 * x ^ 2)) x := by
  have hn := HasDerivAt.const_mul Real.pi
    (((hasDerivAt_id x).const_mul 6).sub_const 1)
  have hd := (((hasDerivAt_id x).const_mul 2).add_const 1).const_mul 2
  have ha := (Real.hasDerivAt_arctan (2 * x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hdn : 2 * (2 * x + 1) ≠ 0 := by intro h; apply hx; nlinarith
  have hraw := (hn.div hd hdn).sub ha
  simp only [id_eq, mul_one] at hraw
  have heq :
      ((Real.pi * 6 * (2 * (2 * x + 1)) - Real.pi * (6 * x - 1) * (2 * 2)) /
          (2 * (2 * x + 1)) ^ 2 - 1 / (1 + (2 * x) ^ 2) * 2) =
        4 * Real.pi / (1 + 2 * x) ^ 2 - 2 / (1 + 4 * x ^ 2) := by
    have hq : 1 + 4 * x ^ 2 ≠ 0 := by positivity
    field_simp [hx, hq, hdn]
    have hlin : 2 * x + 1 ≠ 0 := by intro h; apply hx; nlinarith
    field_simp [hlin]
    ring
  rw [← heq]
  convert hraw using 1
  funext y
  dsimp only [annH, Function.comp_apply]
  congr 2
  ring

theorem ann_H_monotoneOn : MonotoneOn annH (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx
    have hx0 : 0 < 1 + 2 * x := by simp only [mem_Ici] at hx; linarith
    exact (ann_hasDerivAt_H hx0.ne').continuousAt.continuousWithinAt
  · intro x hx
    have hxmem : (0 : ℝ) < x := by simpa using hx
    exact ((ann_hasDerivAt_H
      (by linarith : (1 : ℝ) + 2 * x ≠ 0)).differentiableAt).differentiableWithinAt
  · intro x hx
    have hxmem : (0 : ℝ) < x := by simpa using hx
    have hx0 : 0 < 1 + 2 * x := by linarith
    rw [(ann_hasDerivAt_H hx0.ne').deriv]
    have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsq1 : 0 < (1 + 2 * x) ^ 2 := by positivity
    have hsq2 : 0 < 1 + 4 * x ^ 2 := by positivity
    rw [sub_nonneg, div_le_div_iff₀ hsq2 hsq1]
    nlinarith [sq_nonneg (2 * x - 1)]

/-- `annH r ≤ 0` forces the interior branch below the large-angle branch. -/
theorem ann_interior_le_large_of_H {r : ℝ} (hr0 : 0 ≤ r) (hrh : r < 1 / 2)
    (hH : annH r ≤ 0) : annInteriorRatio r ≤ annLargeAngleRatio r := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * r) := ann_largeAngle_den_pos r
  have hm : 0 < 1 - 2 * r := by linarith
  have hp : 0 < 1 + 2 * r := by linarith
  have hatan : Real.pi * (6 * r - 1) / (2 * (1 + 2 * r)) ≤ Real.arctan (2 * r) := by
    dsimp [annH] at hH; linarith
  have hkey : Real.pi * (6 * r - 1) / 2 ≤ (1 + 2 * r) * Real.arctan (2 * r) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (1 + 2 * r))] at hatan
    nlinarith
  rw [annInteriorRatio, annLargeAngleRatio, div_le_div_iff₀ hm hden]
  nlinarith

/-- `0 ≤ annH r` forces the large-angle branch below the interior branch. -/
theorem ann_large_le_interior_of_H {r : ℝ} (hr0 : 0 ≤ r) (hrh : r < 1 / 2)
    (hH : 0 ≤ annH r) : annLargeAngleRatio r ≤ annInteriorRatio r := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * r) := ann_largeAngle_den_pos r
  have hm : 0 < 1 - 2 * r := by linarith
  have hp : 0 < 1 + 2 * r := by linarith
  have hatan : Real.arctan (2 * r) ≤ Real.pi * (6 * r - 1) / (2 * (1 + 2 * r)) := by
    dsimp [annH] at hH; linarith
  have hkey : (1 + 2 * r) * Real.arctan (2 * r) ≤ Real.pi * (6 * r - 1) / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (1 + 2 * r))] at hatan
    nlinarith
  rw [annInteriorRatio, annLargeAngleRatio, div_le_div_iff₀ hden hm]
  nlinarith

/-! ### The three rational gates on the transcendental comparisons -/

theorem ann_gate_frozen :
    annPiUpper / 2 - annPiLower / annFrozenRatio ≤ annAtanLower6 (2 * annA) := by
  norm_num [annPiUpper, annPiLower, annFrozenRatio, annRLambda, annAtanLower6, annA]

theorem ann_gate_HqL :
    annPiUpper * (6 * annQL - 1) / (2 * (1 + 2 * annQL)) ≤
      annAtanLower6 (2 * annQL) := by
  norm_num [annPiUpper, annAtanLower6, annQL]

theorem ann_gate_HqR :
    annPiUpper / 4 - annAtanLower6 ((1 - 2 * annQR) / (1 + 2 * annQR)) ≤
      annPiLower * (6 * annQR - 1) / (2 * (1 + 2 * annQR)) := by
  norm_num [annPiUpper, annPiLower, annAtanLower6, annQR]

/-! ### The frozen branch is hidden on the whole interval -/

/-- At the left endpoint the large-angle branch already exceeds the frozen
branch: `2.392472… > 2.384552…`. -/
theorem ann_frozen_le_large_at_annA : annFrozenRatio ≤ annLargeAngleRatio annA := by
  have hden : 0 < Real.pi / 2 - Real.arctan (2 * annA) := ann_largeAngle_den_pos annA
  have hlow : annAtanLower6 (2 * annA) ≤ Real.arctan (2 * annA) :=
    ann_atanLower6_le (by norm_num [annA]) (by norm_num [annA])
  have hgate := ann_gate_frozen
  have hpl := ann_pi_lower_lt
  have hpu := ann_pi_lt_upper
  have hfr : 0 < annFrozenRatio := annFrozenRatio_pos
  have hstep : Real.pi / 2 - Real.pi / annFrozenRatio ≤ Real.arctan (2 * annA) := by
    have h1 : Real.pi / 2 ≤ annPiUpper / 2 := by linarith
    have h2 : annPiLower / annFrozenRatio ≤ Real.pi / annFrozenRatio := by
      rw [div_le_div_iff₀ hfr hfr]
      nlinarith
    linarith
  rw [annLargeAngleRatio, le_div_iff₀ hden]
  have hpi : Real.pi / annFrozenRatio * annFrozenRatio = Real.pi := by
    field_simp
  nlinarith

/-- The large-angle branch is increasing, so the frozen branch stays hidden. -/
theorem ann_frozen_le_large {r : ℝ} (hr : annA ≤ r) :
    annFrozenRatio ≤ annLargeAngleRatio r := by
  refine ann_frozen_le_large_at_annA.trans ?_
  have hat : Real.arctan (2 * annA) ≤ Real.arctan (2 * r) :=
    Real.arctan_mono (by linarith)
  rw [annLargeAngleRatio, annLargeAngleRatio]
  apply div_le_div_of_nonneg_left ann_pi_pos.le (ann_largeAngle_den_pos r)
  linarith

/-! ### The two retained segments, and no re-crossing -/

theorem ann_H_annQL_nonpos : annH annQL ≤ 0 := by
  have hlow : annAtanLower6 (2 * annQL) ≤ Real.arctan (2 * annQL) :=
    ann_atanLower6_le (by norm_num [annQL]) (by norm_num [annQL])
  have hgate := ann_gate_HqL
  have hpu := ann_pi_lt_upper
  have hmono : Real.pi * (6 * annQL - 1) / (2 * (1 + 2 * annQL)) ≤
      annPiUpper * (6 * annQL - 1) / (2 * (1 + 2 * annQL)) := by
    apply div_le_div_of_nonneg_right ?_ (by norm_num [annQL])
    nlinarith [show (0:ℝ) < 6 * annQL - 1 by norm_num [annQL]]
  dsimp [annH]
  linarith

theorem ann_H_annQR_nonneg : 0 ≤ annH annQR := by
  have hup : Real.arctan (2 * annQR) ≤
      Real.pi / 4 - annAtanLower6 ((1 - 2 * annQR) / (1 + 2 * annQR)) :=
    ann_arctan_le_of_reflect (by norm_num [annQR]) (by norm_num [annQR])
  have hgate := ann_gate_HqR
  have hpl := ann_pi_lower_lt
  have hpu := ann_pi_lt_upper
  have hmono : annPiLower * (6 * annQR - 1) / (2 * (1 + 2 * annQR)) ≤
      Real.pi * (6 * annQR - 1) / (2 * (1 + 2 * annQR)) := by
    apply div_le_div_of_nonneg_right ?_ (by norm_num [annQR])
    nlinarith [show (0:ℝ) < 6 * annQR - 1 by norm_num [annQR]]
  have hpi4 : Real.pi / 4 ≤ annPiUpper / 4 := by linarith
  dsimp [annH]
  linarith

/-- **The large-angle branch is the active one on `[annA, annQL]`.** -/
theorem ann_paperG_eq_large {r : ℝ} (hrL : annA ≤ r) (hrR : r ≤ annQL) :
    annPaperG r = annLargeAngleRatio r := by
  have hr0 : (0 : ℝ) ≤ r := le_trans (by norm_num [annA]) hrL
  have hrh : r < 1 / 2 := lt_of_le_of_lt hrR (by norm_num [annQL])
  have hH : annH r ≤ 0 :=
    le_trans (ann_H_monotoneOn hr0 (by simp [annQL]; norm_num) hrR) ann_H_annQL_nonpos
  have hint : annInteriorRatio r ≤ annLargeAngleRatio r :=
    ann_interior_le_large_of_H hr0 hrh hH
  have hfr : annFrozenRatio ≤ annLargeAngleRatio r := ann_frozen_le_large hrL
  rw [annPaperG, max_eq_right (le_max_of_le_right hint), max_eq_right hfr]

/-- **The interior branch is the active one on `[annQR, annR₀]`.** -/
theorem ann_paperG_eq_interior {r : ℝ} (hrL : annQR ≤ r) (hrR : r ≤ annR₀) :
    annPaperG r = annInteriorRatio r := by
  have hr0 : (0 : ℝ) ≤ r := le_trans (by norm_num [annQR]) hrL
  have hrh : r < 1 / 2 := lt_of_le_of_lt hrR (by norm_num [annR₀])
  have hH : 0 ≤ annH r :=
    le_trans ann_H_annQR_nonneg
      (ann_H_monotoneOn (by norm_num [annQR]) hr0 hrL)
  have hlarge : annLargeAngleRatio r ≤ annInteriorRatio r :=
    ann_large_le_interior_of_H hr0 hrh hH
  have hfrozen : annFrozenRatio ≤ annInteriorRatio r := by
    rw [annFrozenRatio, annInteriorRatio]
    have hd1 : 0 < 1 - 2 * annRLambda := by norm_num [annRLambda]
    have hd2 : 0 < 1 - 2 * r := by linarith
    rw [div_le_div_iff₀ hd1 hd2]
    have : (2353 : ℝ) / 10000 ≤ r := by simpa [annQR] using hrL
    norm_num [annRLambda]
    nlinarith
  rw [annPaperG, max_eq_left (max_le hfrozen hlarge)]

/-! ## Primitives and the fundamental theorem of calculus -/

/-- `r / annLargeAngleRatio r` on the left segment. -/
def annLargeIntegrand (r : ℝ) : ℝ := r * (Real.pi / 2 - Real.arctan (2 * r)) / Real.pi

/-- An exact primitive of `annLargeIntegrand`. -/
def annLargePrimitive (r : ℝ) : ℝ :=
  r ^ 2 / 4 - ((4 * r ^ 2 + 1) / 8 * Real.arctan (2 * r) - r / 4) / Real.pi

/-- `r / annInteriorRatio r` on the right segment. -/
def annRightIntegrand (r : ℝ) : ℝ := r * (1 - 2 * r) / (1 + 2 * r)

/-- An exact primitive of `annRightIntegrand`. -/
def annRightPrimitive (r : ℝ) : ℝ := -r ^ 2 / 2 + r - Real.log (1 + 2 * r) / 2

theorem ann_hasDerivAt_largePrimitive (r : ℝ) :
    HasDerivAt annLargePrimitive (annLargeIntegrand r) r := by
  have hq : (1 : ℝ) + (2 * r) ^ 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hatan : HasDerivAt (fun x : ℝ => Real.arctan (2 * x))
      (1 / (1 + (2 * r) ^ 2) * 2) r := by
    have h := (Real.hasDerivAt_arctan (2 * r)).comp r
      ((hasDerivAt_id r).const_mul 2)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have hcoef : HasDerivAt (fun x : ℝ => (4 * x ^ 2 + 1) / 8) r r := by
    have h := (((hasDerivAt_id r).pow 2).const_mul (4 : ℝ)).add_const (1 : ℝ)
    have h2 := h.div_const 8
    convert h2 using 1
    simp only [id_eq]
    ring
  have hu := (hcoef.mul hatan).sub ((hasDerivAt_id r).div_const 4)
  have hsq := ((hasDerivAt_id r).pow 2).div_const 4
  have h := hsq.sub (hu.div_const Real.pi)
  convert h using 1
  simp only [id_eq]
  dsimp [annLargeIntegrand]
  field_simp
  ring

theorem ann_continuous_largeIntegrand : Continuous annLargeIntegrand := by
  apply Continuous.div_const
  exact continuous_id.mul (continuous_const.sub
    (Real.continuous_arctan.comp (continuous_const.mul continuous_id)))

theorem ann_left_interval_integral :
    (∫ r in annA..annQL, annLargeIntegrand r) =
      annLargePrimitive annQL - annLargePrimitive annA := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => ann_hasDerivAt_largePrimitive r) ?_
  exact ann_continuous_largeIntegrand.intervalIntegrable _ _

theorem ann_hasDerivAt_rightPrimitive {r : ℝ} (hr : 1 + 2 * r ≠ 0) :
    HasDerivAt annRightPrimitive (annRightIntegrand r) r := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + 2 * x) 2 r := by
    convert (hasDerivAt_const r 1).add
      ((hasDerivAt_const r 2).mul (hasDerivAt_id r)) using 1
    simp only [id_eq]
    ring
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + 2 * x))
      (2 * (1 + 2 * r)⁻¹) r := by
    convert (Real.hasDerivAt_log hr).comp r hinner using 1
    ring
  have hprimitive : HasDerivAt annRightPrimitive (-r + 1 - (1 + 2 * r)⁻¹) r := by
    dsimp [annRightPrimitive]
    have hpoly := (((hasDerivAt_id r).pow 2).neg.div_const 2).add (hasDerivAt_id r)
    convert hpoly.sub (hlog.div_const 2) using 1
    simp only [id_eq]
    ring
  convert hprimitive using 1
  dsimp [annRightIntegrand]
  have hr' : 1 + r * 2 ≠ 0 := by simpa [mul_comm] using hr
  field_simp [hr, hr']
  ring

theorem ann_continuousOn_rightIntegrand :
    ContinuousOn annRightIntegrand (uIcc annQR annR₀) := by
  rw [uIcc_of_le (by norm_num [annQR, annR₀])]
  intro r hr
  apply ContinuousAt.continuousWithinAt
  have hden : 1 + 2 * r ≠ 0 := by
    have := hr.1
    norm_num [annQR] at this ⊢
    linarith
  change ContinuousAt (fun x : ℝ => x * (1 - 2 * x) / (1 + 2 * x)) r
  exact (continuousAt_id.mul (continuousAt_const.sub
    (continuousAt_const.mul continuousAt_id))).div
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) hden

theorem ann_right_interval_integral :
    (∫ r in annQR..annR₀, annRightIntegrand r) =
      annRightPrimitive annR₀ - annRightPrimitive annQR := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => ?_)
    ann_continuousOn_rightIntegrand.intervalIntegrable
  have hrange : r ∈ Icc annQR annR₀ := by
    simpa only [uIcc_of_le (show annQR ≤ annR₀ by norm_num [annQR, annR₀])] using hr
  apply ann_hasDerivAt_rightPrimitive
  have := hrange.1
  norm_num [annQR] at this ⊢
  linarith

/-! ## The exact `log` enclosure with the strengthened tail

The three-term partial sum plus the crude tail `2 z^7 / (1 - z^2)` used by the
`π/56` route is *not* good enough at this target: it overshoots by a factor
seven on the tail and eats the whole `9.7·10⁻⁷` margin.  The bound below uses
`1 / (2k + 7) ≤ 1 / 7` on every tail term, i.e. the tail
`2 z^7 / (7 (1 - z^2))`. -/

def annLogX : ℝ := (1 + 2 * annR₀) / (1 + 2 * annQR) - 1

def annLogZ : ℝ := annLogX / (annLogX + 2)

def annLogGeomUpper : ℝ :=
  2 * annLogZ + 2 * annLogZ ^ 3 / 3 + 2 * annLogZ ^ 5 / 5
    + 2 * annLogZ ^ 7 / (7 * (1 - annLogZ ^ 2))

theorem annLogZ_eq : annLogZ = 1321 / 8674 := by
  norm_num [annLogZ, annLogX, annR₀, annQR]

theorem ann_log_geom_upper : Real.log (1 + annLogX) ≤ annLogGeomUpper := by
  have hx : 0 ≤ annLogX := by norm_num [annLogX, annR₀, annQR]
  have hz : annLogX / (annLogX + 2) = annLogZ := rfl
  have hsum := Real.hasSum_log_one_add hx
  rw [hz] at hsum
  set term : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * annLogZ ^ (2 * k + 1)
    with hterm_def
  change HasSum term (Real.log (1 + annLogX)) at hsum
  have hsplit := hsum.summable.sum_add_tsum_nat_add 3
  rw [hsum.tsum_eq] at hsplit
  have hz0 : 0 ≤ annLogZ := by rw [annLogZ_eq]; norm_num
  have hz1 : annLogZ < 1 := by rw [annLogZ_eq]; norm_num
  have hpoint : ∀ n : ℕ, term (n + 3) ≤ 2 / 7 * annLogZ ^ 7 * (annLogZ ^ 2) ^ n := by
    intro n
    have hd : (1 : ℝ) / (2 * ((n + 3 : ℕ) : ℝ) + 1) ≤ 1 / 7 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      term (n + 3) ≤ 2 / 7 * annLogZ ^ (2 * (n + 3) + 1) := by
        rw [hterm_def]
        have hpow : (0 : ℝ) ≤ annLogZ ^ (2 * (n + 3) + 1) := pow_nonneg hz0 _
        have : 2 * (1 / (2 * ((n + 3 : ℕ) : ℝ) + 1)) ≤ 2 / 7 := by linarith
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right this hpow
      _ = 2 / 7 * annLogZ ^ 7 * (annLogZ ^ 2) ^ n := by
        rw [show 2 * (n + 3) + 1 = 7 + 2 * n by omega]
        simp only [pow_add, pow_mul]
        ring
  have htermTail : Summable (fun n : ℕ => term (n + 3)) := by
    simpa only [Function.comp_apply] using
      hsum.summable.comp_injective (i := fun n : ℕ => n + 3) (by
        intro m n h; exact Nat.add_right_cancel h)
  have hzsq : ‖annLogZ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg annLogZ)]
    nlinarith [sq_nonneg (annLogZ - 1)]
  have hgeom : Summable (fun n : ℕ => 2 / 7 * annLogZ ^ 7 * (annLogZ ^ 2) ^ n) :=
    (summable_geometric_of_norm_lt_one hzsq).mul_left _
  have htail : ∑' n : ℕ, term (n + 3) ≤
      2 * annLogZ ^ 7 / (7 * (1 - annLogZ ^ 2)) := by
    calc
      ∑' n : ℕ, term (n + 3) ≤
          ∑' n : ℕ, 2 / 7 * annLogZ ^ 7 * (annLogZ ^ 2) ^ n :=
        htermTail.tsum_le_tsum hpoint hgeom
      _ = 2 * annLogZ ^ 7 / (7 * (1 - annLogZ ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg annLogZ)
          (by nlinarith [sq_nonneg (annLogZ - 1)])]
        have hne : (1 : ℝ) - annLogZ ^ 2 ≠ 0 := by
          nlinarith [sq_nonneg (annLogZ - 1)]
        field_simp
  rw [← hsplit]
  change (∑ i ∈ Finset.range 3, term i) + ∑' i : ℕ, term (i + 3) ≤ _
  calc
    _ ≤ (∑ i ∈ Finset.range 3, term i) +
        2 * annLogZ ^ 7 / (7 * (1 - annLogZ ^ 2)) := add_le_add_right htail _
    _ = annLogGeomUpper := by
      rw [hterm_def]
      norm_num [annLogGeomUpper, Finset.sum_range_succ]
      ring

/-! ## The two segment lower bounds -/

def annILeftLower : ℝ := 732633 / 10 ^ 8

def annIRightLower : ℝ := 136446 / 10 ^ 7

def annCoeffA : ℝ := (4 * annA ^ 2 + 1) / 8

def annCoeffQL : ℝ := (4 * annQL ^ 2 + 1) / 8

def annYQL : ℝ := (1 - 2 * annQL) / (1 + 2 * annQL)

/-- The rational aggregate of the left segment: everything but the `1/π`. -/
def annLeftC : ℝ :=
  annCoeffA * annAtanLower6 (2 * annA) + (annQL - annA) / 4
    + annCoeffQL * annAtanLower6 annYQL

theorem annLeftC_pos : 0 < annLeftC := by
  norm_num [annLeftC, annCoeffA, annCoeffQL, annAtanLower6, annYQL, annA, annQL]

/-- The closing rational gate of the left segment. -/
theorem ann_gate_left :
    annILeftLower ≤
      (annQL ^ 2 - annA ^ 2) / 4 + annLeftC / annPiUpper - annCoeffQL / 4 := by
  norm_num [annILeftLower, annLeftC, annCoeffA, annCoeffQL, annAtanLower6,
    annYQL, annPiUpper, annA, annQL]

/-- The closing rational gate of the right segment. -/
theorem ann_gate_right :
    annIRightLower ≤ (-annR₀ ^ 2 / 2 + annR₀) - (-annQR ^ 2 / 2 + annQR)
      - annLogGeomUpper / 2 := by
  rw [annLogGeomUpper, annLogZ_eq]
  norm_num [annIRightLower, annR₀, annQR]

theorem ann_left_primitive_lower :
    annILeftLower ≤ annLargePrimitive annQL - annLargePrimitive annA := by
  have hpi0 : 0 < Real.pi := ann_pi_pos
  have hpu : Real.pi < annPiUpper := ann_pi_lt_upper
  have hA : annAtanLower6 (2 * annA) ≤ Real.arctan (2 * annA) :=
    ann_atanLower6_le (by norm_num [annA]) (by norm_num [annA])
  have hQL : Real.arctan (2 * annQL) ≤ Real.pi / 4 - annAtanLower6 annYQL := by
    have h := ann_arctan_le_of_reflect (x := 2 * annQL) (by norm_num [annQL])
      (by norm_num [annQL])
    simpa only [annYQL] using h
  have hcA : (0 : ℝ) ≤ annCoeffA := by norm_num [annCoeffA, annA]
  have hcQL : (0 : ℝ) ≤ annCoeffQL := by norm_num [annCoeffQL, annQL]
  -- the numerator of the `1/π` part, bounded below by `annLeftC - annCoeffQL * π/4`
  have hnum : annLeftC - annCoeffQL * (Real.pi / 4) ≤
      annCoeffA * Real.arctan (2 * annA) - annCoeffQL * Real.arctan (2 * annQL)
        + (annQL - annA) / 4 := by
    have h1 : annCoeffA * annAtanLower6 (2 * annA) ≤
        annCoeffA * Real.arctan (2 * annA) := by
      exact mul_le_mul_of_nonneg_left hA hcA
    have h2 : annCoeffQL * Real.arctan (2 * annQL) ≤
        annCoeffQL * (Real.pi / 4 - annAtanLower6 annYQL) :=
      mul_le_mul_of_nonneg_left hQL hcQL
    dsimp [annLeftC]
    nlinarith
  -- divide by π
  have hdiv : (annLeftC - annCoeffQL * (Real.pi / 4)) / Real.pi ≤
      (annCoeffA * Real.arctan (2 * annA) - annCoeffQL * Real.arctan (2 * annQL)
        + (annQL - annA) / 4) / Real.pi :=
    div_le_div_of_nonneg_right hnum hpi0.le
  have hsplit : (annLeftC - annCoeffQL * (Real.pi / 4)) / Real.pi =
      annLeftC / Real.pi - annCoeffQL / 4 := by
    field_simp
  have hC : annLeftC / annPiUpper ≤ annLeftC / Real.pi :=
    div_le_div_of_nonneg_left annLeftC_pos.le hpi0 hpu.le
  have hexp : annLargePrimitive annQL - annLargePrimitive annA =
      (annQL ^ 2 - annA ^ 2) / 4 +
        (annCoeffA * Real.arctan (2 * annA) - annCoeffQL * Real.arctan (2 * annQL)
          + (annQL - annA) / 4) / Real.pi := by
    dsimp [annLargePrimitive, annCoeffA, annCoeffQL]
    field_simp
    ring
  rw [hexp]
  have hgate := ann_gate_left
  rw [hsplit] at hdiv
  linarith

theorem ann_right_primitive_lower :
    annIRightLower ≤ annRightPrimitive annR₀ - annRightPrimitive annQR := by
  have hlog : Real.log (1 + 2 * annR₀) - Real.log (1 + 2 * annQR) =
      Real.log (1 + annLogX) := by
    rw [← Real.log_div (by norm_num [annR₀]) (by norm_num [annQR])]
    congr 1
    norm_num [annLogX, annR₀, annQR]
  have hgate := ann_gate_right
  have hup := ann_log_geom_upper
  dsimp [annRightPrimitive]
  rw [show -annR₀ ^ 2 / 2 + annR₀ - Real.log (1 + 2 * annR₀) / 2 -
      (-annQR ^ 2 / 2 + annQR - Real.log (1 + 2 * annQR) / 2) =
      (-annR₀ ^ 2 / 2 + annR₀) - (-annQR ^ 2 / 2 + annQR)
        - (Real.log (1 + 2 * annR₀) - Real.log (1 + 2 * annQR)) / 2 by ring]
  rw [hlog]
  linarith

/-! ## Assembly: the real integral, then the `∫⁻` form -/

theorem ann_continuousOn_radial_mono {s : Set ℝ} (hs : s ⊆ Icc annA annR₀) :
    ContinuousOn (fun r => r / annPaperG r) s :=
  ann_continuousOn_radial.mono hs

private theorem ann_intervalIntegrable {a b : ℝ}
    (hs : uIcc a b ⊆ Icc annA annR₀) :
    IntervalIntegrable (fun r => r / annPaperG r) volume a b :=
  (ann_continuousOn_radial.mono hs).intervalIntegrable

theorem annILower_le_intervalIntegral :
    annILower ≤ ∫ r in annA..annR₀, r / annPaperG r := by
  have hAL : annA ≤ annQL := by norm_num [annA, annQL]
  have hLR : annQL ≤ annQR := by norm_num [annQL, annQR]
  have hRR : annQR ≤ annR₀ := by norm_num [annQR, annR₀]
  have hfL : IntervalIntegrable (fun r => r / annPaperG r) volume annA annQL := by
    apply ann_intervalIntegrable
    rw [uIcc_of_le hAL]
    exact Icc_subset_Icc le_rfl (hLR.trans hRR)
  have hfM : IntervalIntegrable (fun r => r / annPaperG r) volume annQL annQR := by
    apply ann_intervalIntegrable
    rw [uIcc_of_le hLR]
    exact Icc_subset_Icc hAL hRR
  have hfR : IntervalIntegrable (fun r => r / annPaperG r) volume annQR annR₀ := by
    apply ann_intervalIntegrable
    rw [uIcc_of_le hRR]
    exact Icc_subset_Icc (hAL.trans hLR) le_rfl
  -- the left segment computes the large-angle primitive
  have hleft : (∫ r in annA..annQL, r / annPaperG r) =
      annLargePrimitive annQL - annLargePrimitive annA := by
    rw [← ann_left_interval_integral]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hAL]
    intro r hr
    change r / annPaperG r = annLargeIntegrand r
    rw [ann_paperG_eq_large hr.1 hr.2, annLargeAngleRatio, annLargeIntegrand,
      div_div_eq_mul_div]
  -- the right segment computes the interior primitive
  have hright : (∫ r in annQR..annR₀, r / annPaperG r) =
      annRightPrimitive annR₀ - annRightPrimitive annQR := by
    rw [← ann_right_interval_integral]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hRR]
    intro r hr
    change r / annPaperG r = annRightIntegrand r
    have hp : (1 : ℝ) + 2 * r ≠ 0 := by
      have := hr.1
      norm_num [annQR] at this ⊢
      linarith
    have hm : (1 : ℝ) - 2 * r ≠ 0 := by
      have := hr.2
      norm_num [annR₀] at this ⊢
      linarith
    rw [ann_paperG_eq_interior hr.1 hr.2, annInteriorRatio, annRightIntegrand]
    change r / ((1 + 2 * r) / (1 - 2 * r)) = r * (1 - 2 * r) / (1 + 2 * r)
    field_simp
  -- the straddling gap is discarded by nonnegativity, not covered by a branch
  have hmiddle : 0 ≤ ∫ r in annQL..annQR, r / annPaperG r := by
    apply intervalIntegral.integral_nonneg hLR
    intro r hr
    apply div_nonneg _ (annPaperG_pos r).le
    have : (0 : ℝ) ≤ annQL := by norm_num [annQL]
    linarith [hr.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hfL.trans hfM) hfR,
    ← intervalIntegral.integral_add_adjacent_intervals hfL hfM, hleft, hright]
  have := ann_left_primitive_lower
  have := ann_right_primitive_lower
  have hsum : annILower ≤ annILeftLower + annIRightLower := by
    norm_num [annILower, annILeftLower, annIRightLower]
  linarith

theorem annILower_le_integral :
    annILower ≤ ∫ r in Icc annA annR₀, r / annPaperG r := by
  refine annILower_le_intervalIntegral.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_of_le (by norm_num [annA, annR₀]),
    MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem ann_integrableOn_radial :
    IntegrableOn (fun r => r / annPaperG r) (Icc annA annR₀) volume :=
  ann_continuousOn_radial.integrableOn_compact isCompact_Icc

theorem ann_radial_nonneg_ae :
    0 ≤ᵐ[volume.restrict (Icc annA annR₀)] fun r => r / annPaperG r := by
  filter_upwards [self_mem_ae_restrict (measurableSet_Icc (a := annA) (b := annR₀))]
    with r hr
  apply div_nonneg _ (annPaperG_pos r).le
  exact le_trans (by norm_num [annA]) hr.1

/-- **The wrapper-facing `hI` input of the M5 confined interface.**

`ENNReal.ofReal annILower ≤ ∫⁻ r in Icc annA annR₀, ENNReal.ofReal (r / annPaperG r)`
-/
theorem annILower_le_lintegral :
    ENNReal.ofReal annILower ≤
      ∫⁻ r in Icc annA annR₀, ENNReal.ofReal (r / annPaperG r) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ann_integrableOn_radial
    ann_radial_nonneg_ae]
  exact ENNReal.ofReal_le_ofReal annILower_le_integral

/-- The annular target sits strictly below the certified radial gain. -/
theorem annTarget_lt_annILower : annTarget < annILower := by
  norm_num [annTarget, annILower]

end

end StarKakeyaLower
