import StarKakeyaLower.AnnularCaseIIntegral
import StarKakeyaLower.EndpointConfinedExit

/-!
# The Figure-5 endpoint package of the joint inner/outer annular tuple

This module instantiates the CLEAN milestone-M6 endpoint interface
(`Figure5EndpointDomain` / `Figure5EndpointAnalyticPackage` of
`StarKakeyaLower.Figure5EndpointDomain`) at the production parameter tuple
`(annA, annR₀, annR₁, annPaperG)` fixed by `StarKakeyaLower.AnnularKernel` and
`StarKakeyaLower.AnnularCaseIIntegral`, and closes the confined branch of the
route by feeding that package into `confined_lower_bound_of_endpointDomain`.

## Import hygiene

The import closure is `AnnularCaseIIntegral` (⊂ `AnnularKernel` ⊂ `Mathlib`) and
`EndpointConfinedExit`, both of which are CLEAN in the sense of
`spikes/001-joint-inner-outer/M6-ENDPOINT-STATUS.md`: neither reaches
`StarKakeyaLower.StrongerKernel` nor `StarKakeyaLower.Figure5FrozenPackage`.
In particular **`base_ray_frozen_analytic` is not reachable from this module**.
That certificate is a rational polynomial split at `t = 7/100` which is *false*
at the height cap `annA` of this tuple; the base-ray gate below is proved from
scratch, directly against `annPaperG`.

## The three package obligations

* Domination **(A)** `strongInteriorRatio r ≤ annPaperG r` and **(B)**
  `strongLargeAngleRatio r ≤ annPaperG r` are definitional: the generic ratios
  of `Figure5EndpointDomain` are syntactically the `annInteriorRatio` /
  `annLargeAngleRatio` branches of the `annPaperG` maximum, so each is one
  `le_max_*` step.  They hold on *all* of `ℝ`, not merely on `Icc annA annR₀`.
* **(C)** `base_ray_gap` is the only deep gate.  It is discharged by
  `ann_base_ray_gap` below.

## The base-ray certificate

Write `k = 25000/14773` and `l = k - 1 = 10227/14773`, so that
`2k - 1 = 35227/14773 = annFrozenRatio` exactly (`ann_two_annBaseK_sub_one`).
It therefore suffices to prove the *strict scalar* statement `α < k t`, since
then `2α - t < (2k-1) t = annFrozenRatio * t ≤ annPaperG r * t`.

Assume for contradiction `k t ≤ α`.  Then `l t ≤ α - t`, and both `k t` and
`l t` lie in `[0, π/2]`, so `sin` is monotone at both places.  Three exact
rational branches close the assumption:

| branch | scalar gate | certified in |
|---|---|---|
| `0 < t ≤ 3/25` | `annR₁Upper * t < sin (k t)` | `ann_baseRay_small` |
| `3/25 ≤ t ≤ 1/2` | `annA * t < sin (k t) * sin (l t)` | `ann_baseRay_mid` |
| `1/2 < t` | `annA * t < k l t² / 4` | `ann_baseRay_large_poly` |

The small branch contradicts the `R₁`-norm hypothesis `sin α ≤ annR₁ sin t`
(with `sin t < t` and the reviewed kernel enclosure `ann_r₁_upper`); the middle
and large branches contradict the one-chord height hypothesis
`sin α * sin (α - t) ≤ annA * sin t` (with `sin t ≤ t`).

All three gates are decided by exact rational arithmetic on top of three
Mathlib sine estimates — `Real.sin_bound` (Taylor with the `5/96 x⁴`
remainder), `Real.sin_gt_sub_cube` and `Real.mul_le_sin` (Jordan) — with no
`native_decide`, no interval oracle and no floating-point evaluation.
-/

open Set Real MeasureTheory
open scoped ENNReal

namespace StarKakeyaLower

noncomputable section

/-! ## The rational cut constants of the base-ray certificate -/

/-- The base-ray slope cut `k`, chosen so that `2k - 1 = annFrozenRatio`. -/
def annBaseK : ℝ := 25000 / 14773

/-- The companion slope `l = k - 1`, the cut for the *lagging* angle `α - t`. -/
def annBaseL : ℝ := 10227 / 14773

theorem annBaseK_pos : 0 < annBaseK := by norm_num [annBaseK]

theorem annBaseL_pos : 0 < annBaseL := by norm_num [annBaseL]

/-- `l = k - 1`: this is what turns `k t ≤ α` into `l t ≤ α - t`. -/
theorem ann_annBaseL_eq : annBaseL = annBaseK - 1 := by
  norm_num [annBaseL, annBaseK]

/-- `2k - 1 = annFrozenRatio`, exactly.  This is the whole reason for the value
of `k`: the scalar cut `α < k t` converts into the package conclusion without
any slack. -/
theorem ann_two_annBaseK_sub_one : 2 * annBaseK - 1 = annFrozenRatio := by
  rw [annFrozenRatio_eq]; norm_num [annBaseK]

/-- The frozen branch of the paper maximum, available at every radius. -/
theorem ann_frozen_le_annPaperG (r : ℝ) : annFrozenRatio ≤ annPaperG r :=
  le_max_of_le_right (le_max_left _ _)

/-! ## Branch 1 — the small-angle gate

`annR₁Upper * t < sin (k t)` for `0 < t ≤ 3/25`.

The Taylor lower bound `x - x³/6 - (5/96) x⁴ ≤ sin x` is `Real.sin_bound`, valid
because `k * (3/25) < 1`.  After dividing by `t` the gate is the exact rational
inequality

`annR₁Upper < k - k³ t²/6 - (5/96) k⁴ t³`,

whose worst case `t = 3/25` leaves the margin `0.00414362952857…`. -/

theorem ann_sin_taylor_lower {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x - x ^ 3 / 6 - x ^ 4 * (5 / 96) ≤ Real.sin x := by
  have habs : |x| ≤ 1 := by rwa [abs_of_pos hx0]
  have hb := Real.sin_bound habs
  rw [abs_of_pos hx0] at hb
  have := (abs_le.1 hb).1
  linarith

theorem ann_baseRay_small {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 3 / 25) :
    annR₁Upper * t < Real.sin (annBaseK * t) := by
  have hx0 : 0 < annBaseK * t := mul_pos annBaseK_pos ht0
  have hx1 : annBaseK * t ≤ 1 := by
    have : annBaseK * t ≤ annBaseK * (3 / 25) :=
      mul_le_mul_of_nonneg_left ht annBaseK_pos.le
    refine this.trans ?_
    norm_num [annBaseK]
  have hlow := ann_sin_taylor_lower hx0 hx1
  refine lt_of_lt_of_le ?_ hlow
  have ht2 : t ^ 2 ≤ (3 / 25 : ℝ) ^ 2 := by nlinarith
  have ht3 : t ^ 3 ≤ (3 / 25 : ℝ) ^ 3 := by nlinarith
  -- the bracket inequality, exact rational arithmetic
  have hbr : annR₁Upper <
      annBaseK - annBaseK ^ 3 * t ^ 2 / 6 - annBaseK ^ 4 * t ^ 3 * (5 / 96) := by
    have hk3 : (0 : ℝ) < annBaseK ^ 3 := by norm_num [annBaseK]
    have hk4 : (0 : ℝ) < annBaseK ^ 4 := by norm_num [annBaseK]
    have h2 : annBaseK ^ 3 * t ^ 2 / 6 ≤ annBaseK ^ 3 * (3 / 25 : ℝ) ^ 2 / 6 := by
      nlinarith
    have h3 : annBaseK ^ 4 * t ^ 3 * (5 / 96) ≤
        annBaseK ^ 4 * (3 / 25 : ℝ) ^ 3 * (5 / 96) := by nlinarith
    have hnum : annR₁Upper <
        annBaseK - annBaseK ^ 3 * (3 / 25 : ℝ) ^ 2 / 6 -
          annBaseK ^ 4 * (3 / 25 : ℝ) ^ 3 * (5 / 96) := by
      norm_num [annR₁Upper, annBaseK]
    linarith
  have hmul := mul_lt_mul_of_pos_right hbr ht0
  have heq :
      (annBaseK - annBaseK ^ 3 * t ^ 2 / 6 - annBaseK ^ 4 * t ^ 3 * (5 / 96)) * t =
        annBaseK * t - (annBaseK * t) ^ 3 / 6 - (annBaseK * t) ^ 4 * (5 / 96) := by
    ring
  linarith [heq ▸ hmul]

/-! ## Branch 2 — the mid-angle gate

`annA * t < sin (k t) * sin (l t)` for `3/25 ≤ t ≤ 1/2`.

Both arguments stay in `(0, 1]` (`k/2 = 0.8461…`), so `Real.sin_gt_sub_cube`
applies to each.  Dividing the resulting polynomial gate by `t²` gives

`annA < t * (k - k³t²/4) * (l - l³t²/4)`,

whose right-hand side is increasing in `t` through the leading factor and
decreasing through `t²`; a single cut at `t = 1/5` therefore suffices, and each
half is decided by freezing `t` at its lower end and `t²` at its upper end.
Margins: `0.00413232333…` on `[3/25, 1/5]` and `0.05483507955…` on `[1/5, 1/2]`. -/

theorem ann_baseRay_mid_poly {t : ℝ} (ht : 3 / 25 ≤ t) (ht2 : t ≤ 1 / 2) :
    annA < t * ((annBaseK - annBaseK ^ 3 * t ^ 2 / 4) *
      (annBaseL - annBaseL ^ 3 * t ^ 2 / 4)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  rcases le_or_gt t (1 / 5) with hcut | hcut
  · -- `t² ≤ 1/25`
    have hs : t ^ 2 ≤ 1 / 25 := by nlinarith
    have hk3 : (0 : ℝ) < annBaseK ^ 3 := by norm_num [annBaseK]
    have hl3 : (0 : ℝ) < annBaseL ^ 3 := by norm_num [annBaseL]
    have hu : annBaseK - annBaseK ^ 3 / 100 ≤
        annBaseK - annBaseK ^ 3 * t ^ 2 / 4 := by nlinarith
    have hv : annBaseL - annBaseL ^ 3 / 100 ≤
        annBaseL - annBaseL ^ 3 * t ^ 2 / 4 := by nlinarith
    have hu0 : (0 : ℝ) < annBaseK - annBaseK ^ 3 / 100 := by norm_num [annBaseK]
    have hv0 : (0 : ℝ) < annBaseL - annBaseL ^ 3 / 100 := by norm_num [annBaseL]
    have hprod : (annBaseK - annBaseK ^ 3 / 100) * (annBaseL - annBaseL ^ 3 / 100) ≤
        (annBaseK - annBaseK ^ 3 * t ^ 2 / 4) *
          (annBaseL - annBaseL ^ 3 * t ^ 2 / 4) :=
      mul_le_mul hu hv hv0.le (by linarith)
    have hfin : (3 / 25 : ℝ) *
        ((annBaseK - annBaseK ^ 3 / 100) * (annBaseL - annBaseL ^ 3 / 100)) ≤
        t * ((annBaseK - annBaseK ^ 3 * t ^ 2 / 4) *
          (annBaseL - annBaseL ^ 3 * t ^ 2 / 4)) :=
      mul_le_mul ht hprod (by positivity) ht0.le
    have hnum : annA < (3 / 25 : ℝ) *
        ((annBaseK - annBaseK ^ 3 / 100) * (annBaseL - annBaseL ^ 3 / 100)) := by
      norm_num [annA, annBaseK, annBaseL]
    linarith
  · -- `t² ≤ 1/4`
    have hs : t ^ 2 ≤ 1 / 4 := by nlinarith
    have hk3 : (0 : ℝ) < annBaseK ^ 3 := by norm_num [annBaseK]
    have hl3 : (0 : ℝ) < annBaseL ^ 3 := by norm_num [annBaseL]
    have hu : annBaseK - annBaseK ^ 3 / 16 ≤
        annBaseK - annBaseK ^ 3 * t ^ 2 / 4 := by nlinarith
    have hv : annBaseL - annBaseL ^ 3 / 16 ≤
        annBaseL - annBaseL ^ 3 * t ^ 2 / 4 := by nlinarith
    have hu0 : (0 : ℝ) < annBaseK - annBaseK ^ 3 / 16 := by norm_num [annBaseK]
    have hv0 : (0 : ℝ) < annBaseL - annBaseL ^ 3 / 16 := by norm_num [annBaseL]
    have hprod : (annBaseK - annBaseK ^ 3 / 16) * (annBaseL - annBaseL ^ 3 / 16) ≤
        (annBaseK - annBaseK ^ 3 * t ^ 2 / 4) *
          (annBaseL - annBaseL ^ 3 * t ^ 2 / 4) :=
      mul_le_mul hu hv hv0.le (by linarith)
    have hfin : (1 / 5 : ℝ) *
        ((annBaseK - annBaseK ^ 3 / 16) * (annBaseL - annBaseL ^ 3 / 16)) ≤
        t * ((annBaseK - annBaseK ^ 3 * t ^ 2 / 4) *
          (annBaseL - annBaseL ^ 3 * t ^ 2 / 4)) :=
      mul_le_mul hcut.le hprod (by positivity) ht0.le
    have hnum : annA < (1 / 5 : ℝ) *
        ((annBaseK - annBaseK ^ 3 / 16) * (annBaseL - annBaseL ^ 3 / 16)) := by
      norm_num [annA, annBaseK, annBaseL]
    linarith

theorem ann_baseRay_mid {t : ℝ} (ht : 3 / 25 ≤ t) (ht2 : t ≤ 1 / 2) :
    annA * t < Real.sin (annBaseK * t) * Real.sin (annBaseL * t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hk0 : 0 < annBaseK * t := mul_pos annBaseK_pos ht0
  have hl0 : 0 < annBaseL * t := mul_pos annBaseL_pos ht0
  have hk1 : annBaseK * t ≤ 1 := by
    have : annBaseK * t ≤ annBaseK * (1 / 2) :=
      mul_le_mul_of_nonneg_left ht2 annBaseK_pos.le
    refine this.trans ?_; norm_num [annBaseK]
  have hl1 : annBaseL * t ≤ 1 := by
    have : annBaseL * t ≤ annBaseL * (1 / 2) :=
      mul_le_mul_of_nonneg_left ht2 annBaseL_pos.le
    refine this.trans ?_; norm_num [annBaseL]
  have hsk := Real.sin_gt_sub_cube hk0 hk1
  have hsl := Real.sin_gt_sub_cube hl0 hl1
  have hkcube : (annBaseK * t) ^ 3 ≤ annBaseK * t := by nlinarith [mul_pos hk0 hk0]
  have hlcube : (annBaseL * t) ^ 3 ≤ annBaseL * t := by nlinarith [mul_pos hl0 hl0]
  have hkA : (0 : ℝ) < annBaseK * t - (annBaseK * t) ^ 3 / 4 := by linarith
  have hlB : (0 : ℝ) < annBaseL * t - (annBaseL * t) ^ 3 / 4 := by linarith
  have hpoly := ann_baseRay_mid_poly ht ht2
  have hmul := mul_lt_mul_of_pos_right hpoly ht0
  have heq :
      (t * ((annBaseK - annBaseK ^ 3 * t ^ 2 / 4) *
        (annBaseL - annBaseL ^ 3 * t ^ 2 / 4))) * t =
        (annBaseK * t - (annBaseK * t) ^ 3 / 4) *
          (annBaseL * t - (annBaseL * t) ^ 3 / 4) := by ring
  have hprod : (annBaseK * t - (annBaseK * t) ^ 3 / 4) *
      (annBaseL * t - (annBaseL * t) ^ 3 / 4) <
      Real.sin (annBaseK * t) * Real.sin (annBaseL * t) :=
    mul_lt_mul'' hsk hsl hkA.le hlB.le
  have := heq ▸ hmul
  linarith

/-! ## Branch 3 — the large-angle gate

For `1/2 < t` the Jordan inequality `2x/π ≤ sin x` on `[0, π/2]`, weakened to
`x/2 < sin x` (valid because `π < 4`), is already enough: the product
`sin α · sin (α - t)` exceeds `(k t/2)(l t/2) = k l t²/4`, and `k l /8 =
0.14644039…` already exceeds `annA = 0.13177`, with margin `0.01467039…`. -/

theorem ann_half_lt_sin {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 2) :
    x / 2 < Real.sin x := by
  have hj := Real.mul_le_sin hx0.le hx
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi : Real.pi < 4 := by
    have := ann_pi_lt_upper
    have h4 : annPiUpper < (4 : ℝ) := by norm_num [annPiUpper]
    linarith
  have hcoef : (1 : ℝ) / 2 < 2 / Real.pi := by
    rw [div_lt_div_iff₀ (by norm_num) hpi0]; linarith
  nlinarith

theorem ann_baseRay_large_poly {t : ℝ} (ht : 1 / 2 < t) :
    annA * t < annBaseK * annBaseL * t ^ 2 / 4 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hkl : (0 : ℝ) < annBaseK * annBaseL := mul_pos annBaseK_pos annBaseL_pos
  have hnum : annA < annBaseK * annBaseL * (1 / 2) / 4 := by
    norm_num [annA, annBaseK, annBaseL]
  have hstep : annBaseK * annBaseL * (1 / 2) / 4 < annBaseK * annBaseL * t / 4 := by
    nlinarith
  have : annA * t < annBaseK * annBaseL * t / 4 * t := by nlinarith
  nlinarith

/-! ## The base-ray gate of the analytic package -/

/-- **The scalar cut.**  Under the two geometric hypotheses of the base-ray
branch, the endpoint angle satisfies `α < k t` strictly. -/
theorem ann_alpha_lt_annBaseK_mul {t α : ℝ} (ht0 : 0 < t)
    (hαtop : α ≤ Real.pi / 2)
    (hR1 : Real.sin α ≤ annR₁ * Real.sin t)
    (hheight : Real.sin α * Real.sin (α - t) ≤ annA * Real.sin t) :
    α < annBaseK * t := by
  by_contra hcon
  rw [not_lt] at hcon
  have hkt0 : 0 < annBaseK * t := mul_pos annBaseK_pos ht0
  have hlt0 : 0 < annBaseL * t := mul_pos annBaseL_pos ht0
  have hlt : annBaseL * t ≤ α - t := by
    have : annBaseL * t = annBaseK * t - t := by rw [ann_annBaseL_eq]; ring
    linarith
  have hkt_top : annBaseK * t ≤ Real.pi / 2 := hcon.trans hαtop
  have hαt_top : α - t ≤ Real.pi / 2 := by linarith
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsin_k : Real.sin (annBaseK * t) ≤ Real.sin α :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hαtop hcon
  rcases le_or_gt t (3 / 25) with hsmall | hbig
  · -- small branch: contradict the `R₁`-norm bound
    have hst : Real.sin t < t := Real.sin_lt ht0
    have hr₁0 : (0 : ℝ) < annR₁ := annR₁_pos
    have hr₁u : annR₁ < annR₁Upper := ann_r₁_upper
    have hchain : Real.sin α < annR₁Upper * t := by nlinarith
    have hgate := ann_baseRay_small ht0 hsmall
    linarith
  · have hsin_l : Real.sin (annBaseL * t) ≤ Real.sin (α - t) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hαt_top hlt
    have hst : Real.sin t ≤ t := Real.sin_le ht0.le
    have hsk0 : 0 ≤ Real.sin (annBaseK * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hkt0.le (by linarith)
    have hsl0 : 0 ≤ Real.sin (annBaseL * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hlt0.le (by linarith)
    have ha0 : (0 : ℝ) < annA := annA_pos
    rcases le_or_gt t (1 / 2) with hmid | hlarge
    · -- mid branch: contradict the one-chord height bound
      have hgate := ann_baseRay_mid hbig.le hmid
      have hprod : Real.sin (annBaseK * t) * Real.sin (annBaseL * t) ≤
          Real.sin α * Real.sin (α - t) :=
        mul_le_mul hsin_k hsin_l hsl0 (hsk0.trans hsin_k)
      nlinarith
    · -- large branch: Jordan on both angles
      have hα0 : 0 < α := hkt0.trans_le hcon
      have hαt0 : 0 < α - t := hlt0.trans_le hlt
      have hjα := ann_half_lt_sin hα0 hαtop
      have hjαt := ann_half_lt_sin hαt0 hαt_top
      have hklt : annBaseK * t / 2 ≤ α / 2 := by linarith
      have hllt : annBaseL * t / 2 ≤ (α - t) / 2 := by linarith
      have hprod : annBaseK * t / 2 * (annBaseL * t / 2) <
          Real.sin α * Real.sin (α - t) :=
        mul_lt_mul'' (lt_of_le_of_lt hklt hjα) (lt_of_le_of_lt hllt hjαt)
          (by positivity) (by positivity)
      have hgate := ann_baseRay_large_poly hlarge
      have heq : annBaseK * t / 2 * (annBaseL * t / 2) =
          annBaseK * annBaseL * t ^ 2 / 4 := by ring
      nlinarith

/-- **The `base_ray_gap` gate of the analytic package, verbatim.**

The signature is exactly the package field.  Four of its hypotheses (`_hr`,
`_htop`, `_hhalf`, `_hsint`) are not consumed by the scalar certificate — the
cut `α < k t` needs only `α ≤ π/2` together with the two physical bounds — but
they are retained so that this theorem is literally the package obligation. -/
theorem ann_base_ray_gap {r t α : ℝ} (_hr : r ∈ Icc annA annR₀) (ht0 : 0 < t)
    (_htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (_hhalf : t / 2 ≤ α) (hαtop : α ≤ Real.pi / 2) (_hsint : 0 ≤ Real.sin t)
    (hR1 : Real.sin α ≤ annR₁ * Real.sin t)
    (hheight : Real.sin α * Real.sin (α - t) ≤ annA * Real.sin t) :
    2 * α - t < annPaperG r * t := by
  have hcut := ann_alpha_lt_annBaseK_mul ht0 hαtop hR1 hheight
  have hfrozen : 2 * α - t < annFrozenRatio * t := by
    have heq : annFrozenRatio * t = 2 * (annBaseK * t) - t := by
      rw [← ann_two_annBaseK_sub_one]; ring
    linarith
  exact hfrozen.trans_le
    (mul_le_mul_of_nonneg_right (ann_frozen_le_annPaperG r) ht0.le)

/-! ## The endpoint domain and its analytic package -/

/-- **The Figure-5 endpoint domain of the annular tuple.** -/
def annFigure5Domain : Figure5EndpointDomain where
  a := annA
  r0 := annR₀
  R1 := annR₁
  g := annPaperG
  a_pos := annA_pos
  a_le_r0 := by norm_num [annA, annR₀]
  r0_lt_half := annR₀_lt_half
  R1_pos := annR₁_pos

@[simp] theorem annFigure5Domain_a : annFigure5Domain.a = annA := rfl

@[simp] theorem annFigure5Domain_r0 : annFigure5Domain.r0 = annR₀ := rfl

@[simp] theorem annFigure5Domain_R1 : annFigure5Domain.R1 = annR₁ := rfl

@[simp] theorem annFigure5Domain_g : annFigure5Domain.g = annPaperG := rfl

/-! ### Domination (A): the interior branch

`strongInteriorRatio` of the CLEAN endpoint interface and `annInteriorRatio` of
the integral module are the *same function*, so the domination is `le_max_left`. -/

theorem ann_strongInteriorRatio_eq (r : ℝ) :
    strongInteriorRatio r = annInteriorRatio r := rfl

theorem ann_strongInteriorRatio_le_annPaperG (r : ℝ) :
    strongInteriorRatio r ≤ annPaperG r := le_max_left _ _

/-! ### Domination (B): the large-angle branch -/

theorem ann_strongLargeAngleRatio_eq (r : ℝ) :
    strongLargeAngleRatio r = annLargeAngleRatio r := rfl

theorem ann_strongLargeAngleRatio_le_annPaperG (r : ℝ) :
    strongLargeAngleRatio r ≤ annPaperG r :=
  le_max_of_le_right (le_max_right _ _)

/-- **The Figure-5 endpoint analytic package of the annular tuple.**

Built through `Figure5EndpointAnalyticPackage.of_dominations`, so `one_lt_g` is
derived and only the three listed gates are paid. -/
theorem annFigure5AnalyticPackage :
    Figure5EndpointAnalyticPackage annFigure5Domain :=
  Figure5EndpointAnalyticPackage.of_dominations
    (fun {r} _ => ann_strongInteriorRatio_le_annPaperG r)
    (fun {r} _ => ann_strongLargeAngleRatio_le_annPaperG r)
    (fun {_ _ _} hr ht0 htop hhalf hαtop hsint hR1 hheight =>
      ann_base_ray_gap hr ht0 htop hhalf hαtop hsint hR1 hheight)

/-! ## The confined lower bound of the annular tuple

Unconditional on the geometry: the only hypothesis is the no-high-needle
dichotomy branch `hhigh`, which is exactly the confined case. -/

/-- **M6 endpoint/confined exit at the production tuple.** -/
theorem annular_confined_lower_bound {E : Set Plane} (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      annA ≤ (K.needleFamily theta).height K.center) :
    ENNReal.ofReal annILower * directionAngleOuter (K.A_in_radius annR₁) ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center annR₀) :=
  confined_lower_bound_of_endpointDomain K annFigure5Domain
    annFigure5AnalyticPackage hhigh ann_aemeasurable_ofReal_radial
    annILower_le_lintegral

end

end StarKakeyaLower
