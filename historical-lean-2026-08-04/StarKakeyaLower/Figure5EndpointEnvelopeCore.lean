import StarKakeyaLower.Figure5EndpointDomain
import StarKakeyaLower.LiGeometry

/-!
# Figure 5 core: base endpoints and the parameterised upper-gap source

The Figure-5 base endpoints are the genuine endpoints of the unit support
segment of a directed support parameter.  This file proves the one-chord
identity they satisfy, the mixed-span comparison against the canonical first
contact span, and the analytic `g`-gap estimate for the three literal active
constraints at the selected upper target contact
(`Figure5UpperGapSourceFor`).

This module is CLEAN and parameterised by `Figure5EndpointDomain`.  The historical
`StarKakeyaLower.Figure5EndpointEnvelope` is a thin frozen facade over it: it
declares the original `Figure5UpperGapSource` inductive at the `100π/5599`
tuple, maps it into `Figure5UpperGapSourceFor`, and re-exports every name below
through its import.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- The physical Figure-5 base endpoints.  They are the actual endpoints of
`q`'s unit support segment, not auxiliary scalar points. -/
def figure5BaseMinus (q : DirectedSupportParameter) : CoordinatePlane :=
  supportPoint q.1 q.2.1 (q.2.2 - 1 / 2)

def figure5BasePlus (q : DirectedSupportParameter) : CoordinatePlane :=
  supportPoint q.1 q.2.1 (q.2.2 + 1 / 2)

/-- Raw provenance for a base contact.  Unlike the former `baseRayCutoff`
constructor this does not require the physical endpoints to lie on the two ends
of the target chart.  It records their honest polar coordinates; the active
endpoint is determined later from the selected actual component. -/
structure Figure5BaseRayRawProvenance (t : ℝ)
    (q : DirectedSupportParameter) where
  thetaPlus : ℝ
  thetaMinus : ℝ
  rhoPlus : ℝ
  rhoMinus : ℝ
  thetaPlus_mem : thetaPlus ∈ Icc 0 t
  thetaMinus_mem : thetaMinus ∈ Icc 0 t
  rhoPlus_nonneg : 0 ≤ rhoPlus
  rhoMinus_nonneg : 0 ≤ rhoMinus
  plus_polar : figure5BasePlus q =
    scaleCoordinatePlane rhoPlus (unitDirection thetaPlus)
  minus_polar : figure5BaseMinus q =
    scaleCoordinatePlane rhoMinus (unitDirection thetaMinus)

/-- The old two-chart-end formula is a general one-chord identity.  Neither
polar angle has to be `0` or `t`. -/
theorem figure5_single_ray_chord_identity
    {q : DirectedSupportParameter} {thetaPlus thetaMinus rhoPlus rhoMinus : ℝ}
    (hplus : figure5BasePlus q =
      scaleCoordinatePlane rhoPlus (unitDirection thetaPlus))
    (hminus : figure5BaseMinus q =
      scaleCoordinatePlane rhoMinus (unitDirection thetaMinus)) :
    Real.sin (q.1 - thetaPlus) * Real.sin (q.1 - thetaMinus) =
      q.2.1 * Real.sin (thetaMinus - thetaPlus) := by
  have hsub := supportNeedle_endpoint_sub q.1 q.2.1 q.2.2
  have hx := congrArg Prod.fst hsub
  have hy := congrArg Prod.snd hsub
  simp only [figure5BasePlus, figure5BaseMinus] at hplus hminus
  rw [hplus, hminus] at hx hy
  simp [subCoordinatePlane, scaleCoordinatePlane, unitDirection] at hx hy
  have hnormal := supportPoint_dot_normal q.1 q.2.1 (q.2.2 + 1 / 2)
  rw [hplus] at hnormal
  simp [planeDot, scaleCoordinatePlane, unitDirection, unitNormal] at hnormal
  have hone : rhoPlus * Real.sin (q.1 - thetaPlus) = -q.2.1 := by
    rw [Real.sin_sub]
    nlinarith
  have htwo : Real.sin (q.1 - thetaMinus) =
      -(rhoPlus * Real.sin (thetaMinus - thetaPlus)) := by
    rw [Real.sin_sub, Real.sin_sub]
    rw [← hx, ← hy]
    ring
  rw [htwo]
  calc
    Real.sin (q.1 - thetaPlus) *
        -(rhoPlus * Real.sin (thetaMinus - thetaPlus)) =
      -(rhoPlus * Real.sin (q.1 - thetaPlus)) *
        Real.sin (thetaMinus - thetaPlus) := by ring
    _ = q.2.1 * Real.sin (thetaMinus - thetaPlus) := by rw [hone]; ring

/-! ### The parameterised upper gap source

`Figure5UpperGapSourceFor P` is the branch-specific Figure-5 source over an
arbitrary clean endpoint domain.  The constructors contain only contact geometry
and scalar normalization; in particular the desired gap is not an input.  The
base constructor keeps the two physical endpoints, their radial parameters and
bounds, the chord-height identity, and the two inequalities consumed by the
package's `base_ray_gap` gate. -/
inductive Figure5UpperGapSourceFor (P : Figure5EndpointDomain)
    (r t δ₀ αmax : ℝ) (q : DirectedSupportParameter) : Prop where
  /-- If the analytic lift does not exceed the far end of the target chart, the
  desired gap is immediate from `1 < g`. -/
  | nearHalf
      (hr : r ∈ Icc P.a P.r0)
      (ht0 : 0 < t) (hhalf : αmax ≤ t) :
      Figure5UpperGapSourceFor P r t δ₀ αmax q
  | heightCutoff
      (hr : r ∈ Icc P.a P.r0)
      (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
      (ht : strongEndpointPhi r δ₀ ≤ t)
      (halpha : αmax ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
      (height_cutoff : Real.sin αmax ≤ δ₀ / r) :
      Figure5UpperGapSourceFor P r t δ₀ αmax q
  | baseRayCutoff
      (hr : r ∈ Icc P.a P.r0)
      (ht0 : 0 < t)
      (htop : t < Real.pi / 2 - Real.arctan (2 * r))
      (hhalf : t / 2 ≤ αmax)
      (halpha : αmax ∈ Icc 0 (Real.pi / 2))
      (hsint : 0 ≤ Real.sin t)
      (radius_constraint : Real.sin αmax ≤ P.R1 * Real.sin t)
      (height_constraint : Real.sin αmax * Real.sin (αmax - t) ≤
        P.a * Real.sin t)
      (raw : Figure5BaseRayRawProvenance t q) :
      Figure5UpperGapSourceFor P r t δ₀ αmax q

/-- The analytic assembly of the three genuine endpoint branches.  Every
tuple-specific step is routed through the analytic package: `one_lt_g` for the
near branch, `interior_le_g` for the height branch and `base_ray_gap` for the
base-ray branch. -/
theorem Figure5UpperGapSourceFor.gap_lt {P : Figure5EndpointDomain}
    (HP : Figure5EndpointAnalyticPackage P)
    {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSourceFor P r t δ₀ αmax q) :
    2 * αmax - t < P.g r * t := by
  cases H with
  | nearHalf hr ht0 hhalf =>
      have hg : 1 < P.g r := HP.one_lt_g hr
      have hleft : 2 * αmax - t ≤ t := by linarith
      have hright : t < P.g r * t := by nlinarith
      exact hleft.trans_lt hright
  | heightCutoff hr hδ0 hδr ht halpha hcut =>
      have hr0 : 0 < r := Figure5EndpointDomain.radius_pos hr
      have hrhalf : r < 1 / 2 := Figure5EndpointDomain.radius_lt_half hr
      have hαle : αmax ≤ Real.arcsin (δ₀ / r) := by
        have h := Real.arcsin_le_arcsin hcut
        rw [Real.arcsin_sin halpha.1 halpha.2] at h
        exact h
      have hcontact := interior_contact_strict_gap hr0 hrhalf hδ0 hδr rfl
        (t := strongEndpointPhi r δ₀) rfl
      have ht₀pos : 0 < strongEndpointPhi r δ₀ := by
        have hx0 : 0 < δ₀ / r := div_pos hδ0 hr0
        have hx1 : δ₀ / r < 1 := (div_lt_one hr0).2 hδr
        have hasin : δ₀ / r < Real.arcsin (δ₀ / r) :=
          self_lt_arcsin_of_pos_of_lt_one hx0 hx1
        have hatan : Real.arctan (2 * δ₀) < 2 * δ₀ :=
          arctan_lt_self_of_pos (by positivity)
        have hscale : 2 * δ₀ < δ₀ / r := by
          rw [lt_div_iff₀ hr0]
          nlinarith
        rw [strongEndpointPhi]
        linarith
      have hratio0 : 0 < strongInteriorRatio r :=
        strongInteriorRatio_pos hr0.le hrhalf
      have hstep : 2 * αmax - t < strongInteriorRatio r * t := by
        have hmono : strongInteriorRatio r * strongEndpointPhi r δ₀ ≤
            strongInteriorRatio r * t :=
          mul_le_mul_of_nonneg_left ht hratio0.le
        linarith
      exact hstep.trans_le (mul_le_mul_of_nonneg_right
        (HP.interior_le_g hr) (by linarith))
  | baseRayCutoff hr ht0 htop hhalf halpha hsint hR hheight _raw =>
      exact HP.base_ray_gap hr ht0 htop hhalf halpha.2 hsint hR hheight

end

end StarKakeyaLower
