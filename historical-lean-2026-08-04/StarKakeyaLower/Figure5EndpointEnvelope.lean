import StarKakeyaLower.Figure5FrozenPackage

/-!
# Figure 5: base endpoints and the upper-gap source (frozen facade)

This is the historical module.  Importing it alone gives exactly the API it gave
before milestone M6: the base endpoints `figure5BaseMinus` / `figure5BasePlus`,
the raw provenance structure, the one-chord identity, the mixed-span comparison,
and the genuine `inductive Figure5UpperGapSource` with its three constructors
and `gap_lt` — all re-exported or re-declared with their original statements.

The mathematics has moved to the CLEAN, parameterised
`StarKakeyaLower.Figure5EndpointEnvelopeCore`, which this module imports (via
`Figure5FrozenPackage`) and therefore re-exports.  The only content here is the
original inductive at the `100π/5599` tuple together with the two conversions
`Figure5UpperGapSource.toFor` / `Figure5UpperGapSourceFor.toStrong`, which
identify it with `Figure5UpperGapSourceFor strongFigure5Domain`.  `gap_lt` is
the generic theorem transported along that identification; no branch estimate is
reproved.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-- Branch-specific Figure-5 source.  The constructors contain only contact
geometry and scalar normalization.  In particular the desired gap is not an
input.  The base constructor keeps the two physical endpoints, their radial
parameters and bounds, the chord-height identity, and the two inequalities
consumed by `base_ray_frozen_analytic`. -/
inductive Figure5UpperGapSource
    (r t δ₀ αmax : ℝ) (q : DirectedSupportParameter) : Prop where
  /-- If the analytic lift does not exceed the far end of the target chart, the
  desired gap is immediate from `1 < g`. -/
  | nearHalf
      (hr : r ∈ Icc strongA strongR₀)
      (ht0 : 0 < t) (hhalf : αmax ≤ t) :
      Figure5UpperGapSource r t δ₀ αmax q
  | heightCutoff
      (hr : r ∈ Icc strongA strongR₀)
      (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
      (ht : strongEndpointPhi r δ₀ ≤ t)
      (halpha : αmax ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
      (height_cutoff : Real.sin αmax ≤ δ₀ / r) :
      Figure5UpperGapSource r t δ₀ αmax q
  | baseRayCutoff
      (hr : r ∈ Icc strongA strongR₀)
      (ht0 : 0 < t)
      (htop : t < Real.pi / 2 - Real.arctan (2 * r))
      (hhalf : t / 2 ≤ αmax)
      (halpha : αmax ∈ Icc 0 (Real.pi / 2))
      (hsint : 0 ≤ Real.sin t)
      (radius_constraint : Real.sin αmax ≤ strongR₁ * Real.sin t)
      (height_constraint : Real.sin αmax * Real.sin (αmax - t) ≤
        strongA * Real.sin t)
      (raw : Figure5BaseRayRawProvenance t q) :
      Figure5UpperGapSource r t δ₀ αmax q

/-- The frozen source is the generic source at `strongFigure5Domain`.  Both
directions are pure constructor relabelling. -/
theorem Figure5UpperGapSource.toFor
    {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) :
    Figure5UpperGapSourceFor strongFigure5Domain r t δ₀ αmax q := by
  cases H with
  | nearHalf hr ht0 hhalf =>
      exact Figure5UpperGapSourceFor.nearHalf hr ht0 hhalf
  | heightCutoff hr hδ0 hδr ht halpha hcut =>
      exact Figure5UpperGapSourceFor.heightCutoff hr hδ0 hδr ht halpha hcut
  | baseRayCutoff hr ht0 htop hhalf halpha hsint hR hheight raw =>
      exact Figure5UpperGapSourceFor.baseRayCutoff hr ht0 htop hhalf halpha
        hsint hR hheight raw

theorem Figure5UpperGapSourceFor.toStrong
    {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSourceFor strongFigure5Domain r t δ₀ αmax q) :
    Figure5UpperGapSource r t δ₀ αmax q := by
  cases H with
  | nearHalf hr ht0 hhalf =>
      exact Figure5UpperGapSource.nearHalf hr ht0 hhalf
  | heightCutoff hr hδ0 hδr ht halpha hcut =>
      exact Figure5UpperGapSource.heightCutoff hr hδ0 hδr ht halpha hcut
  | baseRayCutoff hr ht0 htop hhalf halpha hsint hR hheight raw =>
      exact Figure5UpperGapSource.baseRayCutoff hr ht0 htop hhalf halpha hsint
        hR hheight raw

/-- The analytic assembly of the two genuine endpoint branches. -/
theorem Figure5UpperGapSource.gap_lt
    {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) :
    2 * αmax - t < strongPaperG r * t :=
  Figure5UpperGapSourceFor.gap_lt strongFigure5AnalyticPackage H.toFor

end

end StarKakeyaLower
