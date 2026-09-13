import StarKakeyaLower.Figure5EndpointEnvelope
import StarKakeyaLower.Figure5LocalContactCore

/-!
# Figure 5 local-contact endpoint comparison (frozen facade)

This is the historical module.  Importing it alone gives exactly the API it gave
before milestone M6, with the original kinds: the genuine
`inductive Figure5SelectedGapGeometry` with its four constructors, the genuine
structures `Figure5LocalContactCertificate` and
`Figure5ActualSelectedTargetRelation` with their constructors and projections,
and every theorem with its original statement.

The mathematics lives in the CLEAN, parameterised
`StarKakeyaLower.Figure5LocalContactCore`, which this module imports and
therefore re-exports.  Nothing is reproved here: each declaration below either
relabels constructors between the frozen and the generic datatype, or delegates
to the corresponding `...For` theorem at `strongFigure5Domain`.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-! ## The frozen selected-endpoint classification -/

/-- Source-free geometric classification of one normalized selected endpoint.
`mixed` is the new selected-longest closure: it stores the actual selected span,
not a preassembled height cutoff.  `baseBase` is the only constructor carrying
the two constraints used by the frozen single-ray estimate. -/
inductive Figure5SelectedGapGeometry (r t δ₀ α : ℝ)
    (q : DirectedSupportParameter) (A : NormalizedPolarArc) : Prop where
  | nearHalf
      (hr : r ∈ Icc strongA strongR₀)
      (ht0 : 0 < t) (hhalf : α ≤ t) :
      Figure5SelectedGapGeometry r t δ₀ α q A
  | height
      (hr : r ∈ Icc strongA strongR₀)
      (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
      (ht : strongEndpointPhi r δ₀ ≤ t)
      (alpha_chart : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
      (height_cutoff : Real.sin α ≤ δ₀ / r) :
      Figure5SelectedGapGeometry r t δ₀ α q A
  | mixed
      (hr : r ∈ Icc strongA strongR₀)
      (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
      (ht : t = strongEndpointPhi r δ₀)
      (height_lt_radius : q.2.1 < r)
      (x effectiveBase : ℝ) (base_ge_half : 1 / 2 ≤ effectiveBase)
      (base_angle : x = Real.arctan (q.2.1 / effectiveBase))
      (selected_span : A.span = Real.arcsin (q.2.1 / r) - x)
      (alpha_chart : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
      (side_sin : Real.sin α ≤ q.2.1 / r) :
      Figure5SelectedGapGeometry r t δ₀ α q A
  | baseBase
      (hr : r ∈ Icc strongA strongR₀)
      (ht0 : 0 < t)
      (htop : t < Real.pi / 2 - Real.arctan (2 * r))
      (hhalf : t / 2 ≤ α)
      (halpha : α ∈ Icc 0 (Real.pi / 2))
      (hsint : 0 ≤ Real.sin t)
      (radius_constraint : Real.sin α ≤ strongR₁ * Real.sin t)
      (height_constraint : Real.sin α * Real.sin (α - t) ≤
        strongA * Real.sin t)
      (raw : Figure5BaseRayRawProvenance t q) :
      Figure5SelectedGapGeometry r t δ₀ α q A

/-- The frozen classification is the generic one at `strongFigure5Domain`.
Both directions are pure constructor relabelling. -/
theorem Figure5SelectedGapGeometry.toFor
    {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometry r t δ₀ α q A) :
    Figure5SelectedGapGeometryFor strongFigure5Domain r t δ₀ α q A := by
  cases G with
  | nearHalf hr ht0 hhalf =>
      exact Figure5SelectedGapGeometryFor.nearHalf hr ht0 hhalf
  | height hr hδ0 hδr ht hchart hcut =>
      exact Figure5SelectedGapGeometryFor.height hr hδ0 hδr ht hchart hcut
  | mixed hr hδ0 hδr ht hhr x eb hbase hx hspan hchart hside =>
      exact Figure5SelectedGapGeometryFor.mixed hr hδ0 hδr ht hhr x eb hbase hx
        hspan hchart hside
  | baseBase hr ht0 htop hhalf halpha hsint hR hh raw =>
      exact Figure5SelectedGapGeometryFor.baseBase hr ht0 htop hhalf halpha
        hsint hR hh raw

theorem Figure5SelectedGapGeometryFor.toStrong
    {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometryFor strongFigure5Domain r t δ₀ α q A) :
    Figure5SelectedGapGeometry r t δ₀ α q A := by
  cases G with
  | nearHalf hr ht0 hhalf =>
      exact Figure5SelectedGapGeometry.nearHalf hr ht0 hhalf
  | height hr hδ0 hδr ht hchart hcut =>
      exact Figure5SelectedGapGeometry.height hr hδ0 hδr ht hchart hcut
  | mixed hr hδ0 hδr ht hhr x eb hbase hx hspan hchart hside =>
      exact Figure5SelectedGapGeometry.mixed hr hδ0 hδr ht hhr x eb hbase hx
        hspan hchart hside
  | baseBase hr ht0 htop hhalf halpha hsint hR hh raw =>
      exact Figure5SelectedGapGeometry.baseBase hr ht0 htop hhalf halpha hsint
        hR hh raw

/-- Endpoint activity plus selected-longest span comparison automatically
produces the analytic source sum.  No source is retained by the caller. -/
theorem Figure5SelectedGapGeometry.toGapSource
    {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometry r t δ₀ α q A)
    (hheight : 0 < q.2.1) (hheightA : q.2.1 ≤ strongA)
    (hselected : Icc A.lo A.hi ⊆ Icc 0 t) :
    Figure5UpperGapSource r t δ₀ α q :=
  (Figure5SelectedGapGeometryFor.toGapSource G.toFor hheight hheightA
    hselected).toStrong

/-! ## The frozen certificate and target relation -/

/-- A local certificate for one chosen direction.  It records only a normalized
support, its selected arc/lift, and the two endpoint classifications after the
explicit normalizations above. -/
structure Figure5LocalContactCertificate (r t : ℝ)
    (d : ProjectiveDirection) where
  q : DirectedSupportParameter
  D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r
  A : NormalizedPolarArc
  gamma : ℝ
  support : Figure5PositiveNormalizedSupport r strongA strongR₁ q
  selectedLift : Figure5SelectedChangedLift r t q D A
  gamma_direction : (gamma : ProjectiveDirection) = d
  upper_gap : 2 * figure5UpperAnalyticAngle gamma t A - t < strongPaperG r * t
  lower_gap : 2 * figure5LowerAnalyticAngle gamma t A - t < strongPaperG r * t

/-- Target-height relation for the actual selected component, expressed using
an orientation-aware analytic lift.  Both endpoints are read in the honest
rotated support charts, so that the base-ray provenance stored by the base
branch is a genuine statement about the physical needle endpoints. -/
structure Figure5ActualSelectedTargetRelation
    (r t δ₀ gamma : ℝ) (q : DirectedSupportParameter)
    (D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r)
    (A : NormalizedPolarArc) : Prop where
  target_eq : t = strongEndpointPhi r δ₀
  upper : Figure5SelectedGapGeometry r t δ₀
    (figure5UpperAnalyticAngle gamma t A)
    (figure5UpperSupport t A q)
    (A.rotate (figure5UpperRotation t A))
  lower : Figure5SelectedGapGeometry r t δ₀
    (figure5LowerAnalyticAngle gamma t A)
    (figure5LowerSupport A q)
    (figure5ReflectedLowerArc t A)

/-- The frozen target relation is the generic one at `strongFigure5Domain`. -/
theorem Figure5ActualSelectedTargetRelation.toFor
    {r t δ₀ gamma : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A) :
    Figure5ActualSelectedTargetRelationFor strongFigure5Domain r t δ₀ gamma q D A where
  target_eq := H.target_eq
  upper := H.upper.toFor
  lower := H.lower.toFor

theorem Figure5ActualSelectedTargetRelationFor.toStrong
    {r t δ₀ gamma : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5ActualSelectedTargetRelationFor strongFigure5Domain r t δ₀ gamma
      q D A) :
    Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A where
  target_eq := H.target_eq
  upper := H.upper.toStrong
  lower := H.lower.toStrong

/-- The frozen local certificate is the generic one at `strongFigure5Domain`. -/
def Figure5LocalContactCertificateFor.toStrong {r t : ℝ}
    {d : ProjectiveDirection}
    (C : Figure5LocalContactCertificateFor strongFigure5Domain r t d) :
    Figure5LocalContactCertificate r t d where
  q := C.q
  D := C.D
  A := C.A
  gamma := C.gamma
  support := C.support
  selectedLift := C.selectedLift
  gamma_direction := C.gamma_direction
  upper_gap := C.upper_gap
  lower_gap := C.lower_gap

def Figure5LocalContactCertificate.toFor {r t : ℝ} {d : ProjectiveDirection}
    (C : Figure5LocalContactCertificate r t d) :
    Figure5LocalContactCertificateFor strongFigure5Domain r t d where
  q := C.q
  D := C.D
  A := C.A
  gamma := C.gamma
  support := C.support
  selectedLift := C.selectedLift
  gamma_direction := C.gamma_direction
  upper_gap := C.upper_gap
  lower_gap := C.lower_gap

/-! ## The frozen specializations of the generalized theorems

Each statement below is identical to its pre-M6 form; the corresponding generic
theorem carries a `...For` suffix in `Figure5LocalContactCore`. -/

theorem Figure5SelectedChangedLift.upper_selected
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A)
    (hq : Figure5PositiveNormalizedSupport r strongA strongR₁ q) :
    selectedSupportFirstArc? r (figure5UpperSupport t A q).1
        (figure5UpperSupport t A q).2 =
      some (D.firstArc.rotate (figure5UpperRotation t A)) :=
  H.upper_selectedFor hq

theorem Figure5SelectedChangedLift.lower_selected
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A)
    (hq : Figure5PositiveNormalizedSupport r strongA strongR₁ q) :
    selectedSupportFirstArc? r (figure5LowerSupport A q).1
        (figure5LowerSupport A q).2 =
      some (D.firstArc.rotate (figure5LowerRotation A)) :=
  H.lower_selectedFor hq

theorem figure5_local_contact_pointwise
    {r t gamma : ℝ} {A : NormalizedPolarArc}
    (_ht : 0 ≤ t) (hA : Icc A.lo A.hi ⊆ Icc 0 t)
    (hu : 2 * figure5UpperAnalyticAngle gamma t A - t < strongPaperG r * t)
    (hl : 2 * figure5LowerAnalyticAngle gamma t A - t < strongPaperG r * t) :
    (gamma : ProjectiveDirection) ∈
      quotientCenteredDilate (strongPaperG r) Real.pi (t / 2) (t / 2) :=
  figure5_local_contact_pointwiseFor _ht hA hu hl

theorem figure5_selected_strict_presentation_endpoints_active
    {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q)
    (hheight_strict : q.2.1 < r)
    (hselected : Figure5SelectedChangedLift r t q D A) :
    (D.firstArc =
        (principalTraceShiftedClosedPolarPresentations
          (a := q.2.2 - 1 / 2) (b := q.2.2 + 1 / 2) q.1
          hsupport.height_pos
          (div_nonneg hsupport.height_pos.le hsupport.radius_pos.le)
          ((div_lt_one hsupport.radius_pos).2 hheight_strict)).1.arc.getD D.firstArc ∧
      principalTraceLeftPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2) (q.2.1 / r) =
        Icc (D.firstArc.lo - q.1) (D.firstArc.hi - q.1) ∧
      ∀ lo hi : ℝ, lo ≤ hi →
        Icc lo hi ⊆ principalTraceRightPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2)
          (q.2.1 / r) → hi - lo ≤ D.firstArc.hi - D.firstArc.lo) ∨
    (D.firstArc =
        (principalTraceShiftedClosedPolarPresentations
          (a := q.2.2 - 1 / 2) (b := q.2.2 + 1 / 2) q.1
          hsupport.height_pos
          (div_nonneg hsupport.height_pos.le hsupport.radius_pos.le)
          ((div_lt_one hsupport.radius_pos).2 hheight_strict)).2.arc.getD D.firstArc ∧
      principalTraceRightPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2) (q.2.1 / r) =
        Icc (D.firstArc.lo - q.1) (D.firstArc.hi - q.1) ∧
      ∀ lo hi : ℝ, lo ≤ hi →
        Icc lo hi ⊆ principalTraceLeftPiece q.2.1 (q.2.2 - 1 / 2) (q.2.2 + 1 / 2)
          (q.2.1 / r) → hi - lo ≤ D.firstArc.hi - D.firstArc.lo) :=
  figure5_selected_strict_presentation_endpoints_activeFor hsupport
    hheight_strict hselected

/-! ## The frozen branch constructors and the assembly -/

theorem figure5_easy_gapGeometry
    {r t δ₀ α : ℝ} {qq : DirectedSupportParameter} {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀)
    (ht0 : 0 < t) (hup : α ≤ t) :
    Figure5SelectedGapGeometry r t δ₀ α qq AA :=
  (figure5_easy_gapGeometryFor (P := strongFigure5Domain) hr ht0 hup).toStrong

theorem figure5_hard_mixed_gapGeometry
    {r t δ₀ h base spanA α : ℝ} {qq : DirectedSupportParameter}
    {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀) (ht0 : 0 ≤ t) (hrpos : 0 < r)
    (hh0 : 0 < h) (hhr : h < r) (hbase : 1 / 2 ≤ base)
    (hspan : spanA = Real.arcsin (h / r) - Real.arctan (h / base))
    (hspant : spanA ≤ t) (hα : α = t + Real.arctan (h / base)) :
    Figure5SelectedGapGeometry r t δ₀ α qq AA :=
  (figure5_hard_mixed_gapGeometryFor (P := strongFigure5Domain) hr hδ0 hδr ht ht0
    hrpos hh0 hhr hbase hspan hspant hα).toStrong

theorem figure5_hard_baseBase_gapGeometry
    {r t δ₀ ψ₁ ψ₂ : ℝ} {qq : DirectedSupportParameter} {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀)
    (ht0 : 0 < t) (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hsint : 0 ≤ Real.sin t)
    (hh0 : 0 < qq.2.1) (hhA : qq.2.1 ≤ strongA)
    (hψ₁ : 0 ≤ ψ₁) (hle : ψ₁ ≤ ψ₂) (hψ₂ : ψ₂ ≤ Real.pi / 2)
    (hS : ψ₂ - ψ₁ ≤ t) (htψ : t + ψ₁ ≤ Real.pi / 2)
    (hchord : Real.sin ψ₁ * Real.sin ψ₂ = qq.2.1 * Real.sin (ψ₂ - ψ₁))
    (hnorm : qq.2.1 ≤ strongR₁ * Real.sin ψ₁)
    (hraw : Figure5BaseRayRawProvenance t qq) :
    Figure5SelectedGapGeometry r t δ₀ (t + ψ₁) qq AA :=
  (figure5_hard_baseBase_gapGeometryFor (P := strongFigure5Domain) hr ht0 htop
    hsint hh0 hhA hψ₁ hle hψ₂ hS htψ hchord hnorm hraw).toStrong

theorem figure5ActualSelectedTargetRelation_of_principal
    {r t δ₀ : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q)
    (hstrict : q.2.1 < r)
    (hselected : Figure5SelectedChangedLift r t q D A)
    (hr : r ∈ Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀)
    (ht0 : 0 < t) (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hsint : 0 ≤ Real.sin t) :
    ∃ gamma : ℝ, (gamma : ProjectiveDirection) = (q.1 : ProjectiveDirection) ∧
      Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A := by
  obtain ⟨gamma, hdir, hrel⟩ :=
    figure5ActualSelectedTargetRelationFor_of_principal strongFigure5Domain
      hsupport hstrict hselected hr hδ0 hδr ht ht0 htop hsint
  exact ⟨gamma, hdir, hrel.toStrong⟩

noncomputable def figure5LocalContactCertificate_of_actualSelected
    {r t δ₀ : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (hsupport : Figure5PositiveNormalizedSupport r strongA strongR₁ q)
    (hselected : Figure5SelectedChangedLift r t q D A)
    (hstrict : q.2.1 < r)
    (hr : r ∈ Icc strongA strongR₀)
    (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀)
    (ht0 : 0 < t) (htop : t < Real.pi / 2 - Real.arctan (2 * r))
    (hsint : 0 ≤ Real.sin t) :
    Figure5LocalContactCertificate r t (q.1 : ProjectiveDirection) :=
  (figure5LocalContactCertificateFor_of_actualSelected strongFigure5AnalyticPackage
    hsupport hselected hstrict hr hδ0 hδr ht ht0 htop hsint).toStrong

end

end StarKakeyaLower
