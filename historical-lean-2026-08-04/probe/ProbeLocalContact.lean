-- Probe: imports ONLY the historical Figure5LocalContact.
import StarKakeyaLower.Figure5LocalContact

namespace StarKakeyaLower
open Set Real
noncomputable section

/-! ### `Figure5SelectedGapGeometry` is still a genuine inductive -/

#check @Figure5SelectedGapGeometry
#check @Figure5SelectedGapGeometry.rec
#check @Figure5SelectedGapGeometry.nearHalf
#check @Figure5SelectedGapGeometry.height
#check @Figure5SelectedGapGeometry.mixed
#check @Figure5SelectedGapGeometry.baseBase

-- QUALIFIED explicit term-mode pattern match on all four constructors
theorem probeGapMatch {r t δ₀ α : ℝ} {q : DirectedSupportParameter}
    {A : NormalizedPolarArc} (G : Figure5SelectedGapGeometry r t δ₀ α q A) :
    r ∈ Icc strongA strongR₀ :=
  match G with
  | Figure5SelectedGapGeometry.nearHalf hr _ _ => hr
  | Figure5SelectedGapGeometry.height hr _ _ _ _ _ => hr
  | Figure5SelectedGapGeometry.mixed hr _ _ _ _ _ _ _ _ _ _ _ => hr
  | Figure5SelectedGapGeometry.baseBase hr _ _ _ _ _ _ _ _ => hr

theorem probeGapFunMatch {r t δ₀ α : ℝ} {q : DirectedSupportParameter}
    {A : NormalizedPolarArc} :
    Figure5SelectedGapGeometry r t δ₀ α q A → r ∈ Icc strongA strongR₀
  | Figure5SelectedGapGeometry.nearHalf hr _ _ => hr
  | Figure5SelectedGapGeometry.height hr _ _ _ _ _ => hr
  | Figure5SelectedGapGeometry.mixed hr _ _ _ _ _ _ _ _ _ _ _ => hr
  | Figure5SelectedGapGeometry.baseBase hr _ _ _ _ _ _ _ _ => hr

example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometry r t δ₀ α q A) : r ∈ Icc strongA strongR₀ := by
  cases G with
  | nearHalf hr ht0 hhalf => exact hr
  | height hr hδ0 hδr ht hchart hcut => exact hr
  | mixed hr hδ0 hδr ht hhr x eb hbase hx hspan hchart hside => exact hr
  | baseBase hr ht0 htop hhalf halpha hsint hR hh raw => exact hr

example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometry r t δ₀ α q A) : r ∈ Icc strongA strongR₀ := by
  induction G with
  | nearHalf hr _ _ => exact hr
  | height hr _ _ _ _ _ => exact hr
  | mixed hr _ _ _ _ _ _ _ _ _ _ _ => exact hr
  | baseBase hr _ _ _ _ _ _ _ _ => exact hr

-- baseline constructor applications, verbatim
example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀) (ht0 : 0 < t) (hhalf : α ≤ t) :
    Figure5SelectedGapGeometry r t δ₀ α q A :=
  Figure5SelectedGapGeometry.nearHalf hr ht0 hhalf

example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀) (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : strongEndpointPhi r δ₀ ≤ t)
    (hchart : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hcut : Real.sin α ≤ δ₀ / r) :
    Figure5SelectedGapGeometry r t δ₀ α q A :=
  Figure5SelectedGapGeometry.height hr hδ0 hδr ht hchart hcut

example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀) (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : t = strongEndpointPhi r δ₀) (hhr : q.2.1 < r)
    (x eb : ℝ) (hbase : 1 / 2 ≤ eb) (hx : x = Real.arctan (q.2.1 / eb))
    (hspan : A.span = Real.arcsin (q.2.1 / r) - x)
    (hchart : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hside : Real.sin α ≤ q.2.1 / r) :
    Figure5SelectedGapGeometry r t δ₀ α q A :=
  Figure5SelectedGapGeometry.mixed hr hδ0 hδr ht hhr x eb hbase hx hspan hchart hside

example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀) (ht0 : 0 < t)
    (htop : t < Real.pi / 2 - Real.arctan (2 * r)) (hhalf : t / 2 ≤ α)
    (halpha : α ∈ Icc 0 (Real.pi / 2)) (hsint : 0 ≤ Real.sin t)
    (hR : Real.sin α ≤ strongR₁ * Real.sin t)
    (hh : Real.sin α * Real.sin (α - t) ≤ strongA * Real.sin t)
    (raw : Figure5BaseRayRawProvenance t q) :
    Figure5SelectedGapGeometry r t δ₀ α q A :=
  Figure5SelectedGapGeometry.baseBase hr ht0 htop hhalf halpha hsint hR hh raw

/-! ### The two structures: constructors and projections -/

#check @Figure5LocalContactCertificate
#check @Figure5LocalContactCertificate.mk
#check @Figure5LocalContactCertificate.q
#check @Figure5LocalContactCertificate.D
#check @Figure5LocalContactCertificate.A
#check @Figure5LocalContactCertificate.gamma
#check @Figure5LocalContactCertificate.support
#check @Figure5LocalContactCertificate.selectedLift
#check @Figure5LocalContactCertificate.gamma_direction
#check @Figure5LocalContactCertificate.upper_gap
#check @Figure5LocalContactCertificate.lower_gap
#check @Figure5LocalContactCertificate.rec

#check @Figure5ActualSelectedTargetRelation
#check @Figure5ActualSelectedTargetRelation.mk
#check @Figure5ActualSelectedTargetRelation.target_eq
#check @Figure5ActualSelectedTargetRelation.upper
#check @Figure5ActualSelectedTargetRelation.lower
#check @Figure5ActualSelectedTargetRelation.rec

-- structure eta / anonymous-constructor + projection round trip
example {r t : ℝ} {d : ProjectiveDirection}
    (C : Figure5LocalContactCertificate r t d) :
    Figure5LocalContactCertificate r t d :=
  ⟨C.q, C.D, C.A, C.gamma, C.support, C.selectedLift, C.gamma_direction,
    C.upper_gap, C.lower_gap⟩

example {r t : ℝ} {d : ProjectiveDirection}
    (C : Figure5LocalContactCertificate r t d) :
    2 * figure5UpperAnalyticAngle C.gamma t C.A - t < strongPaperG r * t :=
  C.upper_gap

example {r t δ₀ gamma : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A) :
    Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A :=
  ⟨H.target_eq, H.upper, H.lower⟩

example {r t δ₀ gamma : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A) :
    t = strongEndpointPhi r δ₀ := H.target_eq

-- qualified match on the structure constructor
theorem probeRelMatch {r t δ₀ gamma : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A) :
    t = strongEndpointPhi r δ₀ :=
  match H with
  | Figure5ActualSelectedTargetRelation.mk te _ _ => te

/-! ### Baseline theorem signatures, verbatim -/

example {r t δ₀ α : ℝ} {q : DirectedSupportParameter} {A : NormalizedPolarArc}
    (G : Figure5SelectedGapGeometry r t δ₀ α q A)
    (hheight : 0 < q.2.1) (hheightA : q.2.1 ≤ strongA)
    (hselected : Icc A.lo A.hi ⊆ Icc 0 t) :
    Figure5UpperGapSource r t δ₀ α q := G.toGapSource hheight hheightA hselected

example {r t gamma : ℝ} {A : NormalizedPolarArc}
    (ht : 0 ≤ t) (hA : Icc A.lo A.hi ⊆ Icc 0 t)
    (hu : 2 * figure5UpperAnalyticAngle gamma t A - t < strongPaperG r * t)
    (hl : 2 * figure5LowerAnalyticAngle gamma t A - t < strongPaperG r * t) :
    (gamma : ProjectiveDirection) ∈
      quotientCenteredDilate (strongPaperG r) Real.pi (t / 2) (t / 2) :=
  figure5_local_contact_pointwise ht hA hu hl

example {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A)
    (hq : Figure5PositiveNormalizedSupport r strongA strongR₁ q) :
    selectedSupportFirstArc? r (figure5UpperSupport t A q).1
        (figure5UpperSupport t A q).2 =
      some (D.firstArc.rotate (figure5UpperRotation t A)) := H.upper_selected hq

example {r t : ℝ} {q : DirectedSupportParameter}
    {D : FirstArcData (supportNeedleTriangle q.1 q.2.1 q.2.2) r}
    {A : NormalizedPolarArc}
    (H : Figure5SelectedChangedLift r t q D A)
    (hq : Figure5PositiveNormalizedSupport r strongA strongR₁ q) :
    selectedSupportFirstArc? r (figure5LowerSupport A q).1
        (figure5LowerSupport A q).2 =
      some (D.firstArc.rotate (figure5LowerRotation A)) := H.lower_selected hq

example {r t δ₀ α : ℝ} {qq : DirectedSupportParameter} {AA : NormalizedPolarArc}
    (hr : r ∈ Icc strongA strongR₀) (ht0 : 0 < t) (hup : α ≤ t) :
    Figure5SelectedGapGeometry r t δ₀ α qq AA :=
  figure5_easy_gapGeometry hr ht0 hup

example {r t δ₀ : ℝ} {q : DirectedSupportParameter}
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
      Figure5ActualSelectedTargetRelation r t δ₀ gamma q D A :=
  figure5ActualSelectedTargetRelation_of_principal hsupport hstrict hselected hr
    hδ0 hδr ht ht0 htop hsint

example {r t δ₀ : ℝ} {q : DirectedSupportParameter}
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
  figure5LocalContactCertificate_of_actualSelected hsupport hselected hstrict hr
    hδ0 hδr ht ht0 htop hsint

-- the old envelope API is still reachable transitively, as at baseline
#check @Figure5UpperGapSource.nearHalf
#check @figure5_baseRay_provenance
#check @figure5_height_le_radius_mul_sin
#check @figure5ReflectedLowerArc
#check @Figure5SelectedChangedLift.reflected_lower_lift
#check @figure5_selected_strict_presentation_endpoints_active

end
end StarKakeyaLower
