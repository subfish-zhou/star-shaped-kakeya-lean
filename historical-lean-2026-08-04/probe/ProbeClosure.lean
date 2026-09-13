-- Probe: imports ONLY the historical UniversalEndpointClosure.
import StarKakeyaLower.UniversalEndpointClosure

namespace StarKakeyaLower
open Set MeasureTheory Real
noncomputable section

variable {E : Set Plane}

-- baseline statements, verbatim
example {p : ℝ} [Fact (0 < p)] {g x rad β γ : ℝ}
    (h : ((γ : ℝ) : AddCircle p) ∈ quotientCenteredDilate g p x rad) :
    ((β + γ : ℝ) : AddCircle p) ∈ quotientCenteredDilate g p (β + x) rad :=
  mem_quotientCenteredDilate_add h

example {g lo hi : ℝ} (hlt : lo < hi) (hg : 1 < g) :
    directionInterval lo hi ⊆
      quotientCenteredDilate g Real.pi ((lo + hi) / 2) ((hi - lo) / 2) :=
  directionInterval_subset_centeredDilate hlt hg

example (y : Plane) : planeNormSq (planeCoordinateEquiv y) = ‖y‖ ^ 2 :=
  planeNormSq_planeCoordinateEquiv y

example (K : StarShapedKakeya E) {d : ProjectiveDirection}
    (hd : d ∈ K.A_in_radius strongR₁) :
    (universalPositiveNeedle K d).triangle ⊆ originClosedDisk strongR₁ :=
  universalPositiveNeedle_triangle_subset_disk K hd

example {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : 0 < r := strongRadius_pos hr
example {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : r < 1 / 2 := strongRadius_lt_half hr

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    FirstArcData (universalPositiveNeedle K d).triangle r :=
  universalArcData K hhigh hr d

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : DirectionNeedleFamily r :=
  universalFamily K hhigh hr

-- the definitional unfolding of `universalFamily` is the baseline one
example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) :
    universalFamily K hhigh hr =
      directionNeedleFamilyOfRaw (universalPositiveNeedle K)
        (universalArcData K hhigh hr) := rfl

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    (universalFamily K hhigh hr).needle d = universalPositiveNeedle K d :=
  universalFamily_needle K hhigh hr d

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    selectedSupportFirstArc? r (universalPositiveNeedle K d).angle
        ((universalPositiveNeedle K d).height, (universalPositiveNeedle K d).centre) =
      some ((universalFamily K hhigh hr).firstArc d) :=
  universalFamily_selected K hhigh hr d

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (hδ : (universalPositiveNeedle K d).height = 0) :
    (((universalFamily K hhigh hr).firstCenter d : ℝ) : ProjectiveDirection) = d ∧
      (universalFamily K hhigh hr).firstRadius d = 0 :=
  universalFamily_zeroHeight K hhigh hr hδ

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (hδ : 0 < (universalPositiveNeedle K d).height) :
    0 < (universalFamily K hhigh hr).firstRadius d :=
  universalFamily_firstRadius_pos K hhigh hr hδ

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (h : (universalFamily K hhigh hr).firstRadius d = 0) :
    (universalPositiveNeedle K d).height = 0 :=
  universalFamily_height_eq_zero_of_firstRadius_eq_zero K hhigh hr h

example {A : NormalizedPolarArc} {q : PolarAngle} (h : A.carrier ⊆ {q}) :
    A.hi = A.lo :=
  NormalizedPolarArc.hi_eq_lo_of_carrier_subset_singleton h

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d₀ d : ProjectiveDirection}
    (hdB : d ∈ K.A_in_radius strongR₁)
    (hdJ : d ∈ (universalFamily K hhigh hr).JGamma
      ((universalFamily K hhigh hr).firstArcTarget d₀))
    (hd₀pos : ((universalFamily K hhigh hr).firstArc d₀).lo <
      ((universalFamily K hhigh hr).firstArc d₀).hi)
    (hδd : 0 < (universalPositiveNeedle K d).height)
    (hsat : ¬ Real.pi ≤ strongPaperG r *
      (((universalFamily K hhigh hr).firstArc d₀).hi -
        ((universalFamily K hhigh hr).firstArc d₀).lo)) :
    d ∈ quotientCenteredDilate (strongPaperG r) Real.pi
      ((universalFamily K hhigh hr).firstCenter d₀)
      ((universalFamily K hhigh hr).firstRadius d₀) :=
  universalFamily_positiveMember_mem_dilate K hhigh hr hdB hdJ hd₀pos hδd hsat

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d₀ d : ProjectiveDirection}
    (hdJ : d ∈ (universalFamily K hhigh hr).JGamma
      ((universalFamily K hhigh hr).firstArcTarget d₀))
    (hδd : (universalPositiveNeedle K d).height = 0) :
    d ∈ directionInterval ((universalFamily K hhigh hr).firstArc d₀).lo
      ((universalFamily K hhigh hr).firstArc d₀).hi :=
  universalFamily_zeroMember_mem_directionInterval K hhigh hr hdJ hδd

example (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) :
    FirstArcPointwiseHybridCriticalContainment (universalFamily K hhigh hr)
      (K.A_in_radius strongR₁) (strongPaperG r) :=
  universal_hybrid_containment K hhigh hr

-- the full historical endpoint API is reachable from this single import,
-- exactly as before M6
#check @Figure5UpperGapSource.baseRayCutoff
#check @Figure5SelectedGapGeometry.mixed
#check @Figure5LocalContactCertificate.q
#check @Figure5ActualSelectedTargetRelation.target_eq
#check @figure5LocalContactCertificate_of_actualSelected

end
end StarKakeyaLower
