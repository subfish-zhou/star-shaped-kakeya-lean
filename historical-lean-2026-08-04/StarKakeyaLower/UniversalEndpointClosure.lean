import StarKakeyaLower.UniversalEndpointClosureCore
import StarKakeyaLower.Figure5LocalContact

/-!
# The universal Case-I endpoint closure (frozen facade)

This is the historical module.  Importing it alone gives exactly the API it gave
before milestone M6: the quotient-interval helpers, the radius containment of
the inner class, the canonical trace data `universalArcData`, the family
`universalFamily` with its five basic lemmas, and the pointwise hybrid
containment `universal_hybrid_containment` — every one of them with its original
statement at the `100π/5599` tuple.

All of the mathematics lives in the CLEAN, parameterised
`StarKakeyaLower.UniversalEndpointClosureCore`, which this module imports and
therefore re-exports; it also re-exports the historical
`StarKakeyaLower.Figure5LocalContact` facade, so the whole pre-M6 endpoint API
is reachable from this single import as before.  Nothing is reproved here.

The two exits the milestone-M5 confined interface consumes, `endpointTraceFor`
and `endpointCriticalFor`, are generic and live in the core module.
-/

open Set MeasureTheory Real

namespace StarKakeyaLower

noncomputable section

variable {E : Set Plane}

/-! ## Radius containment of the inner class -/

theorem universalPositiveNeedle_triangle_subset_disk (K : StarShapedKakeya E)
    {d : ProjectiveDirection} (hd : d ∈ K.A_in_radius strongR₁) :
    (universalPositiveNeedle K d).triangle ⊆ originClosedDisk strongR₁ :=
  universalPositiveNeedle_triangle_subset_diskFor K hd

/-! ## The frozen Case-I radial range -/

theorem strongRadius_pos {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : 0 < r :=
  strongParameterDomain.a_pos.trans_le hr.1

theorem strongRadius_lt_half {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : r < 1 / 2 :=
  hr.2.trans_lt strongParameterDomain.r₀_lt_half

/-! ## Canonical first-arc data for the universal family

Each declaration below is the generic one at `strongFigure5Domain`. -/

def universalArcData (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    FirstArcData (universalPositiveNeedle K d).triangle r :=
  universalArcDataFor strongFigure5Domain K hhigh hr d

def universalFamily (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) : DirectionNeedleFamily r :=
  directionNeedleFamilyOfRaw (universalPositiveNeedle K)
    (universalArcData K hhigh hr)

theorem universalFamily_needle (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    (universalFamily K hhigh hr).needle d = universalPositiveNeedle K d := rfl

theorem universalFamily_selected (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) (d : ProjectiveDirection) :
    selectedSupportFirstArc? r (universalPositiveNeedle K d).angle
        ((universalPositiveNeedle K d).height, (universalPositiveNeedle K d).centre) =
      some ((universalFamily K hhigh hr).firstArc d) :=
  universalFamilyFor_selected strongFigure5Domain K hhigh hr d

theorem universalFamily_zeroHeight (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (hδ : (universalPositiveNeedle K d).height = 0) :
    (((universalFamily K hhigh hr).firstCenter d : ℝ) : ProjectiveDirection) = d ∧
      (universalFamily K hhigh hr).firstRadius d = 0 :=
  universalFamilyFor_zeroHeight strongFigure5Domain K hhigh hr hδ

theorem universalFamily_firstRadius_pos (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (hδ : 0 < (universalPositiveNeedle K d).height) :
    0 < (universalFamily K hhigh hr).firstRadius d :=
  universalFamilyFor_firstRadius_pos strongFigure5Domain K hhigh hr hδ

theorem universalFamily_height_eq_zero_of_firstRadius_eq_zero
    (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d : ProjectiveDirection}
    (h : (universalFamily K hhigh hr).firstRadius d = 0) :
    (universalPositiveNeedle K d).height = 0 :=
  universalFamilyFor_height_eq_zero_of_firstRadius_eq_zero strongFigure5Domain K
    hhigh hr h

/-! ## The positive-height and zero-height members -/

theorem universalFamily_positiveMember_mem_dilate
    (K : StarShapedKakeya E)
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
  universalFamilyFor_positiveMember_mem_dilate strongFigure5Domain
    strongFigure5AnalyticPackage K hhigh hr hdB hdJ hd₀pos hδd hsat

theorem universalFamily_zeroMember_mem_directionInterval
    (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) {d₀ d : ProjectiveDirection}
    (hdJ : d ∈ (universalFamily K hhigh hr).JGamma
      ((universalFamily K hhigh hr).firstArcTarget d₀))
    (hδd : (universalPositiveNeedle K d).height = 0) :
    d ∈ directionInterval ((universalFamily K hhigh hr).firstArc d₀).lo
      ((universalFamily K hhigh hr).firstArc d₀).hi :=
  universalFamilyFor_zeroMember_mem_directionInterval strongFigure5Domain K hhigh
    hr hdJ hδd

/-! ## The pointwise hybrid containment on the inner-radius class -/

theorem universal_hybrid_containment (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction,
      strongA ≤ (K.needleFamily theta).height K.center)
    {r : ℝ} (hr : r ∈ Icc strongA strongR₀) :
    FirstArcPointwiseHybridCriticalContainment (universalFamily K hhigh hr)
      (K.A_in_radius strongR₁) (strongPaperG r) :=
  universal_hybrid_containmentFor strongFigure5Domain
    strongFigure5AnalyticPackage K hhigh hr

end

end StarKakeyaLower
