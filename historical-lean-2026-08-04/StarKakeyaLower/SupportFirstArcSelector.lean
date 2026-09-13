import StarKakeyaLower.Figure5EndpointDomain
import StarKakeyaLower.LiGeometry

/-!
# The deterministic selected support first arc

This module is CLEAN: its import closure is `LiGeometry` (and the parameter-free
`Figure5EndpointDomain`), so it carries no frozen witness constant.  It holds the
optional first-arc selector of a support parameter and its rotation covariance,
both of which are entirely parameter-free.  They were moved here out of
`CaseIEndpointAnalytic` so that the Figure-5 endpoint geometry, the orientation
adapter and the universal first-arc layer can all be built without importing a
frozen kernel; `CaseIEndpointAnalytic` imports this module, so every previously
available name still resolves.
-/

open Set Real

namespace StarKakeyaLower

noncomputable section

/-! ## The selected support first arc

The endpoints are computed by the closed trace decomposition itself.  The nested
`if`s make all inadmissible (and empty-trace) cases literally `none`; in
particular no default arc is silently inserted. -/

/-- The selected first arc of the support triangle with parameter `p=(δ,c)`.
It is absent when the radius/height hypotheses fail or when the actual trace is
empty. -/
noncomputable def selectedSupportFirstArc? (r α : ℝ) (p : SupportParameter) :
    Option NormalizedPolarArc :=
  if hr : 0 < r then
    if hδ0 : 0 ≤ p.1 then
      if hδr : p.1 ≤ r then
        (supportTraceFirstArcData? (α := α) (c := p.2) hr hδ0 hδr).map
          FirstArcData.firstArc
      else none
    else none
  else none

/-- The optional selector itself is rotation covariant at positive height.  This
is the convenient graph-level form of the exact presentation theorem in
`LiGeometry`; in particular it does not assume that the selected component is
locally constant. -/
theorem selectedSupportFirstArc?_add_of_pos
    {r α δ c β : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r) :
    selectedSupportFirstArc? r (α + β) (δ, c) =
      (selectedSupportFirstArc? r α (δ, c)).map
        (NormalizedPolarArc.rotate β) := by
  rw [selectedSupportFirstArc?, selectedSupportFirstArc?, dif_pos hr,
    dif_pos hδ.le, dif_pos hδr, dif_pos hr, dif_pos hδ.le, dif_pos hδr]
  simpa only [Option.map_map, Function.comp_apply] using
    supportTraceFirstArcData?_firstArc_rotate β hr hδ hδr

end

end StarKakeyaLower
