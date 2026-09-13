import StarKakeyaLower.OneTenthGlobalAssemblyClosed

/-!
# Arbitrary-set star-shaped Kakeya outer-area lower bound

The only geometric hypothesis is the original `StarShapedKakeya E`: one star
center and a unit segment in every unoriented direction. In particular `E`
need not be measurable or bounded, and no measurable needle selector, section
inequality, angular record, price record, or area receipt is assumed.
-/
open Set MeasureTheory
namespace StarKakeyaLower

/-- Every star-shaped planar Kakeya set has Lebesgue outer area at least 1/10. -/
theorem StarShapedKakeya.one_tenth_le_outerArea {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure E :=
  OneTenth.one_tenth_outer_of_open_covers E
    (fun G hEG hG => OneTenth.GlobalAssembly.open_cover_one_tenth K hEG hG)

end StarKakeyaLower
