import StarKakeyaLower.OneTenth

/-! Fresh parent import and raw-hypothesis semantic audit. -/
open Set MeasureTheory
namespace StarKakeyaLower.OneTenth.ParentAudit

/-- Unpack precisely the requested geometric contract, with no measurable or
bounded original set and no auxiliary price/section/area premises. -/
theorem raw_hypotheses {E : Set Plane} (o : Plane)
    (hstar : ∀ ⦃x⦄, x ∈ E → segment ℝ o x ⊆ E)
    (hunit : ∀ θ : Direction, ∃ n : UnitNeedle,
      n.HasDirection θ ∧ n.carrier ⊆ E) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure E := by
  exact StarShapedKakeya.one_tenth_le_outerArea
    { center := o, star := hstar, needle_exists := hunit }

#check @StarShapedKakeya.one_tenth_le_outerArea
#check @raw_hypotheses
#print Plane
#print Direction
#print UnitNeedle
#print UnitNeedle.carrier
#print UnitNeedle.HasDirection
#print StarShapedKakeya
#print axioms StarShapedKakeya.one_tenth_le_outerArea
#print axioms raw_hypotheses

end StarKakeyaLower.OneTenth.ParentAudit
