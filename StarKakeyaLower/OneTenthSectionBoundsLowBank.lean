import StarKakeyaLower.OneTenthSectionBoundsReal
import StarKakeyaLower.OneTenthKernelIntegralsAssembly

/-! Exercised consumer: the proved actual source minorants discharge ALL
geometric inputs of the existing three-bank low integral receipt. -/
open Set MeasureTheory Real
open scoped ENNReal
namespace StarKakeyaLower.OneTenth.SectionBounds
noncomputable section
open Sources

/-- Same physical bank, real B/U addition, exact integral prices. No section
minorant or area inequality is a hypothesis of this theorem. -/
theorem low_radial_price (o : Plane) {c : ℝ → Plane} (hc : Measurable c)
    {V : Set ℝ} (hV : MeasurableSet V) (hVL : V ⊆ L o c)
    (G : Set Plane) (hG : IsOpen G) (htri : ∀ q ∈ V, triangle o c q ⊆ G)
    (hh : ∀ q ∈ V, |farHeight o c q| ≤ 1/5) :
    ENNReal.ofReal (lowCoefficient*(mass V).toReal) ≤
      radialBank (centeredCoordinateEnvelope o G) (Ioo 0 (1/5 : ℝ)) +
      radialBank (centeredCoordinateEnvelope o G) (Ico (1/5 : ℝ) (7/20)) +
      radialBank (centeredCoordinateEnvelope o G) (Ico (7/20 : ℝ) (1/2)) := by
  apply KernelIntegrals.low_price_le_radialBanks
    (isOpen_centeredCoordinateEnvelope o hG).measurableSet
    (mass (V ∩ B o c)).toReal (mass (V \ B o c)).toReal (mass V).toReal
    (mass_split_real o hc hV (fun q hq => (hVL hq).1))
  · intro r hr
    exact low_section_real o hc hV hVL G htri hh hr.1 (by linarith [hr.2])
  · intro r hr
    exact mid_section_real o hc hV hVL G htri hh hr.1.le hr.2
  · intro r hr
    exact outer_section_real o hc hV hVL G htri hh (by linarith [hr.1]) (by linarith [hr.2])

end
end StarKakeyaLower.OneTenth.SectionBounds
