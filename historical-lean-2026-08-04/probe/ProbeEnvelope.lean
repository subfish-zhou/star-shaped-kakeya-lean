-- Probe: imports ONLY the historical Figure5EndpointEnvelope.
import StarKakeyaLower.Figure5EndpointEnvelope

namespace StarKakeyaLower
open Set Real
noncomputable section

-- 1. the old name is a genuine inductive (recursor exists)
#check @Figure5UpperGapSource
#check @Figure5UpperGapSource.rec
#check @Figure5UpperGapSource.nearHalf
#check @Figure5UpperGapSource.heightCutoff
#check @Figure5UpperGapSource.baseRayCutoff

-- 2. QUALIFIED explicit term-mode pattern matching on every constructor
theorem probeQualifiedMatch {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) :
    r ∈ Icc strongA strongR₀ :=
  match H with
  | Figure5UpperGapSource.nearHalf hr _ _ => hr
  | Figure5UpperGapSource.heightCutoff hr _ _ _ _ _ => hr
  | Figure5UpperGapSource.baseRayCutoff hr _ _ _ _ _ _ _ _ => hr

-- 2b. qualified `fun` pattern match (anonymous constructor elimination)
theorem probeQualifiedFunMatch {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter} :
    Figure5UpperGapSource r t δ₀ αmax q → r ∈ Icc strongA strongR₀
  | Figure5UpperGapSource.nearHalf hr _ _ => hr
  | Figure5UpperGapSource.heightCutoff hr _ _ _ _ _ => hr
  | Figure5UpperGapSource.baseRayCutoff hr _ _ _ _ _ _ _ _ => hr

-- 3. qualified `cases ... with` naming every constructor
example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) : r ∈ Icc strongA strongR₀ := by
  cases H with
  | nearHalf hr ht0 hhalf => exact hr
  | heightCutoff hr hδ0 hδr ht halpha hcut => exact hr
  | baseRayCutoff hr ht0 htop hhalf halpha hsint hR hh raw => exact hr

-- 3b. `induction ... with` (uses the recursor directly)
example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) : r ∈ Icc strongA strongR₀ := by
  induction H with
  | nearHalf hr _ _ => exact hr
  | heightCutoff hr _ _ _ _ _ => exact hr
  | baseRayCutoff hr _ _ _ _ _ _ _ _ => exact hr

-- 4. `rcases` with fully qualified patterns
example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) : r ∈ Icc strongA strongR₀ := by
  rcases H with ⟨hr, ht0, hhalf⟩ | ⟨hr, hδ0, hδr, ht, ha, hc⟩ |
    ⟨hr, ht0, htop, hhalf, ha, hs, hR, hh, raw⟩ <;> exact hr

-- 5. baseline theorem signature, verbatim
example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (H : Figure5UpperGapSource r t δ₀ αmax q) :
    2 * αmax - t < strongPaperG r * t := H.gap_lt

-- 6. baseline constructor application, verbatim argument shape
example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (hr : r ∈ Icc strongA strongR₀) (ht0 : 0 < t) (hhalf : αmax ≤ t) :
    Figure5UpperGapSource r t δ₀ αmax q := .nearHalf hr ht0 hhalf

example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (hr : r ∈ Icc strongA strongR₀) (hδ0 : 0 < δ₀) (hδr : δ₀ < r)
    (ht : strongEndpointPhi r δ₀ ≤ t)
    (halpha : αmax ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hcut : Real.sin αmax ≤ δ₀ / r) :
    Figure5UpperGapSource r t δ₀ αmax q :=
  Figure5UpperGapSource.heightCutoff hr hδ0 hδr ht halpha hcut

example {r t δ₀ αmax : ℝ} {q : DirectedSupportParameter}
    (hr : r ∈ Icc strongA strongR₀) (ht0 : 0 < t)
    (htop : t < Real.pi / 2 - Real.arctan (2 * r)) (hhalf : t / 2 ≤ αmax)
    (halpha : αmax ∈ Icc 0 (Real.pi / 2)) (hsint : 0 ≤ Real.sin t)
    (hR : Real.sin αmax ≤ strongR₁ * Real.sin t)
    (hh : Real.sin αmax * Real.sin (αmax - t) ≤ strongA * Real.sin t)
    (raw : Figure5BaseRayRawProvenance t q) :
    Figure5UpperGapSource r t δ₀ αmax q :=
  Figure5UpperGapSource.baseRayCutoff hr ht0 htop hhalf halpha hsint hR hh raw

-- 7. the other baseline names of this module
#check @figure5BaseMinus
#check @figure5BasePlus
#check @Figure5BaseRayRawProvenance
#check @Figure5BaseRayRawProvenance.mk
#check @Figure5BaseRayRawProvenance.thetaPlus
#check @figure5_single_ray_chord_identity
#check @strongEndpointPhi_le_of_mixedSpan

end
end StarKakeyaLower
