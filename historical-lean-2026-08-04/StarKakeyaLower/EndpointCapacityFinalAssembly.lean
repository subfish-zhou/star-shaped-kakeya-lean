import StarKakeyaLower.EndpointCapacityLowSchedule
import StarKakeyaLower.EndpointCapacityHighAggregate

/-!
# Final low/high radial-ledger assembly

The low interval and countably many high ledgers are radially disjoint.  This
module combines their *local integral* bounds before invoking planar layer cake,
so planar outer measure is paid exactly once.  It also closes the projective
direction cover, selected-triangle containment, height dichotomy, and final
`141/2000` arithmetic.  The conditional top-level theorem isolates the two
remaining concrete local payment inequalities.
-/

open Set MeasureTheory Real Function
open scoped ENNReal Topology BigOperators

namespace StarKakeyaLower.Witness141

noncomputable section

def selectedRadialQ {E : Set Plane} (K : StarShapedKakeya E) : ℝ → ℝ≥0∞ :=
  radialSuperlevelOuter
    (directionTriangleUnion (universalPositiveNeedle K) Set.univ)

def lowRadial : Set ℝ := Icc (b 0) (switch 32)

private def radialCell (o : Option ℕ) : Set ℝ :=
  match o with
  | none => lowRadial
  | some k => highLedger k

private def radialCode : Option ℕ → ℕ
  | none => 0
  | some k => k + 1

private theorem radialCell_measurable (o : Option ℕ) : MeasurableSet (radialCell o) := by
  cases o <;> simp [radialCell, lowRadial, highLedger]

private theorem radialCell_pairwise :
    Pairwise (fun o p : Option ℕ => Disjoint (radialCell o) (radialCell p)) := by
  intro o p hop
  cases o with
  | none =>
      cases p with
      | none => exact (hop rfl).elim
      | some k =>
          rw [Set.disjoint_left]
          intro u hu hv
          have hsep := low_high_radial_separation
          have hk0 : highB 0 ≤ highB k := by
            unfold highB highA
            norm_num
            positivity
          exact (not_lt_of_ge hv.1) (hu.2.trans_lt (hsep.trans_le hk0))
  | some k =>
      cases p with
      | none =>
          exact (by
            rw [Set.disjoint_left]
            intro u hu hv
            have hsep := low_high_radial_separation
            have hk0 : highB 0 ≤ highB k := by
              unfold highB highA
              norm_num
              positivity
            exact (not_lt_of_ge hu.1) (hv.2.trans_lt (hsep.trans_le hk0)))
      | some l =>
          exact highLedger_pairwise_disjoint (fun h => hop (by simp [h]))

private theorem radialCell_subset_interval (o : Option ℕ) :
    radialCell o ⊆ Icc (b 0) (highB (radialCode o)) := by
  cases o with
  | none =>
      intro u hu
      exact ⟨hu.1, hu.2.trans low_high_radial_separation.le⟩
  | some k =>
      intro u hu
      have hb0 : b 0 ≤ highB k := by
        have hs := low_high_radial_separation
        have hk0 : highB 0 ≤ highB k := by
          unfold highB highA
          norm_num
          positivity
        have hbSwitch : b 0 ≤ switch 32 := by
          change (13613 / 500000 : ℝ) ≤ 519371 / 1000000
          norm_num
        exact hbSwitch.trans (hs.le.trans hk0)
      exact ⟨hb0.trans hu.1, hu.2.trans (highOuterRadius_lt_next_highB k).le⟩

/-- The low schedule and all high ledgers form one disjoint radial ledger. -/
theorem lowRadial_disjoint_highRadial :
    Disjoint lowRadial (⋃ k, highLedger k) := by
  rw [Set.disjoint_left]
  intro u hu hv
  rcases mem_iUnion.1 hv with ⟨k, hk⟩
  exact Set.disjoint_left.1 (radialCell_pairwise (i := none) (j := some k) (by simp)) hu hk

/-- Crucial one-payment lemma: low plus high integrals are the integral over one
radially disjoint union, and that union costs at most the selected outer measure. -/
theorem low_add_high_lintegral_le_selectedOuter
    {E : Set Plane} (K : StarShapedKakeya E) :
    (∫⁻ u in lowRadial, ENNReal.ofReal u * (selectedRadialQ K).leftLim u) +
      (∫⁻ u in ⋃ k, highLedger k,
        ENNReal.ofReal u * (selectedRadialQ K).leftLim u) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal u * (selectedRadialQ K).leftLim u
  have hcells : (∫⁻ u in ⋃ o : Option ℕ, radialCell o, f u) =
      ∑' o : Option ℕ, ∫⁻ u in radialCell o, f u := by
    exact lintegral_iUnion radialCell_measurable radialCell_pairwise f
  have htotal : (∫⁻ u in ⋃ o : Option ℕ, radialCell o, f u) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
    rw [hcells]
    apply tsum_le_of_sum_le' bot_le
    intro s
    by_cases hs : s.Nonempty
    · let m := (s.image radialCode).max' (hs.image radialCode)
      have hsum : (∑ o ∈ s, ∫⁻ u in radialCell o, f u) =
          ∫⁻ u in ⋃ o : s, radialCell o.1, f u := by
        have hi := lintegral_iUnion
          (μ := volume) (s := fun o : s => radialCell o.1)
          (fun o => radialCell_measurable o.1)
          (fun i j hij => radialCell_pairwise (by
            intro h; apply hij; exact Subtype.ext h)) f
        rw [hi]
        simp only [tsum_fintype]
        exact (Finset.sum_attach s (fun o => ∫⁻ u in radialCell o, f u)).symm
      rw [hsum]
      calc
        (∫⁻ u in ⋃ o : s, radialCell o.1, f u) ≤
            ∫⁻ u in Icc (b 0) (highB m), f u := by
          apply lintegral_mono_set
          rintro u hu
          rcases mem_iUnion.1 hu with ⟨o, ho⟩
          have hcode : radialCode o.1 ≤ m :=
            Finset.le_max' (s.image radialCode) (radialCode o.1)
              (Finset.mem_image.2 ⟨o.1, o.2, rfl⟩)
          have hm : highB (radialCode o.1) ≤ highB m := by
            unfold highB highA
            norm_num
            have hc : ((radialCode o.1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcode
            linarith
          exact ⟨(radialCell_subset_interval o.1 ho).1,
            (radialCell_subset_interval o.1 ho).2.trans hm⟩
        _ ≤ volume.toOuterMeasure
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
          exact K.selectedTriangleUnion_leftLim_lintegral_le (b_pos 0)
    · simp at hs
      simp [hs]
  change (∫⁻ u in radialCell none, f u) +
      (∫⁻ u in ⋃ k, radialCell (some k), f u) ≤ _
  have hunion : radialCell none ∪ (⋃ k, radialCell (some k)) =
      ⋃ o : Option ℕ, radialCell o := by
    ext u
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (h | ⟨k, hk⟩)
      · exact ⟨none, h⟩
      · exact ⟨some k, hk⟩
    · rintro ⟨o, ho⟩
      cases o with
      | none => exact Or.inl ho
      | some k => exact Or.inr ⟨k, ho⟩
  calc
    _ = ∫⁻ u in radialCell none ∪ (⋃ k, radialCell (some k)), f u := by
      have hd : Disjoint (radialCell none) (⋃ k, radialCell (some k)) := by
        simpa [radialCell] using lowRadial_disjoint_highRadial
      exact (lintegral_union
        (MeasurableSet.iUnion (fun k => radialCell_measurable (some k))) hd).symm
    _ = ∫⁻ u in ⋃ o : Option ℕ, radialCell o, f u := by rw [hunion]
    _ ≤ _ := htotal

/-- Nearest-radius low and high classes cover every projective direction. -/
theorem low_high_direction_cover {E : Set Plane} (K : StarShapedKakeya E) :
    (Set.univ : Set ProjectiveDirection) ⊆
      (⋃ j : Fin 32, lowClass K j) ∪ (⋃ k : ℕ, highClass K k) := by
  intro d _hd
  by_cases hlow : (universalPositiveNeedle K d).nearestRadiusSq ≤ eta ^ 2
  · exact Or.inl (by rw [iUnion_lowClass K]; exact hlow)
  · exact Or.inr (highClasses_cover_nearestSq_gt_eta_sq K (lt_of_not_ge hlow))

/-- Combination of the two *local* bounds.  The right side is paid once: the
two local integrals are first joined along disjoint radial sets. -/
theorem common_mul_projectiveVolume_le_selectedOuter_of_local_bounds
    {E : Set Plane} (K : StarShapedKakeya E)
    (hlow :
      ENNReal.ofReal common * volume (⋃ j : Fin 32, lowClass K j) ≤
        ∫⁻ u in Icc (b 0) (switch 32),
          ENNReal.ofReal u * (selectedRadialQ K).leftLim u)
    (hhigh :
      ENNReal.ofReal common * ∑' k, volume (highClass K k) ≤
        ∫⁻ u in ⋃ k, highLedger k,
          ENNReal.ofReal u * (selectedRadialQ K).leftLim u) :
    ENNReal.ofReal common * volume (Set.univ : Set ProjectiveDirection) ≤
      volume.toOuterMeasure
        (directionTriangleUnion (universalPositiveNeedle K) Set.univ) := by
  have hmass : volume (Set.univ : Set ProjectiveDirection) ≤
      volume (⋃ j : Fin 32, lowClass K j) +
        ∑' k, volume (highClass K k) := by
    calc
      volume (Set.univ : Set ProjectiveDirection) ≤
          volume ((⋃ j : Fin 32, lowClass K j) ∪
            (⋃ k : ℕ, highClass K k)) :=
        measure_mono (low_high_direction_cover K)
      _ ≤ volume (⋃ j : Fin 32, lowClass K j) +
          volume (⋃ k : ℕ, highClass K k) := measure_union_le _ _
      _ ≤ volume (⋃ j : Fin 32, lowClass K j) +
          ∑' k, volume (highClass K k) :=
        add_le_add_right (measure_iUnion_le (fun k => highClass K k)) _
  calc
    ENNReal.ofReal common * volume (Set.univ : Set ProjectiveDirection) ≤
        ENNReal.ofReal common *
          (volume (⋃ j : Fin 32, lowClass K j) +
            ∑' k, volume (highClass K k)) := mul_le_mul_right hmass _
    _ = ENNReal.ofReal common * volume (⋃ j : Fin 32, lowClass K j) +
          ENNReal.ofReal common * ∑' k, volume (highClass K k) := mul_add _ _ _
    _ ≤ (∫⁻ u in Icc (b 0) (switch 32),
            ENNReal.ofReal u * (selectedRadialQ K).leftLim u) +
          (∫⁻ u in ⋃ k, highLedger k,
            ENNReal.ofReal u * (selectedRadialQ K).leftLim u) := add_le_add hlow hhigh
    _ ≤ _ := low_add_high_lintegral_le_selectedOuter K

/-- Conditional top-level `141/2000` theorem.  Its only unproved inputs are the
two requested concrete local payment inequalities; all aggregation, the
height dichotomy, selected-union containment, and final arithmetic are closed. -/
theorem final_141_over_2000_of_concrete_local_bounds
    (hlocal : ∀ {E : Set Plane} (K : StarShapedKakeya E),
      (∀ d, (universalPositiveNeedle K d).height < eta) →
      (ENNReal.ofReal common * volume (⋃ j : Fin 32, lowClass K j) ≤
        ∫⁻ u in Icc (b 0) (switch 32),
          ENNReal.ofReal u * (selectedRadialQ K).leftLim u) ∧
      (ENNReal.ofReal common * ∑' k, volume (highClass K k) ≤
        ∫⁻ u in ⋃ k, highLedger k,
          ENNReal.ofReal u * (selectedRadialQ K).leftLim u)) :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (141 / 2000 : ℝ) < volume.toOuterMeasure E := by
  intro E K
  rw [show (141 / 2000 : ℝ) = target by norm_num [target]]
  by_cases hheight : ∃ theta : Direction,
      eta ≤ (K.needleFamily theta).height K.center
  · have ht : ENNReal.ofReal target < ENNReal.ofReal (eta / 2) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [eta] : 0 < eta / 2)).2
        target_lt_eta_half
    exact ht.trans_le (K.high_branch_outerMeasure hheight)
  · have hposHeight : ∀ d, (universalPositiveNeedle K d).height < eta :=
      fun d => universalPositiveNeedle_height_lt_of_no_high hheight d
    rcases hlocal K hposHeight with ⟨hlow, hhigh⟩
    have hselected :=
      common_mul_projectiveVolume_le_selectedOuter_of_local_bounds K hlow hhigh
    have htoE : volume.toOuterMeasure
          (directionTriangleUnion (universalPositiveNeedle K) Set.univ) ≤
        volume.toOuterMeasure E := by
      calc
        volume.toOuterMeasure
            (directionTriangleUnion (universalPositiveNeedle K) Set.univ) ≤
          volume.toOuterMeasure (centeredCoordinate K '' E) :=
            measure_mono (universalPositiveTriangleUnion_subset K)
        _ = volume.toOuterMeasure E := outerMeasure_centeredCoordinate_image K
    exact ofReal_target_lt_common_mul_projectiveVolume.trans_le
      (hselected.trans htoE)

end
end StarKakeyaLower.Witness141
