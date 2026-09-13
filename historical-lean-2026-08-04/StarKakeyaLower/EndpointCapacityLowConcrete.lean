import StarKakeyaLower.EndpointCapacityLowSchedule

open Set MeasureTheory Real Function
open scoped ENNReal BigOperators Interval

namespace StarKakeyaLower.Witness141
noncomputable section

private def selectedQ {E : Set Plane} (K : StarShapedKakeya E) : ℝ → ℝ≥0∞ :=
  radialSuperlevelOuter
    (directionTriangleUnion (universalPositiveNeedle K) Set.univ)

/-- 32 head pieces followed by the 31 shared switch pieces. -/
abbrev LowRow := Fin 32 ⊕ Fin 31

def lowRowLo : LowRow → ℝ
  | .inl m => b m
  | .inr q => switch ⟨q.1 + 1, by omega⟩

def lowRowHi : LowRow → ℝ
  | .inl m => if h : m.1 < 31 then b ⟨m.1 + 1, by omega⟩ else switch 1
  | .inr q => switch ⟨q.1 + 2, by omega⟩

def lowRowWindow : LowRow → Fin 32
  | .inl _ => 0
  | .inr q => ⟨q.1 + 1, by omega⟩

def lowRowAtoms : LowRow → Finset ℕ
  | .inl m => Finset.range (m.1 + 1)
  | .inr q => (Finset.range 32).filter (fun j => q.1 + 1 ≤ j)

private theorem lowRowAtoms_sub (k : LowRow) : lowRowAtoms k ⊆ Finset.range 32 := by
  intro j hj
  rcases k with m | q
  · simp only [lowRowAtoms, Finset.mem_range] at hj ⊢
    omega
  · exact (Finset.mem_filter.1 hj).1

private theorem b_mono : Monotone b := b_strictMono.monotone

private theorem classLower_nonneg (j : Fin 32) : 0 ≤ classLower j := by
  by_cases hj : j.1 = 0
  · simp [classLower, hj]
  · simp [classLower, hj, (b_pos ⟨j.1 - 1, by omega⟩).le]

private theorem classLower_mono : Monotone classLower := by
  intro i j hij
  by_cases hi : i.1 = 0
  · have hei : i = 0 := Fin.ext hi
    subst i
    simpa [classLower] using classLower_nonneg j
  · have hj : j.1 ≠ 0 := by omega
    simp only [classLower, hi, hj, ↓reduceDIte]
    apply b_mono
    exact Fin.mk_le_mk.mpr (by omega)

set_option maxHeartbeats 800000 in
-- Exhaustively checks the frozen endpoint bounds for all 63 concrete rows.
private theorem lowRow_bounds (k : LowRow) :
    0 < lowRowLo k ∧ lowRowLo k ≤ lowRowHi k ∧
      lowRowHi k ≤ outerRadius (lowRowWindow k) := by
  rcases k with m | q
  · fin_cases m <;> norm_num [lowRowLo, lowRowHi, lowRowWindow, b, switch, outerRadius]
  · fin_cases q <;> norm_num [lowRowLo, lowRowHi, lowRowWindow, switch, outerRadius]

private theorem eta_le_switch_succ (q : Fin 31) :
    eta ≤ switch ⟨q.1 + 1, by omega⟩ := by
  fin_cases q <;> norm_num [eta, switch]

private theorem lowRowAtoms_eligible {E : Set Plane} (K : StarShapedKakeya E)
    (k : LowRow) {r : ℝ} (hr : r ∈ Ioc (lowRowLo k) (lowRowHi k)) :
    (⋃ j ∈ lowRowAtoms k, lowAtom K j) ⊆ lowEligible K (lowRowWindow k) r := by
  intro theta htheta
  simp only [mem_iUnion] at htheta
  obtain ⟨j, hjS, hjtheta⟩ := htheta
  have hj32 := Finset.mem_range.1 (lowRowAtoms_sub k hjS)
  rw [lowEligible]
  apply mem_iUnion.2
  refine ⟨⟨j, hj32⟩, ?_⟩
  apply mem_iUnion.2
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rcases k with m | q
      · have hjle : j ≤ m.1 := by simpa [lowRowAtoms] using hjS
        have hb : b ⟨j, hj32⟩ ≤ b m := b_mono (Fin.mk_le_mk.mpr hjle)
        exact hb.trans hr.1.le
      · exact (b_le_eta ⟨j, hj32⟩).trans ((eta_le_switch_succ q).trans hr.1.le)
    · rcases k with m | q
      · simp only [lowRowWindow]
        norm_num [outerRadius]
        exact sq_nonneg (classLower ⟨j, hj32⟩)
      · have hij : (⟨q.1 + 1, by omega⟩ : Fin 32) ≤ (⟨j, hj32⟩ : Fin 32) :=
          Fin.mk_le_mk.mpr (Finset.mem_filter.1 hjS).2
        calc
          outerRadius ⟨q.1 + 1, by omega⟩ ^ 2
              ≤ 1 / 4 + classLower ⟨q.1 + 1, by omega⟩ ^ 2 :=
            outerRadius_sq_le_quarter_add_classLower_sq _
          _ ≤ 1 / 4 + classLower ⟨j, hj32⟩ ^ 2 := by
            have hm := classLower_mono hij
            have h0 := classLower_nonneg (⟨q.1 + 1, by omega⟩ : Fin 32)
            nlinarith
          _ = classLower ⟨j, hj32⟩ ^ 2 + 1 / 4 := by ring
  · simpa [lowAtom, hj32] using hjtheta

private theorem lowRow_integrand {E : Set Plane} (K : StarShapedKakeya E)
    (k : LowRow) {r : ℝ} (hr : r ∈ Ioc (lowRowLo k) (lowRowHi k))
    (hstrict : r < outerRadius (lowRowWindow k)) :
    ENNReal.ofReal (endpointWindowKernel (outerRadius (lowRowWindow k)) r) *
        volume (⋃ j ∈ lowRowAtoms k, lowAtom K j) ≤
      ENNReal.ofReal r * (selectedQ K).leftLim r := by
  have hb := lowRow_bounds k
  have hr0 : 0 < r := hb.1.trans hr.1
  have hw := lowEligible_fixedWindow_leftLim K (lowRowWindow k) r hr0 hstrict
  have hsub := measure_mono (μ := volume) (lowRowAtoms_eligible K k hr)
  have hker : endpointWindowKernel (outerRadius (lowRowWindow k)) r =
      r * ((outerRadius (lowRowWindow k) - r) /
        (outerRadius (lowRowWindow k) + r)) := by
    unfold endpointWindowKernel
    ring
  change _ ≤ ENNReal.ofReal r *
    (radialSuperlevelOuter _).leftLim r
  calc
    _ = ENNReal.ofReal r *
        (ENNReal.ofReal ((outerRadius (lowRowWindow k) - r) /
          (outerRadius (lowRowWindow k) + r)) *
          volume (⋃ j ∈ lowRowAtoms k, lowAtom K j)) := by
      rw [hker, ENNReal.ofReal_mul hr0.le]
      ring
    _ ≤ ENNReal.ofReal r *
        (ENNReal.ofReal ((outerRadius (lowRowWindow k) - r) /
          (outerRadius (lowRowWindow k) + r)) * volume (lowEligible K (lowRowWindow k) r)) :=
      mul_le_mul_right (mul_le_mul_right hsub _) _
    _ ≤ _ := mul_le_mul_right hw _

private theorem lowRow_payment_nonneg (k : LowRow) :
    0 ≤ endpointWindowPayment (outerRadius (lowRowWindow k)) (lowRowLo k) (lowRowHi k) := by
  have hb := lowRow_bounds k
  rw [← intervalIntegral_endpointWindowKernel (by linarith [hb.1]) hb.1.le
    (hb.1.le.trans hb.2.1)]
  apply intervalIntegral.integral_nonneg hb.2.1
  intro r hr
  unfold endpointWindowKernel
  have hr0 : 0 ≤ r := hb.1.le.trans hr.1
  have hrR : r ≤ outerRadius (lowRowWindow k) := hr.2.trans hb.2.2
  exact div_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hrR))
    (add_nonneg (hr0.trans hrR) hr0)

def lowRowWeight (k : LowRow) : NNReal :=
  ⟨endpointWindowPayment (outerRadius (lowRowWindow k)) (lowRowLo k) (lowRowHi k),
    lowRow_payment_nonneg k⟩

private theorem lowRow_local {E : Set Plane} (K : StarShapedKakeya E) (k : LowRow) :
    (lowRowWeight k : ENNReal) * volume (⋃ j ∈ lowRowAtoms k, lowAtom K j) ≤
      ∫⁻ r in Ioc (lowRowLo k) (lowRowHi k),
        ENNReal.ofReal r * (selectedQ K).leftLim r := by
  have hb := lowRow_bounds k
  have hcont : ContinuousOn (endpointWindowKernel (outerRadius (lowRowWindow k)))
      (Icc (lowRowLo k) (lowRowHi k)) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    have hden : outerRadius (lowRowWindow k) + r ≠ 0 := by
      apply ne_of_gt
      nlinarith [hb.1, hr.1]
    unfold endpointWindowKernel
    fun_prop (disch := assumption)
  have hnonneg : ∀ᵐ r ∂volume.restrict (Icc (lowRowLo k) (lowRowHi k)),
      0 ≤ endpointWindowKernel (outerRadius (lowRowWindow k)) r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    unfold endpointWindowKernel
    have hr0 : 0 ≤ r := hb.1.le.trans hr.1
    have hrR : r ≤ outerRadius (lowRowWindow k) := hr.2.trans hb.2.2
    exact div_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hrR))
      (add_nonneg (hr0.trans hrR) hr0)
  have hconvert :
      ENNReal.ofReal (endpointWindowPayment (outerRadius (lowRowWindow k))
        (lowRowLo k) (lowRowHi k)) =
      ∫⁻ r in Ioc (lowRowLo k) (lowRowHi k),
        ENNReal.ofReal (endpointWindowKernel (outerRadius (lowRowWindow k)) r) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    · rw [← intervalIntegral.integral_of_le hb.2.1,
        intervalIntegral_endpointWindowKernel (by linarith [hb.1]) hb.1.le
          (hb.1.le.trans hb.2.1)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      unfold endpointWindowKernel
      have hr0 : 0 ≤ r := hb.1.le.trans hr.1.le
      have hrR : r ≤ outerRadius (lowRowWindow k) := hr.2.trans hb.2.2
      exact div_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hrR))
        (add_nonneg (hr0.trans hrR) hr0)
  rw [show (lowRowWeight k : ENNReal) = ENNReal.ofReal (lowRowWeight k : ℝ) by simp]
  change ENNReal.ofReal (endpointWindowPayment (outerRadius (lowRowWindow k))
    (lowRowLo k) (lowRowHi k)) * _ ≤ _
  rw [hconvert]
  rw [← lintegral_mul_const
    (μ := volume.restrict (Ioc (lowRowLo k) (lowRowHi k)))
    (volume (⋃ j ∈ lowRowAtoms k, lowAtom K j))]
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases hs : r < outerRadius (lowRowWindow k)
    · exact lowRow_integrand K k hr hs
    · have heq : r = outerRadius (lowRowWindow k) :=
        le_antisymm (hr.2.trans (lowRow_bounds k).2.2) (le_of_not_gt hs)
      simp [endpointWindowKernel, heq]
  · unfold endpointWindowKernel
    fun_prop

private def lowRowIndex : LowRow → ℕ
  | .inl m => m.1
  | .inr q => q.1 + 32

private theorem lowRowIndex_injective : Function.Injective lowRowIndex := by
  intro k l h
  rcases k with k | k <;> rcases l with l | l
  · congr
    exact Fin.ext (by simpa [lowRowIndex] using h)
  · simp [lowRowIndex] at h
    omega
  · simp [lowRowIndex] at h
    omega
  · congr
    exact Fin.ext (by simpa [lowRowIndex] using h)

private theorem switch_strictMono : StrictMono switch := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [switch, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  case «1» =>
    change (169921 / 500000 : ℝ) < 344933 / 1000000
    norm_num

private theorem switch_one_le_succ (q : Fin 31) :
    switch 1 ≤ switch ⟨q.1 + 1, by omega⟩ :=
  switch_strictMono.monotone (Fin.mk_le_mk.mpr
    (Nat.succ_le_succ (Nat.zero_le q.1)))

private theorem switch_le_last (i : Fin 33) : switch i ≤ switch 32 :=
  switch_strictMono.monotone (Fin.mk_le_mk.mpr (Nat.le_of_lt_succ i.isLt))

private theorem lowRowHi_le_lowRowLo_of_index_lt {k l : LowRow}
    (hkl : lowRowIndex k < lowRowIndex l) : lowRowHi k ≤ lowRowLo l := by
  rcases k with k | k <;> rcases l with l | l
  · simp only [lowRowIndex] at hkl
    simp only [lowRowHi, lowRowLo]
    split
    · exact b_mono (Fin.mk_le_mk.mpr (by omega))
    · omega
  · simp only [lowRowIndex] at hkl
    simp only [lowRowHi, lowRowLo]
    split
    · exact (b_le_eta _).trans (by
        have hη : eta < switch 1 := by norm_num [eta, switch]
        exact hη.le.trans (switch_one_le_succ l))
    · exact switch_one_le_succ l
  · simp only [lowRowIndex] at hkl
    omega
  · simp only [lowRowIndex] at hkl
    exact switch_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))

private theorem lowRow_intervals_pairwiseDisjoint :
    (Set.univ : Set LowRow).PairwiseDisjoint
      (fun k => Ioc (lowRowLo k) (lowRowHi k)) := by
  intro k _ l _ hkl
  change Disjoint (Ioc (lowRowLo k) (lowRowHi k))
    (Ioc (lowRowLo l) (lowRowHi l))
  rw [Set.disjoint_left]
  intro r hrk hrl
  have hidx : lowRowIndex k ≠ lowRowIndex l := fun h =>
    hkl (lowRowIndex_injective h)
  rcases lt_or_gt_of_ne hidx with h | h
  · exact (not_lt_of_ge (hrk.2.trans (lowRowHi_le_lowRowLo_of_index_lt h))) hrl.1
  · exact (not_lt_of_ge (hrl.2.trans (lowRowHi_le_lowRowLo_of_index_lt h))) hrk.1

private theorem iUnion_lowRow_intervals_subset :
    (⋃ k : LowRow, Ioc (lowRowLo k) (lowRowHi k)) ⊆
      Icc (b 0) (switch 32) := by
  intro r hr
  simp only [mem_iUnion] at hr
  obtain ⟨k, hr⟩ := hr
  constructor
  · rcases k with k | k
    · exact (b_mono (Fin.zero_le k)).trans hr.1.le
    · exact (b_le_eta 0).trans (((by norm_num [eta, switch] : eta ≤ switch 1).trans
        (switch_one_le_succ k)).trans hr.1.le)
  · rcases k with k | k
    · simp only [lowRowHi] at hr
      split at hr
      · exact hr.2.trans ((b_le_eta _).trans
          ((by norm_num [eta, switch] : eta ≤ switch 1).trans
            (switch_le_last 1)))
      · exact hr.2.trans (switch_le_last 1)
    · exact hr.2.trans (switch_le_last ⟨k.1 + 2, by omega⟩)

private theorem lowRows_weighted_le_lintegral {E : Set Plane}
    (K : StarShapedKakeya E) :
    ∑ k : LowRow, (lowRowWeight k : ENNReal) *
        volume (⋃ j ∈ lowRowAtoms k, lowAtom K j) ≤
      ∫⁻ r in Icc (b 0) (switch 32),
        ENNReal.ofReal r * (selectedQ K).leftLim r := by
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal r * (selectedQ K).leftLim r
  calc
    _ ≤ ∑ k : LowRow, ∫⁻ r in Ioc (lowRowLo k) (lowRowHi k), f r := by
      apply Finset.sum_le_sum
      intro k _
      exact lowRow_local K k
    _ = ∫⁻ r in ⋃ k : LowRow, Ioc (lowRowLo k) (lowRowHi k), f r := by
      rw [MeasureTheory.lintegral_iUnion]
      · rw [tsum_fintype]
      · exact fun k => measurableSet_Ioc
      · intro k l hkl
        exact lowRow_intervals_pairwiseDisjoint (Set.mem_univ k) (Set.mem_univ l) hkl
    _ ≤ ∫⁻ r in Icc (b 0) (switch 32), f r := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
      rw [← MeasureTheory.lintegral_indicator
        (MeasurableSet.iUnion (fun k => measurableSet_Ioc))]
      apply MeasureTheory.lintegral_mono
      intro r
      by_cases hr : r ∈ ⋃ k : LowRow, Ioc (lowRowLo k) (lowRowHi k)
      · simp [hr, iUnion_lowRow_intervals_subset hr]
      · simp [hr]

private theorem endpointWindowPayment_add {R x y z : ℝ}
    (hRx : R + x ≠ 0) (hRy : R + y ≠ 0) (hRz : R + z ≠ 0) :
    endpointWindowPayment R x y + endpointWindowPayment R y z =
      endpointWindowPayment R x z := by
  unfold endpointWindowPayment
  rw [Real.log_div hRy hRx, Real.log_div hRz hRy, Real.log_div hRz hRx]
  ring

private def lowHeadPiece (m : ℕ) : ℝ :=
  if hm : m < 32 then
    endpointWindowPayment (outerRadius 0) (b ⟨m, hm⟩)
      (if hlast : m < 31 then b ⟨m + 1, by omega⟩ else switch 1)
  else 0

/-- The head rows telescope from any cut `n` to the common endpoint `switch 1`.
The downward induction is structural; in particular, no enumeration of the 32
possible cuts is involved. -/
private theorem lowHead_filtered_telescope (n : ℕ) (hn : n < 32) :
    ∑ m ∈ Finset.Icc n 31, lowHeadPiece m =
      endpointWindowPayment (outerRadius 0) (b ⟨n, hn⟩) (switch 1) := by
  apply Nat.decreasingInduction (n := 31) (motive := fun k _ =>
    ∑ m ∈ Finset.Icc k 31, lowHeadPiece m =
      endpointWindowPayment (outerRadius 0) (b ⟨k, by omega⟩) (switch 1))
  · intro k hk ih
    have hk32 : k < 32 := by omega
    have hsets : Finset.Icc k 31 = insert k (Finset.Icc (k + 1) 31) := by
      ext m
      simp
      omega
    rw [hsets, Finset.sum_insert]
    · rw [ih]
      rw [lowHeadPiece, dif_pos hk32, dif_pos hk]
      apply endpointWindowPayment_add <;> apply ne_of_gt
      · exact add_pos (by norm_num [outerRadius]) (b_pos _)
      · exact add_pos (by norm_num [outerRadius]) (b_pos _)
      · exact add_pos (by norm_num [outerRadius]) (by norm_num [switch])
    · simp
  · simp [lowHeadPiece]
  · omega

private theorem lowHead_filtered_eq (j : Fin 32) :
    (∑ m : Fin 32, if j.1 ∈ lowRowAtoms (.inl m) then
        (lowRowWeight (.inl m) : ℝ) else 0) = lowHeadPayment j := by
  rw [← Finset.sum_filter]
  calc
    _ = ∑ m ∈ Finset.Icc j.1 31, lowHeadPiece m := by
      apply Finset.sum_bij (fun m _ => m.1)
      · intro m hm
        simp only [Finset.mem_Icc]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        simp [lowRowAtoms] at hm
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        apply Fin.ext
        exact heq
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        refine ⟨⟨m, by omega⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, lowRowAtoms,
          Finset.mem_range]
        exact Nat.lt_succ_of_le hm.1
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        change endpointWindowPayment (outerRadius 0) (b m)
          (if h : m.1 < 31 then b ⟨m.1 + 1, by omega⟩ else switch 1) =
            lowHeadPiece m.1
        simp [lowHeadPiece, m.2]
    _ = _ := lowHead_filtered_telescope j.1 j.2

/-- Reindexing the shared rows by `i=q+1` gives exactly the shared part in
`lowPayment`. -/
private theorem lowShared_filtered_eq (j : Fin 32) :
    (∑ q : Fin 31, if j.1 ∈ lowRowAtoms (.inr q) then
        (lowRowWeight (.inr q) : ℝ) else 0) =
      ∑ i : Fin 32, if 1 ≤ i.1 ∧ i.1 ≤ j.1 then lowSegmentPayment i else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun q _ => (⟨q.1 + 1, by omega⟩ : Fin 32))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    simp [lowRowAtoms] at hq
    omega
  · intro q₁ hq₁ q₂ hq₂ heq
    exact Fin.ext (by simpa using Fin.ext_iff.1 heq)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨i.1 - 1, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
    simp [lowRowAtoms]
    omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    change endpointWindowPayment (outerRadius ⟨q.1 + 1, by omega⟩)
        (switch ⟨q.1 + 1, by omega⟩) (switch ⟨q.1 + 2, by omega⟩) =
      lowSegmentPayment ⟨q.1 + 1, by omega⟩
    simp only [lowSegmentPayment]

private theorem lowRow_cover_eq (j : Fin 32) :
    (∑ k ∈ (Finset.univ : Finset LowRow).filter
      (fun k => j.1 ∈ lowRowAtoms k), (lowRowWeight k : ℝ)) = lowPayment j := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, lowHead_filtered_eq,
    lowShared_filtered_eq]
  rfl

private theorem lowRow_cover (j : ℕ) (hj : j ∈ Finset.range 32) :
    commonNN ≤ ∑ k ∈ (Finset.univ : Finset LowRow).filter
      (fun k => j ∈ lowRowAtoms k), lowRowWeight k := by
  let jf : Fin 32 := ⟨j, Finset.mem_range.1 hj⟩
  have h : common ≤ ∑ k ∈ (Finset.univ : Finset LowRow).filter
      (fun k => j ∈ lowRowAtoms k), (lowRowWeight k : ℝ) := by
    rw [show j = jf.1 by rfl, lowRow_cover_eq jf]
    exact (common_lt_lowPayment jf).le
  exact_mod_cast h

/-- Fully concrete low ledger: the 63 radial rows have no remaining schedule
parameters or analytic hypotheses. -/
theorem common_mul_lowUnion_le_lintegral {E : Set Plane}
    (K : StarShapedKakeya E) :
    ENNReal.ofReal common * volume (⋃ j : Fin 32, lowClass K j) ≤
      ∫⁻ r in Icc (b 0) (switch 32), ENNReal.ofReal r *
        (radialSuperlevelOuter
          (directionTriangleUnion (universalPositiveNeedle K) Set.univ)).leftLim r := by
  rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num [common])]
  exact finiteLowLedger_to_lintegral K Finset.univ lowRowAtoms lowRowWeight commonNN
    (fun k _ => lowRowAtoms_sub k) lowRow_cover (lowRows_weighted_le_lintegral K)

end
end StarKakeyaLower.Witness141
