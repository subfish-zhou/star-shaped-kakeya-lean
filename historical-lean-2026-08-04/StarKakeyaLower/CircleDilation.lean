import Mathlib

/-!
# A line-component kernel for dilation of arcs

The eventual Kakeya application lives on a quotient circle.  This file proves
the measure-theoretic core after lifting the open arcs to real intervals and
choosing the disjoint open components of their union.

The input interval family may be arbitrary.  Only the disjoint component
family is required to be countable, as it is for open subsets of the line (and
of the circle).  This file has no quotient-circle assumptions; the completed
cut/lift, saturation, and Haar-measure adapter is implemented in
`QuotientCircle`.  The abstract real-line component theorem below remains the
measure-theoretic kernel used there.
-/

open Set MeasureTheory

namespace StarKakeyaLower

noncomputable section

/-- The open real interval with centre `x` and radius `r`. -/
def centeredInterval (x r : ℝ) : Set ℝ := Ioo (x - r) (x + r)

/-- Same-centre dilation of an open real interval. -/
def centeredDilate (c x r : ℝ) : Set ℝ := centeredInterval x (c * r)

/-- Dilation by `c` of the component `(a,b)`, about its midpoint. -/
def componentDilate (c a b : ℝ) : Set ℝ :=
  centeredInterval ((a + b) / 2) (c * (b - a) / 2)

/--
Abstract countable-component dilation lemma for an arbitrary family of sets.

The measure is evaluated on the possibly nonmeasurable dilated union using its
underlying outer measure.  Measurability is required only for the disjoint
original components, where countable additivity is used.
-/
theorem measure_iUnion_le_mul_of_disjoint_components
    {α ι κ : Type*} [MeasurableSpace α] [Countable κ]
    (μ : Measure α) (C : ENNReal)
    (base dilated : ι → Set α)
    (component enlargedComponent : κ → Set α)
    (owner : ι → κ)
    (hdilated : ∀ i, dilated i ⊆ enlargedComponent (owner i))
    (hdisjoint : _root_.Pairwise (fun i j => Disjoint (component i) (component j)))
    (hmeasurable : ∀ j, MeasurableSet (component j))
    (henlarged : ∀ j, μ (enlargedComponent j) ≤ C * μ (component j))
    (hcomponents : (⋃ i, base i) = ⋃ j, component j) :
    μ (⋃ i, dilated i) ≤ C * μ (⋃ i, base i) := by
  have hcover : (⋃ i, dilated i) ⊆ ⋃ j, enlargedComponent j := by
    intro y hy
    rw [mem_iUnion] at hy ⊢
    obtain ⟨i, hi⟩ := hy
    exact ⟨owner i, hdilated i hi⟩
  calc
    μ (⋃ i, dilated i)
        ≤ μ (⋃ j, enlargedComponent j) := measure_mono hcover
    _ ≤ ∑' j, μ (enlargedComponent j) := measure_iUnion_le _
    _ ≤ ∑' j, C * μ (component j) := ENNReal.tsum_le_tsum henlarged
    _ = C * ∑' j, μ (component j) := ENNReal.tsum_mul_left
    _ = C * μ (⋃ j, component j) := by
      rw [measure_iUnion hdisjoint hmeasurable]
    _ = C * μ (⋃ i, base i) := by rw [hcomponents]

theorem centeredDilate_subset_componentDilate
    {c x r a b : ℝ} (hc : 1 ≤ c) (hr : 0 ≤ r)
    (hsub : centeredInterval x r ⊆ Ioo a b) :
    centeredDilate c x r ⊆ componentDilate c a b := by
  rcases hr.eq_or_lt with hr0 | hrpos
  · subst r
    simp [centeredDilate, centeredInterval]
  have hend : a ≤ x - r ∧ x + r ≤ b := by
    exact (Ioo_subset_Ioo_iff (by linarith : x - r < x + r)).mp hsub
  have hu : 0 ≤ x - r - a := by linarith [hend.1]
  have hv : 0 ≤ b - x - r := by linarith [hend.2]
  have hc0 : 0 ≤ c - 1 := by linarith
  have hc1 : 0 ≤ c + 1 := by linarith
  have hlu : 0 ≤ (c + 1) * (x - r - a) := mul_nonneg hc1 hu
  have hlv : 0 ≤ (c - 1) * (b - x - r) := mul_nonneg hc0 hv
  have hru : 0 ≤ (c - 1) * (x - r - a) := mul_nonneg hc0 hu
  have hrv : 0 ≤ (c + 1) * (b - x - r) := mul_nonneg hc1 hv
  apply Ioo_subset_Ioo
  · dsimp [centeredDilate, componentDilate, centeredInterval]
    nlinarith [hlu, hlv]
  · dsimp [centeredDilate, componentDilate, centeredInterval]
    nlinarith [hru, hrv]

theorem volume_componentDilate
    {c a b : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) :
    volume (componentDilate c a b) =
      ENNReal.ofReal c * volume (Ioo a b) := by
  rw [componentDilate, centeredInterval, Real.volume_Ioo, Real.volume_Ioo]
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  ring

/--
Countable open-component form of the same-centre dilation inequality.

`hcomponents` says that the original union is exactly a disjoint union of open
real intervals, and `owner i` names a component containing interval `i`.
This is the reusable line kernel needed after a circle lift.  No finiteness of
the total length is assumed.
-/
theorem volume_iUnion_centeredDilate_le
    {ι κ : Type*} [Countable κ]
    (c : ℝ) (hc : 1 ≤ c)
    (x r : ι → ℝ) (a b : κ → ℝ) (owner : ι → κ)
    (hr : ∀ i, 0 ≤ r i)
    (hab : ∀ j, a j < b j)
    (howner : ∀ i, centeredInterval (x i) (r i) ⊆ Ioo (a (owner i)) (b (owner i)))
    (hdisjoint : _root_.Pairwise
      (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hcomponents : (⋃ i, centeredInterval (x i) (r i)) = ⋃ j, Ioo (a j) (b j)) :
    volume (⋃ i, centeredDilate c (x i) (r i)) ≤
      ENNReal.ofReal c * volume (⋃ i, centeredInterval (x i) (r i)) := by
  apply measure_iUnion_le_mul_of_disjoint_components
      volume (ENNReal.ofReal c)
      (fun i => centeredInterval (x i) (r i))
      (fun i => centeredDilate c (x i) (r i))
      (fun j => Ioo (a j) (b j))
      (fun j => componentDilate c (a j) (b j)) owner
  · intro i
    exact centeredDilate_subset_componentDilate hc (hr i) (howner i)
  · exact hdisjoint
  · exact fun _ => measurableSet_Ioo
  · intro j
    exact le_of_eq
      (volume_componentDilate (show 0 ≤ c by linarith) (hab j).le)
  · exact hcomponents

/-! ### Open subsets of the line

Mathlib has the order-connected-component construction, but currently no
packaged theorem saying that a bounded open subset of `ℝ` is a countable
disjoint union of its endpoint intervals.  The following lemmas provide that
independent topological kernel. -/

abbrev OpenComponentIndex (U : Set ℝ) := U.ordConnectedSection

def openComponent (U : Set ℝ) (j : OpenComponentIndex U) : Set ℝ :=
  U.ordConnectedComponent (j : ℝ)

theorem openComponent_nonempty {U : Set ℝ} (j : OpenComponentIndex U) :
    (openComponent U j).Nonempty := by
  exact Set.nonempty_ordConnectedComponent.mpr
    (Set.ordConnectedSection_subset j.property)

theorem openComponent_subset {U : Set ℝ} (j : OpenComponentIndex U) :
    openComponent U j ⊆ U :=
  Set.ordConnectedComponent_subset

theorem isOpen_openComponent {U : Set ℝ} (hU : IsOpen U)
    (j : OpenComponentIndex U) : IsOpen (openComponent U j) := by
  have hjU : (j : ℝ) ∈ U := Set.ordConnectedSection_subset j.property
  have heq : openComponent U j = connectedComponentIn U (j : ℝ) := by
    apply Set.Subset.antisymm
    · exact IsPreconnected.subset_connectedComponentIn
        Set.instOrdConnectedOrdConnectedComponent.isPreconnected
        (Set.self_mem_ordConnectedComponent.mpr hjU)
        Set.ordConnectedComponent_subset
    · intro y hy
      change y ∈ U.ordConnectedComponent (j : ℝ)
      rw [Set.mem_ordConnectedComponent]
      exact isPreconnected_connectedComponentIn.ordConnected.uIcc_subset
        (mem_connectedComponentIn hjU) hy |>.trans
          (connectedComponentIn_subset U (j : ℝ))
  rw [heq]
  exact hU.connectedComponentIn

noncomputable def openComponentRational (U : Set ℝ) (hU : IsOpen U)
    (j : OpenComponentIndex U) : ℚ :=
  Classical.choose (by
    obtain ⟨a, b, hab, hsub⟩ :=
      (isOpen_openComponent hU j).exists_Ioo_subset (openComponent_nonempty j)
    obtain ⟨q, hq⟩ := exists_rat_btwn hab
    exact ⟨q, hsub hq⟩ : ∃ q : ℚ, (q : ℝ) ∈ openComponent U j)

-- The verbose witness proof is kept separate so later users need not unfold the choice.
theorem openComponentRational_mem (U : Set ℝ) (hU : IsOpen U)
    (j : OpenComponentIndex U) :
    (openComponentRational U hU j : ℝ) ∈ openComponent U j := by
  exact Classical.choose_spec (by
    obtain ⟨a, b, hab, hsub⟩ :=
      (isOpen_openComponent hU j).exists_Ioo_subset (openComponent_nonempty j)
    obtain ⟨q, hq⟩ := exists_rat_btwn hab
    exact ⟨q, hsub hq⟩ : ∃ q : ℚ, (q : ℝ) ∈ openComponent U j)

theorem countable_openComponentIndex (U : Set ℝ) (hU : IsOpen U) :
    Countable (OpenComponentIndex U) := by
  apply Function.Injective.countable (f := openComponentRational U hU)
  intro j k heq
  apply SetCoe.ext
  apply Set.eq_of_mem_ordConnectedSection_of_uIcc_subset j.property k.property
  have hj := openComponentRational_mem U hU j
  have hk := openComponentRational_mem U hU k
  change (openComponentRational U hU j : ℝ) ∈
    U.ordConnectedComponent (j : ℝ) at hj
  change (openComponentRational U hU k : ℝ) ∈
    U.ordConnectedComponent (k : ℝ) at hk
  rw [Set.mem_ordConnectedComponent] at hj hk
  have hq : (openComponentRational U hU j : ℝ) =
      (openComponentRational U hU k : ℝ) := by exact_mod_cast heq
  rw [← hq] at hk
  rw [uIcc_comm] at hk
  exact (uIcc_subset_uIcc_union_uIcc
    (a := (j : ℝ)) (b := (openComponentRational U hU j : ℝ))
    (c := (k : ℝ))).trans (union_subset hj hk)

theorem pairwise_disjoint_openComponent (U : Set ℝ) :
    _root_.Pairwise (fun i j : OpenComponentIndex U =>
      Disjoint (openComponent U i) (openComponent U j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro y hyi hyj
  change y ∈ U.ordConnectedComponent (i : ℝ) at hyi
  change y ∈ U.ordConnectedComponent (j : ℝ) at hyj
  rw [Set.mem_ordConnectedComponent] at hyi hyj
  have heq : (i : ℝ) = (j : ℝ) :=
    Set.eq_of_mem_ordConnectedSection_of_uIcc_subset i.property j.property
      ((uIcc_subset_uIcc_union_uIcc
        (a := (i : ℝ)) (b := y) (c := (j : ℝ))).trans
        (union_subset hyi (Set.mem_ordConnectedComponent_comm.mp hyj)))
  exact hij (SetCoe.ext heq)

theorem iUnion_openComponent (U : Set ℝ) :
    (⋃ j : OpenComponentIndex U, openComponent U j) = U := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun j => openComponent_subset j
  · intro x hx
    let z : U := ⟨x, hx⟩
    have hj : U.ordConnectedProj z ∈ U.ordConnectedSection :=
      Set.mem_range_self z
    let j : OpenComponentIndex U := ⟨U.ordConnectedProj z, hj⟩
    apply Set.mem_iUnion_of_mem j
    change x ∈ U.ordConnectedComponent (U.ordConnectedProj z)
    exact Set.mem_ordConnectedComponent_ordConnectedProj U z

theorem openComponent_eq_Ioo_csInf_csSup {U : Set ℝ} (hU : IsOpen U)
    (hbelow : BddBelow U) (habove : BddAbove U)
    (j : OpenComponentIndex U) :
    openComponent U j = Ioo (sInf (openComponent U j)) (sSup (openComponent U j)) := by
  let C := openComponent U j
  have hn : C.Nonempty := openComponent_nonempty j
  have hCb : BddBelow C := hbelow.mono (openComponent_subset j)
  have hCa : BddAbove C := habove.mono (openComponent_subset j)
  have hCo : IsOpen C := isOpen_openComponent hU j
  have hCord : C.OrdConnected := Set.instOrdConnectedOrdConnectedComponent
  ext x
  constructor
  · intro hx
    have hxinf : sInf C < x := by
      obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hCo x hx
      have hy : x - e / 2 ∈ C := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_nonpos] <;> linarith)
      exact (csInf_le hCb hy).trans_lt (by linarith)
    have hxsup : x < sSup C := by
      obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hCo x hx
      have hy : x + e / 2 ∈ C := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_nonneg] <;> linarith)
      exact (by linarith : x < x + e / 2).trans_le (le_csSup hCa hy)
    exact ⟨hxinf, hxsup⟩
  · rintro ⟨hinf, hsup⟩
    obtain ⟨a, ha, hax⟩ := exists_lt_of_csInf_lt hn hinf
    obtain ⟨b, hb, hxb⟩ := exists_lt_of_lt_csSup hn hsup
    exact hCord.out ha hb ⟨hax.le, hxb.le⟩

end

end StarKakeyaLower
