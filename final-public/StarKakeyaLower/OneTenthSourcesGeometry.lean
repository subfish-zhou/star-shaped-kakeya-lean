import StarKakeyaLower.OneTenthSources

/-! # Actual far-oriented support frame
Only actual endpoint exchange and a half-turn of the coordinate frame occur.
No reflected or antipodal triangle is adjoined to the target.
-/
open Set MeasureTheory
namespace StarKakeyaLower.OneTenth.Sources
noncomputable section

/-- Coordinate inclusion translated by the actual star centre. -/
def sourcePlane (o : Plane) (z : CoordinatePlane) : Plane :=
  o + WithLp.toLp 2 ![z.1,z.2]

theorem norm_sq_sourcePlane (o : Plane) (z : CoordinatePlane) :
    ‖sourcePlane o z-o‖^2 = planeNormSq z := by
  rw [EuclideanSpace.norm_eq]
  simp only [sourcePlane, add_sub_cancel_left, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (by positivity)

theorem support_reconstruct (o : Plane) (c : ℝ → Plane) (q t : ℝ) :
    sourcePlane o (supportPoint q (signedHeight o c q) (longitudinal o c q+t)) =
      c q + t • angleVector q := by
  ext i
  fin_cases i <;>
    simp [sourcePlane, supportPoint, signedHeight, longitudinal,
      addCoordinatePlane, scaleCoordinatePlane, unitDirection, unitNormal]
  · linear_combination ((c q) 0-o 0) * Real.cos_sq_add_sin_sq q
  · linear_combination ((c q) 1-o 1) * Real.cos_sq_add_sin_sq q

theorem minus_support (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    minus c q = sourcePlane o (supportPoint q (signedHeight o c q) (longitudinal o c q-1/2)) := by
  have he := (support_reconstruct o c q (-(1/2))).symm
  simpa only [minus, neg_smul, sub_eq_add_neg] using he

theorem plus_support (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    plus c q = sourcePlane o (supportPoint q (signedHeight o c q) (longitudinal o c q+1/2)) :=
  (support_reconstruct o c q (1/2)).symm

theorem minus_radius_sq (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    ‖minus c q-o‖^2 = signedHeight o c q^2 + (longitudinal o c q-1/2)^2 := by
  rw [minus_support o, norm_sq_sourcePlane, planeNormSq_supportPoint]

theorem plus_radius_sq (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    ‖plus c q-o‖^2 = signedHeight o c q^2 + (longitudinal o c q+1/2)^2 := by
  rw [plus_support o, norm_sq_sourcePlane, planeNormSq_supportPoint]

/-- The Borel sign test orders the actual endpoint radii, including the tie. -/
theorem minus_radius_le_plus_iff (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    ‖minus c q-o‖ ≤ ‖plus c q-o‖ ↔ 0 ≤ longitudinal o c q := by
  have hl := minus_radius_sq o c q
  have hr := plus_radius_sq o c q
  constructor
  · intro h
    have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    nlinarith
  · intro h
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith

theorem farEndpoint_radius (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    ‖farEndpoint o c q-o‖ = M o c q := by
  classical
  by_cases h : q ∈ A o c
  · have he := (minus_radius_le_plus_iff o c q).mpr h
    simp [farEndpoint, h, M, max_eq_right he]
  · have he : ‖plus c q-o‖ ≤ ‖minus c q-o‖ :=
      le_of_not_ge (fun hh => h ((minus_radius_le_plus_iff o c q).mp hh))
    simp [farEndpoint, h, M, max_eq_left he]

theorem nearEndpoint_radius (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    ‖nearEndpoint o c q-o‖ = N o c q := by
  classical
  by_cases h : q ∈ A o c
  · have he := (minus_radius_le_plus_iff o c q).mpr h
    simp [nearEndpoint, h, N, min_eq_left he]
  · have he : ‖plus c q-o‖ ≤ ‖minus c q-o‖ :=
      le_of_not_ge (fun hh => h ((minus_radius_le_plus_iff o c q).mp hh))
    simp [nearEndpoint, h, N, min_eq_right he]

theorem support_half_turn (q h t : ℝ) :
    supportPoint (Real.pi+q) (-h) (-t) = supportPoint q h t := by
  ext <;> simp [supportPoint, addCoordinatePlane, scaleCoordinatePlane,
    unitDirection, unitNormal, Real.cos_add, Real.sin_add]

/-- Far longitudinal coordinate is exactly 1/2+|s| in the selected frame. -/
theorem farEndpoint_support (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    farEndpoint o c q = sourcePlane o
      (supportPoint (farAngle o c q) (farHeight o c q) (x o c q)) := by
  classical
  by_cases h : q ∈ A o c
  · have hs : 0 ≤ longitudinal o c q := h
    simpa [farEndpoint, farAngle, selectedAngle, farHeight, h, x, abs_of_nonneg hs, add_comm]
      using plus_support o c q
  · have hs : longitudinal o c q < 0 := lt_of_not_ge h
    have he : (1/2 : ℝ) + |longitudinal o c q| = -(longitudinal o c q-1/2) := by
      rw [abs_of_neg hs]; ring
    simp only [farEndpoint, farAngle, selectedAngle, farHeight, if_neg h, x, he,
      support_half_turn]
    exact minus_support o c q

theorem nearEndpoint_support (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    nearEndpoint o c q = sourcePlane o
      (supportPoint (farAngle o c q) (farHeight o c q) (x o c q-1)) := by
  classical
  by_cases h : q ∈ A o c
  · have hs : 0 ≤ longitudinal o c q := h
    have he : (1/2 : ℝ) + |longitudinal o c q|-1 = longitudinal o c q-1/2 := by
      rw [abs_of_nonneg hs]; ring
    simp only [nearEndpoint, farAngle, selectedAngle, farHeight, if_pos h, x, he]
    exact minus_support o c q
  · have hs : longitudinal o c q < 0 := lt_of_not_ge h
    have he : (1/2 : ℝ) + |longitudinal o c q|-1 = -(longitudinal o c q+1/2) := by
      rw [abs_of_neg hs]; ring
    simp only [nearEndpoint, farAngle, selectedAngle, farHeight, if_neg h, x, he,
      support_half_turn]
    exact plus_support o c q

theorem M_sq (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    M o c q^2 = farHeight o c q^2 + x o c q^2 := by
  rw [← farEndpoint_radius, farEndpoint_support, norm_sq_sourcePlane, planeNormSq_supportPoint]

theorem N_sq (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    N o c q^2 = farHeight o c q^2 + (x o c q-1)^2 := by
  rw [← nearEndpoint_radius, nearEndpoint_support, norm_sq_sourcePlane, planeNormSq_supportPoint]

theorem x_le_M (o : Plane) (c : ℝ → Plane) (q : ℝ) : x o c q ≤ M o c q := by
  have he := M_sq o c q
  have hm := half_le_M o c q
  nlinarith [sq_nonneg (farHeight o c q)]

/-- An actual far-oriented unit needle with near endpoint on the left. -/
def farNeedle (o : Plane) (c : ℝ → Plane) (q : ℝ) : UnitNeedle where
  left := nearEndpoint o c q
  right := farEndpoint o c q
  unit_length := by
    classical
    by_cases h : q ∈ A o c
    · simpa [nearEndpoint, farEndpoint, h] using unit_length c q
    · simpa [nearEndpoint, farEndpoint, h, dist_comm] using unit_length c q

theorem farNeedle_triangle (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    (farNeedle o c q).triangleHull o = triangle o c q := by
  classical
  by_cases h : q ∈ A o c
  · simp [triangle, UnitNeedle.triangleHull, UnitNeedle.carrier,
      farNeedle, nearEndpoint, farEndpoint, h]
  · simp [triangle, UnitNeedle.triangleHull, UnitNeedle.carrier,
      farNeedle, nearEndpoint, farEndpoint, h, segment_symm]

/-- Exact support triangle bridge (including negative/zero height and external
feet). It is the same triangle, not its reflection or its antipodal union. -/
theorem triangle_eq_support_image (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    triangle o c q = sourcePlane o ''
      supportNeedleTriangle (farAngle o c q) (farHeight o c q) (x o c q-1/2) := by
  rw [← farNeedle_triangle, triangleHull_eq_square_image]
  have hl := nearEndpoint_support o c q
  have hr := farEndpoint_support o c q
  ext y
  constructor
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩,rfl⟩
    refine ⟨scaleCoordinatePlane s (supportPoint (farAngle o c q) (farHeight o c q)
      (x o c q-1+t)), ⟨s,hs,x o c q-1+t,?_,rfl⟩,?_⟩
    · constructor <;> linarith [ht.1,ht.2]
    · change sourcePlane o _ = trianglePoint o (nearEndpoint o c q) (farEndpoint o c q) (s,t)
      rw [hl,hr]
      ext i
      fin_cases i <;> simp [sourcePlane,trianglePoint,supportPoint,addCoordinatePlane,
        scaleCoordinatePlane,unitDirection,unitNormal] <;> ring
  · rintro ⟨_,⟨s,hs,t,ht,rfl⟩,rfl⟩
    refine ⟨(s,t-(x o c q-1)),⟨hs,?_⟩,?_⟩
    · constructor <;> linarith [ht.1,ht.2]
    · change trianglePoint o (nearEndpoint o c q) (farEndpoint o c q) _ = sourcePlane o _
      rw [hl,hr]
      ext i
      fin_cases i <;> simp [sourcePlane,trianglePoint,supportPoint,addCoordinatePlane,
        scaleCoordinatePlane,unitDirection,unitNormal] <;> ring

/-- Signed height agrees with the actual Euclidean UnitNeedle height. -/
theorem needle_height (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    (needle c q).height o = |signedHeight o c q| := by
  have hv : (needle c q).right - (needle c q).left = (1 : ℝ) • angleVector q := by
    simpa using plus_sub_minus c q
  rw [UnitNeedle.height_eq_abs_normalCoord (by norm_num : |(1 : ℝ)| = 1) hv]
  have he : normalCoord q (o-(needle c q).left) = -signedHeight o c q := by
    simp [normalCoord,det,minus,signedHeight]
    ring
  rw [he, abs_neg]

theorem abs_farHeight (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    |farHeight o c q| = |signedHeight o c q| := by
  classical
  unfold farHeight
  split_ifs <;> simp

theorem farAngle_mem_physical_chart (o : Plane) (c : ℝ → Plane) {q : ℝ} (hq : q ∈ chart) :
    farAngle o c q ∈ Ioc 0 (2*Real.pi) := by
  classical
  have h0 : 0 < q := hq.1
  have hpi : q ≤ Real.pi := hq.2
  unfold farAngle selectedAngle
  split_ifs <;> constructor <;> linarith [Real.pi_pos]

theorem farAngle_projective (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    (farAngle o c q : Direction) = (q : Direction) := by
  classical
  unfold farAngle selectedAngle
  split_ifs
  · rfl
  · simp

/-- At an equal-radius tie the original first physical lift is used. -/
theorem farAngle_tie (o : Plane) (c : ℝ → Plane) {q : ℝ}
    (hq : longitudinal o c q = 0) : farAngle o c q = q := by
  classical
  simp [farAngle, selectedAngle, A, hq]

theorem endpoint_radius_bounds (o : Plane) (c : ℝ → Plane) (q : ℝ) :
    0 ≤ N o c q ∧ N o c q ≤ M o c q ∧ M o c q ≤ N o c q+1 := by
  have hl := norm_sub_le (minus c q-o) (plus c q-minus c q)
  have hr := norm_add_le (minus c q-o) (plus c q-minus c q)
  have hn : ‖plus c q-minus c q‖ = 1 := by rw [plus_sub_minus,norm_angleVector]
  have hp : plus c q-o = (minus c q-o)+(plus c q-minus c q) := by module
  have hm : minus c q-o = (plus c q-o)-(plus c q-minus c q) := by module
  have hplus : ‖plus c q-o‖ ≤ ‖minus c q-o‖+1 := by rw [hp]; simpa [hn] using hr
  have hminus : ‖minus c q-o‖ ≤ ‖plus c q-o‖+1 := by
    calc
      ‖minus c q-o‖ = ‖(plus c q-o)-(plus c q-minus c q)‖ := congrArg norm hm
      _ ≤ ‖plus c q-o‖+‖plus c q-minus c q‖ := norm_sub_le _ _
      _ = ‖plus c q-o‖+1 := by rw [hn]
  refine ⟨le_min (norm_nonneg _) (norm_nonneg _),
    (min_le_left _ _).trans (le_max_left _ _), ?_⟩
  unfold M N
  rcases le_total ‖minus c q-o‖ ‖plus c q-o‖ with h | h
  · simpa [max_eq_right h,min_eq_left h] using hplus
  · simpa [max_eq_left h,min_eq_right h] using hminus

end
end StarKakeyaLower.OneTenth.Sources
