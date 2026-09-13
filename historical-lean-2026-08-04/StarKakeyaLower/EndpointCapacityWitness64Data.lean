import StarKakeyaLower.EndpointCapacityClasses
import StarKakeyaLower.EndpointCapacityLogBound

/-!
# Frozen 64-class endpoint-capacity witness data

Every rational below is copied literally from the approved frozen JSON.
The external certificate is only an audit aid; Lean rechecks every consumed fact.
-/
namespace StarKakeyaLower
namespace Witness3527
noncomputable section

def eta : ℝ := 28217997/200000000

def target : ℝ := 3527/50000

def common : ℝ := 44909/2000000

/-- Exact minimum of the 64 four-term rational payment surrogates.  This long
coefficient is kept literally: `common` is only its shorter internal witness. -/
def certifiedCoefficient : ℝ :=
  120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423 /
    5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000

def piLower : ℝ := 333/106

/-- Low-class upper cuts. -/
def b : Fin 64 → ℝ := ![
    (931611/50000000 : ℝ),
    (27912419/1000000000 : ℝ),
    (34377677/1000000000 : ℝ),
    (9957331/250000000 : ℝ),
    (44379433/1000000000 : ℝ),
    (48778479/1000000000 : ℝ),
    (26236409/500000000 : ℝ),
    (11156397/200000000 : ℝ),
    (58993627/1000000000 : ℝ),
    (62219747/1000000000 : ℝ),
    (65126767/1000000000 : ℝ),
    (17019971/250000000 : ℝ),
    (35305961/500000000 : ℝ),
    (73069283/1000000000 : ℝ),
    (75436029/1000000000 : ℝ),
    (38821751/500000000 : ℝ),
    (7986637/100000000 : ℝ),
    (82240047/1000000000 : ℝ),
    (84489497/1000000000 : ℝ),
    (21652739/250000000 : ℝ),
    (2214857/25000000 : ℝ),
    (18110479/200000000 : ℝ),
    (46274981/500000000 : ℝ),
    (11806797/125000000 : ℝ),
    (24086641/250000000 : ℝ),
    (98091341/1000000000 : ℝ),
    (99873073/1000000000 : ℝ),
    (50761443/500000000 : ℝ),
    (51584641/500000000 : ℝ),
    (104852601/1000000000 : ℝ),
    (3327461/31250000 : ℝ),
    (54028719/500000000 : ℝ),
    (109606187/1000000000 : ℝ),
    (111139813/1000000000 : ℝ),
    (112595057/1000000000 : ℝ),
    (114036141/1000000000 : ℝ),
    (11536969/100000000 : ℝ),
    (116748723/1000000000 : ℝ),
    (59061049/500000000 : ℝ),
    (119386217/1000000000 : ℝ),
    (120567141/1000000000 : ℝ),
    (12186657/100000000 : ℝ),
    (24609689/200000000 : ℝ),
    (124304481/1000000000 : ℝ),
    (62739601/500000000 : ℝ),
    (126653743/1000000000 : ℝ),
    (31948669/250000000 : ℝ),
    (32215743/250000000 : ℝ),
    (16251007/125000000 : ℝ),
    (131050237/1000000000 : ℝ),
    (2641177/20000000 : ℝ),
    (66511631/500000000 : ℝ),
    (133927013/1000000000 : ℝ),
    (33708269/250000000 : ℝ),
    (67836727/500000000 : ℝ),
    (106671/781250 : ℝ),
    (5491/40000 : ℝ),
    (34517717/250000000 : ℝ),
    (1084033/7812500 : ℝ),
    (139412221/1000000000 : ℝ),
    (27991819/200000000 : ℝ),
    (140463269/1000000000 : ℝ),
    (140805967/1000000000 : ℝ),
    (28217997/200000000 : ℝ)]

/-- Outer radii of the fixed windows. -/
def outerRadius : Fin 64 → ℝ := ![
    (1/2 : ℝ),
    (500347039/1000000000 : ℝ),
    (500778497/1000000000 : ℝ),
    (501180431/1000000000 : ℝ),
    (250791933/500000000 : ℝ),
    (50196567/100000000 : ℝ),
    (100474741/200000000 : ℝ),
    (1963851/3906250 : ℝ),
    (503102007/1000000000 : ℝ),
    (503468219/1000000000 : ℝ),
    (62982053/125000000 : ℝ),
    (63027957/125000000 : ℝ),
    (100922717/200000000 : ℝ),
    (504961427/1000000000 : ℝ),
    (252655457/500000000 : ℝ),
    (20226343/40000000 : ℝ),
    (252996301/500000000 : ℝ),
    (25316923/50000000 : ℝ),
    (506718289/1000000000 : ℝ),
    (63386029/125000000 : ℝ),
    (253723007/500000000 : ℝ),
    (507788289/1000000000 : ℝ),
    (508133581/1000000000 : ℝ),
    (254246679/500000000 : ℝ),
    (508843423/1000000000 : ℝ),
    (63649757/125000000 : ℝ),
    (509531069/1000000000 : ℝ),
    (254938537/500000000 : ℝ),
    (510202799/1000000000 : ℝ),
    (510532957/1000000000 : ℝ),
    (102175157/200000000 : ℝ),
    (102242403/200000000 : ℝ),
    (102308633/200000000 : ℝ),
    (255936279/500000000 : ℝ),
    (512203141/1000000000 : ℝ),
    (256260437/500000000 : ℝ),
    (512839391/1000000000 : ℝ),
    (513137569/1000000000 : ℝ),
    (256724689/500000000 : ℝ),
    (256881699/500000000 : ℝ),
    (514055511/1000000000 : ℝ),
    (32145691/62500000 : ℝ),
    (128659303/250000000 : ℝ),
    (257459181/500000000 : ℝ),
    (128804989/250000000 : ℝ),
    (128876159/250000000 : ℝ),
    (515791789/1000000000 : ℝ),
    (516073133/1000000000 : ℝ),
    (64542339/125000000 : ℝ),
    (516625681/1000000000 : ℝ),
    (16152779/31250000 : ℝ),
    (517145569/1000000000 : ℝ),
    (258696341/500000000 : ℝ),
    (32351611/62500000 : ℝ),
    (103572189/200000000 : ℝ),
    (103616077/200000000 : ℝ),
    (259153847/500000000 : ℝ),
    (518502097/1000000000 : ℝ),
    (259356687/500000000 : ℝ),
    (259448111/500000000 : ℝ),
    (20762881/40000000 : ℝ),
    (519219171/1000000000 : ℝ),
    (259677651/500000000 : ℝ),
    (129862023/250000000 : ℝ)]

/-- Radial switch points, including both endpoints. -/
def switch : Fin 65 → ℝ := ![
    (931611/50000000 : ℝ),
    (84298807/250000000 : ℝ),
    (340207097/1000000000 : ℝ),
    (171479687/500000000 : ℝ),
    (345687779/1000000000 : ℝ),
    (348246973/1000000000 : ℝ),
    (17548207/50000000 : ℝ),
    (176715051/500000000 : ℝ),
    (177891097/500000000 : ℝ),
    (358195387/1000000000 : ℝ),
    (180375053/500000000 : ℝ),
    (363165363/1000000000 : ℝ),
    (365730779/1000000000 : ℝ),
    (1437583/3906250 : ℝ),
    (370326129/1000000000 : ℝ),
    (186311923/500000000 : ℝ),
    (93709293/250000000 : ℝ),
    (15085449/40000000 : ℝ),
    (189835683/500000000 : ℝ),
    (76430413/200000000 : ℝ),
    (192281781/500000000 : ℝ),
    (386883233/1000000000 : ℝ),
    (9730937/25000000 : ℝ),
    (78341447/200000000 : ℝ),
    (197064053/500000000 : ℝ),
    (99150077/250000000 : ℝ),
    (24933829/62500000 : ℝ),
    (401395603/1000000000 : ℝ),
    (403728039/1000000000 : ℝ),
    (25382249/62500000 : ℝ),
    (102155763/250000000 : ℝ),
    (205555563/500000000 : ℝ),
    (51699039/125000000 : ℝ),
    (416093141/1000000000 : ℝ),
    (41863871/100000000 : ℝ),
    (421121747/1000000000 : ℝ),
    (105912497/250000000 : ℝ),
    (426055011/1000000000 : ℝ),
    (428613431/1000000000 : ℝ),
    (215619389/500000000 : ℝ),
    (21686433/50000000 : ℝ),
    (27257713/62500000 : ℝ),
    (219421249/500000000 : ℝ),
    (110349509/250000000 : ℝ),
    (444209287/1000000000 : ℝ),
    (446935943/1000000000 : ℝ),
    (112441791/250000000 : ℝ),
    (113157383/250000000 : ℝ),
    (56927763/125000000 : ℝ),
    (28659593/62500000 : ℝ),
    (461544651/1000000000 : ℝ),
    (116147083/250000000 : ℝ),
    (467658433/1000000000 : ℝ),
    (470702561/1000000000 : ℝ),
    (473949383/1000000000 : ℝ),
    (477172403/1000000000 : ℝ),
    (480758603/1000000000 : ℝ),
    (7563743/15625000 : ℝ),
    (488046227/1000000000 : ℝ),
    (245947303/500000000 : ℝ),
    (496141449/1000000000 : ℝ),
    (250180679/500000000 : ℝ),
    (101057457/200000000 : ℝ),
    (101989561/200000000 : ℝ),
    (129862023/250000000 : ℝ)]

def classLower (j : Fin 64) : ℝ :=
  if h : j.1 = 0 then 0 else b ⟨j.1 - 1, by omega⟩

@[simp] theorem b_last : b ⟨63, by omega⟩ = eta := by norm_num [b, eta]
@[simp] theorem switch_zero : switch 0 = b 0 := by norm_num [switch, b]
theorem b_pos (j : Fin 64) : 0 < b j := by fin_cases j <;> norm_num [b]
theorem b_le_eta (j : Fin 64) : b j ≤ eta := by fin_cases j <;> norm_num [b, eta]
set_option maxHeartbeats 2000000 in
-- Exhaustive reduction of all 64 frozen window caps.
theorem switch_succ_le_outerRadius (j : Fin 64) :
    switch ⟨j.1 + 1, by omega⟩ ≤ outerRadius j := by
  fin_cases j <;> norm_num [switch, outerRadius]
set_option maxHeartbeats 2000000 in
-- Exhaustive reduction of all 64 frozen geometric budgets.
theorem outerRadius_sq_le_quarter_add_classLower_sq (j : Fin 64) :
    outerRadius j ^ 2 ≤ 1 / 4 + classLower j ^ 2 := by
  fin_cases j <;> norm_num [outerRadius, classLower, b]
theorem target_lt_eta_half : target < eta / 2 := by norm_num [target, eta]
theorem piLower_lt_pi : piLower < Real.pi := by
  have h : piLower < (3.14159265358979323846 : ℝ) := by norm_num [piLower]
  exact h.trans Real.pi_gt_d20
theorem target_lt_common_mul_piLower : target < common * piLower := by
  norm_num [target, common, piLower]
theorem target_lt_common_mul_pi : target < common * Real.pi := by
  exact target_lt_common_mul_piLower.trans
    (mul_lt_mul_of_pos_left piLower_lt_pi (by norm_num [common]))

/-- The actual schedule coefficient times projective-direction volume remains
below the independent height branch.  This keeps `common * π`, rather than a
rounded rational target, as the universal headline constant. -/
theorem common_mul_pi_lt_eta_half : common * Real.pi < eta / 2 := by
  calc
    common * Real.pi < common * 3.14159265358979323847 :=
      mul_lt_mul_of_pos_left Real.pi_lt_d20 (by norm_num [common])
    _ < eta / 2 := by norm_num [common, eta]

theorem common_lt_certifiedCoefficient : common < certifiedCoefficient := by
  norm_num [common, certifiedCoefficient]

/-- The unrounded exact surrogate coefficient also lies below the height
branch after multiplying by projective-direction volume. -/
theorem certifiedCoefficient_mul_pi_lt_eta_half :
    certifiedCoefficient * Real.pi < eta / 2 := by
  calc
    certifiedCoefficient * Real.pi <
        certifiedCoefficient * 3.14159265358979323847 :=
      mul_lt_mul_of_pos_left Real.pi_lt_d20
        (by norm_num [certifiedCoefficient])
    _ < eta / 2 := by norm_num [certifiedCoefficient, eta]
theorem ofReal_target_lt_common_mul_projectiveVolume :
    ENNReal.ofReal target < ENNReal.ofReal common *
      MeasureTheory.volume (Set.univ : Set ProjectiveDirection) := by
  rw [show MeasureTheory.volume (Set.univ : Set ProjectiveDirection) =
      ENNReal.ofReal Real.pi by
    simp [ProjectiveDirection, AddCircle.measure_univ],
    ← ENNReal.ofReal_mul (by norm_num [common])]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by norm_num [common]) Real.pi_pos)).2 target_lt_common_mul_pi
end
end Witness3527
end StarKakeyaLower
