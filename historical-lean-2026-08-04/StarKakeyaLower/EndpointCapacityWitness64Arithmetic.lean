import StarKakeyaLower.EndpointCapacityPayment
import StarKakeyaLower.EndpointCapacityWitness64Data

/-!
# Four-term arithmetic certificate for the frozen N=64 witness

Each declaration checks one cumulative rational payment independently, avoiding
one monolithic proof state.  No generated total is trusted.
-/
open scoped BigOperators
namespace StarKakeyaLower.Witness3527
noncomputable section


def lowHeadLower (j : Fin 64) : ℝ :=
  endpointWindowPaymentLowerFour (outerRadius 0) (b j) (switch 1)

def lowSegmentLower (i : Fin 64) : ℝ :=
  endpointWindowPaymentLowerFour (outerRadius i)
    (switch ⟨i.1, by omega⟩) (switch ⟨i.1 + 1, by omega⟩)

def lowPaymentLower (j : Fin 64) : ℝ :=
  lowHeadLower j +
    ∑ i : Fin 64, if 1 ≤ i.1 ∧ i.1 ≤ j.1 then lowSegmentLower i else 0

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row0 :
    certifiedCoefficient ≤ lowPaymentLower ⟨0, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row1 :
    certifiedCoefficient ≤ lowPaymentLower ⟨1, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row2 :
    certifiedCoefficient ≤ lowPaymentLower ⟨2, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row3 :
    certifiedCoefficient ≤ lowPaymentLower ⟨3, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row4 :
    certifiedCoefficient ≤ lowPaymentLower ⟨4, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row5 :
    certifiedCoefficient ≤ lowPaymentLower ⟨5, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row6 :
    certifiedCoefficient ≤ lowPaymentLower ⟨6, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row7 :
    certifiedCoefficient ≤ lowPaymentLower ⟨7, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row8 :
    certifiedCoefficient ≤ lowPaymentLower ⟨8, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row9 :
    certifiedCoefficient ≤ lowPaymentLower ⟨9, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row10 :
    certifiedCoefficient ≤ lowPaymentLower ⟨10, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row11 :
    certifiedCoefficient ≤ lowPaymentLower ⟨11, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row12 :
    certifiedCoefficient ≤ lowPaymentLower ⟨12, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row13 :
    certifiedCoefficient ≤ lowPaymentLower ⟨13, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row14 :
    certifiedCoefficient ≤ lowPaymentLower ⟨14, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row15 :
    certifiedCoefficient ≤ lowPaymentLower ⟨15, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row16 :
    certifiedCoefficient ≤ lowPaymentLower ⟨16, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row17 :
    certifiedCoefficient ≤ lowPaymentLower ⟨17, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row18 :
    certifiedCoefficient ≤ lowPaymentLower ⟨18, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row19 :
    certifiedCoefficient ≤ lowPaymentLower ⟨19, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row20 :
    certifiedCoefficient ≤ lowPaymentLower ⟨20, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row21 :
    certifiedCoefficient ≤ lowPaymentLower ⟨21, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row22 :
    certifiedCoefficient ≤ lowPaymentLower ⟨22, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row23 :
    certifiedCoefficient ≤ lowPaymentLower ⟨23, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row24 :
    certifiedCoefficient ≤ lowPaymentLower ⟨24, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row25 :
    certifiedCoefficient ≤ lowPaymentLower ⟨25, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row26 :
    certifiedCoefficient ≤ lowPaymentLower ⟨26, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row27 :
    certifiedCoefficient ≤ lowPaymentLower ⟨27, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row28 :
    certifiedCoefficient ≤ lowPaymentLower ⟨28, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row29 :
    certifiedCoefficient ≤ lowPaymentLower ⟨29, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row30 :
    certifiedCoefficient ≤ lowPaymentLower ⟨30, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row31 :
    certifiedCoefficient ≤ lowPaymentLower ⟨31, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row32 :
    certifiedCoefficient ≤ lowPaymentLower ⟨32, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row33 :
    certifiedCoefficient ≤ lowPaymentLower ⟨33, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row34 :
    certifiedCoefficient ≤ lowPaymentLower ⟨34, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row35 :
    certifiedCoefficient ≤ lowPaymentLower ⟨35, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row36 :
    certifiedCoefficient ≤ lowPaymentLower ⟨36, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row37 :
    certifiedCoefficient ≤ lowPaymentLower ⟨37, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row38 :
    certifiedCoefficient ≤ lowPaymentLower ⟨38, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row39 :
    certifiedCoefficient ≤ lowPaymentLower ⟨39, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row40 :
    certifiedCoefficient ≤ lowPaymentLower ⟨40, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row41 :
    certifiedCoefficient ≤ lowPaymentLower ⟨41, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row42 :
    certifiedCoefficient ≤ lowPaymentLower ⟨42, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row43 :
    certifiedCoefficient ≤ lowPaymentLower ⟨43, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row44 :
    certifiedCoefficient ≤ lowPaymentLower ⟨44, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row45 :
    certifiedCoefficient ≤ lowPaymentLower ⟨45, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row46 :
    certifiedCoefficient ≤ lowPaymentLower ⟨46, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row47 :
    certifiedCoefficient ≤ lowPaymentLower ⟨47, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row48 :
    certifiedCoefficient ≤ lowPaymentLower ⟨48, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row49 :
    certifiedCoefficient ≤ lowPaymentLower ⟨49, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row50 :
    certifiedCoefficient ≤ lowPaymentLower ⟨50, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row51 :
    certifiedCoefficient ≤ lowPaymentLower ⟨51, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row52 :
    certifiedCoefficient ≤ lowPaymentLower ⟨52, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row53 :
    certifiedCoefficient ≤ lowPaymentLower ⟨53, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row54 :
    certifiedCoefficient ≤ lowPaymentLower ⟨54, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row55 :
    certifiedCoefficient ≤ lowPaymentLower ⟨55, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row56 :
    certifiedCoefficient ≤ lowPaymentLower ⟨56, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row57 :
    certifiedCoefficient ≤ lowPaymentLower ⟨57, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row58 :
    certifiedCoefficient ≤ lowPaymentLower ⟨58, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row59 :
    certifiedCoefficient ≤ lowPaymentLower ⟨59, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row60 :
    certifiedCoefficient ≤ lowPaymentLower ⟨60, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row61 :
    certifiedCoefficient ≤ lowPaymentLower ⟨61, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row62 :
    certifiedCoefficient ≤ lowPaymentLower ⟨62, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- One isolated exact row; separation bounds retained elaboration memory.
private theorem certifiedCoefficient_le_lowPaymentLower_row63 :
    certifiedCoefficient ≤ lowPaymentLower ⟨63, by omega⟩ := by
  norm_num [lowPaymentLower, lowHeadLower, lowSegmentLower,
    endpointWindowPaymentLowerFour, logRatioFourTermUpper,
    outerRadius, b, switch, certifiedCoefficient, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
-- Dispatch over 64 already-isolated exact row theorems.
theorem certifiedCoefficient_le_lowPaymentLower (j : Fin 64) :
    certifiedCoefficient ≤ lowPaymentLower j := by
  fin_cases j
  · exact certifiedCoefficient_le_lowPaymentLower_row0
  · exact certifiedCoefficient_le_lowPaymentLower_row1
  · exact certifiedCoefficient_le_lowPaymentLower_row2
  · exact certifiedCoefficient_le_lowPaymentLower_row3
  · exact certifiedCoefficient_le_lowPaymentLower_row4
  · exact certifiedCoefficient_le_lowPaymentLower_row5
  · exact certifiedCoefficient_le_lowPaymentLower_row6
  · exact certifiedCoefficient_le_lowPaymentLower_row7
  · exact certifiedCoefficient_le_lowPaymentLower_row8
  · exact certifiedCoefficient_le_lowPaymentLower_row9
  · exact certifiedCoefficient_le_lowPaymentLower_row10
  · exact certifiedCoefficient_le_lowPaymentLower_row11
  · exact certifiedCoefficient_le_lowPaymentLower_row12
  · exact certifiedCoefficient_le_lowPaymentLower_row13
  · exact certifiedCoefficient_le_lowPaymentLower_row14
  · exact certifiedCoefficient_le_lowPaymentLower_row15
  · exact certifiedCoefficient_le_lowPaymentLower_row16
  · exact certifiedCoefficient_le_lowPaymentLower_row17
  · exact certifiedCoefficient_le_lowPaymentLower_row18
  · exact certifiedCoefficient_le_lowPaymentLower_row19
  · exact certifiedCoefficient_le_lowPaymentLower_row20
  · exact certifiedCoefficient_le_lowPaymentLower_row21
  · exact certifiedCoefficient_le_lowPaymentLower_row22
  · exact certifiedCoefficient_le_lowPaymentLower_row23
  · exact certifiedCoefficient_le_lowPaymentLower_row24
  · exact certifiedCoefficient_le_lowPaymentLower_row25
  · exact certifiedCoefficient_le_lowPaymentLower_row26
  · exact certifiedCoefficient_le_lowPaymentLower_row27
  · exact certifiedCoefficient_le_lowPaymentLower_row28
  · exact certifiedCoefficient_le_lowPaymentLower_row29
  · exact certifiedCoefficient_le_lowPaymentLower_row30
  · exact certifiedCoefficient_le_lowPaymentLower_row31
  · exact certifiedCoefficient_le_lowPaymentLower_row32
  · exact certifiedCoefficient_le_lowPaymentLower_row33
  · exact certifiedCoefficient_le_lowPaymentLower_row34
  · exact certifiedCoefficient_le_lowPaymentLower_row35
  · exact certifiedCoefficient_le_lowPaymentLower_row36
  · exact certifiedCoefficient_le_lowPaymentLower_row37
  · exact certifiedCoefficient_le_lowPaymentLower_row38
  · exact certifiedCoefficient_le_lowPaymentLower_row39
  · exact certifiedCoefficient_le_lowPaymentLower_row40
  · exact certifiedCoefficient_le_lowPaymentLower_row41
  · exact certifiedCoefficient_le_lowPaymentLower_row42
  · exact certifiedCoefficient_le_lowPaymentLower_row43
  · exact certifiedCoefficient_le_lowPaymentLower_row44
  · exact certifiedCoefficient_le_lowPaymentLower_row45
  · exact certifiedCoefficient_le_lowPaymentLower_row46
  · exact certifiedCoefficient_le_lowPaymentLower_row47
  · exact certifiedCoefficient_le_lowPaymentLower_row48
  · exact certifiedCoefficient_le_lowPaymentLower_row49
  · exact certifiedCoefficient_le_lowPaymentLower_row50
  · exact certifiedCoefficient_le_lowPaymentLower_row51
  · exact certifiedCoefficient_le_lowPaymentLower_row52
  · exact certifiedCoefficient_le_lowPaymentLower_row53
  · exact certifiedCoefficient_le_lowPaymentLower_row54
  · exact certifiedCoefficient_le_lowPaymentLower_row55
  · exact certifiedCoefficient_le_lowPaymentLower_row56
  · exact certifiedCoefficient_le_lowPaymentLower_row57
  · exact certifiedCoefficient_le_lowPaymentLower_row58
  · exact certifiedCoefficient_le_lowPaymentLower_row59
  · exact certifiedCoefficient_le_lowPaymentLower_row60
  · exact certifiedCoefficient_le_lowPaymentLower_row61
  · exact certifiedCoefficient_le_lowPaymentLower_row62
  · exact certifiedCoefficient_le_lowPaymentLower_row63

def lowHeadPayment (j : Fin 64) : ℝ :=
  endpointWindowPayment (outerRadius 0) (b j) (switch 1)

def lowSegmentPayment (i : Fin 64) : ℝ :=
  endpointWindowPayment (outerRadius i)
    (switch ⟨i.1, by omega⟩) (switch ⟨i.1 + 1, by omega⟩)

def lowPayment (j : Fin 64) : ℝ :=
  lowHeadPayment j +
    ∑ i : Fin 64, if 1 ≤ i.1 ∧ i.1 ≤ j.1 then lowSegmentPayment i else 0

private theorem lowHeadLower_le (j : Fin 64) : lowHeadLower j ≤ lowHeadPayment j := by
  apply endpointWindowPaymentLowerFour_le
  · norm_num [outerRadius]
  · exact (b_pos j).le
  · exact (b_le_eta j).trans (by norm_num [eta, switch])

set_option maxHeartbeats 2000000 in
-- Exhaustive positivity/order discharge for all frozen segments.
private theorem lowSegmentLower_le (i : Fin 64) : lowSegmentLower i ≤ lowSegmentPayment i := by
  apply endpointWindowPaymentLowerFour_le
  · fin_cases i <;> norm_num [outerRadius]
  · fin_cases i <;> norm_num [switch]
  · fin_cases i <;> norm_num [switch]

theorem lowPaymentLower_le_lowPayment (j : Fin 64) : lowPaymentLower j ≤ lowPayment j := by
  unfold lowPaymentLower lowPayment
  apply add_le_add (lowHeadLower_le j)
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · exact lowSegmentLower_le i
  · exact le_rfl

theorem certifiedCoefficient_le_lowPayment (j : Fin 64) :
    certifiedCoefficient ≤ lowPayment j :=
  (certifiedCoefficient_le_lowPaymentLower j).trans (lowPaymentLower_le_lowPayment j)

theorem common_lt_lowPayment (j : Fin 64) : common < lowPayment j :=
  common_lt_certifiedCoefficient.trans_le (certifiedCoefficient_le_lowPayment j)

end
end StarKakeyaLower.Witness3527
