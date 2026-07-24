import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecDivisionSpace
import LeanTrominoes.PartrecPackedColumnPhase
import LeanTrominoes.PartrecSubtractSpace

/-!
# Evaluator-space certificate for packed column phases

The certificate follows the fixed-width arithmetic pipeline: two additions
build the doubled period and phase offset, a third addition combines them,
two predecessors remove the center offset, and quotient/remainder division
returns the wrapped phase.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def packedColumnPhaseDoublePeriodArgumentsCost
    (period phase column : Nat) : Nat :=
  prependCost [period, phase, column] [period] [period]
    (getCost 0 [period, phase, column])
    (getCost 0 [period, phase, column])

theorem packedColumnPhaseDoublePeriodArguments
    (period phase column : Nat) :
    EvaluatorCodeFits
      Code.packedColumnPhaseDoublePeriodArgumentsCode
      [period, phase, column] [period, period]
      (packedColumnPhaseDoublePeriodArgumentsCost
        period phase column) := by
  simpa [Code.packedColumnPhaseDoublePeriodArgumentsCode,
    packedColumnPhaseDoublePeriodArgumentsCost,
    prependCost] using
    prepend (get 0 [period, phase, column])
      (get 0 [period, phase, column])

def packedColumnPhaseDoublePeriodCost
    (period phase column : Nat) : Nat :=
  natAddCost period period +
    packedColumnPhaseDoublePeriodArgumentsCost
      period phase column

theorem packedColumnPhaseDoublePeriod
    (period phase column : Nat) :
    EvaluatorCodeFits Code.packedColumnPhaseDoublePeriodCode
      [period, phase, column] [period + period]
      (packedColumnPhaseDoublePeriodCost
        period phase column) := by
  simpa [Code.packedColumnPhaseDoublePeriodCode,
    packedColumnPhaseDoublePeriodCost] using
    comp (natAdd period period)
      (packedColumnPhaseDoublePeriodArguments
        period phase column)

def packedColumnPhaseOffsetArgumentsCost
    (period phase column : Nat) : Nat :=
  prependCost [period, phase, column] [phase] [column]
    (getCost 1 [period, phase, column])
    (getCost 2 [period, phase, column])

theorem packedColumnPhaseOffsetArguments
    (period phase column : Nat) :
    EvaluatorCodeFits
      Code.packedColumnPhaseOffsetArgumentsCode
      [period, phase, column] [phase, column]
      (packedColumnPhaseOffsetArgumentsCost
        period phase column) := by
  simpa [Code.packedColumnPhaseOffsetArgumentsCode,
    packedColumnPhaseOffsetArgumentsCost,
    prependCost] using
    prepend (get 1 [period, phase, column])
      (get 2 [period, phase, column])

def packedColumnPhaseOffsetCost
    (period phase column : Nat) : Nat :=
  natAddCost phase column +
    packedColumnPhaseOffsetArgumentsCost
      period phase column

theorem packedColumnPhaseOffset
    (period phase column : Nat) :
    EvaluatorCodeFits Code.packedColumnPhaseOffsetCode
      [period, phase, column] [phase + column]
      (packedColumnPhaseOffsetCost period phase column) := by
  simpa [Code.packedColumnPhaseOffsetCode,
    packedColumnPhaseOffsetCost] using
    comp (natAdd phase column)
      (packedColumnPhaseOffsetArguments
        period phase column)

def packedColumnPhaseSumArgumentsCost
    (period phase column : Nat) : Nat :=
  prependCost [period, phase, column]
    [phase + column] [period + period]
    (packedColumnPhaseOffsetCost period phase column)
    (packedColumnPhaseDoublePeriodCost period phase column)

theorem packedColumnPhaseSumArguments
    (period phase column : Nat) :
    EvaluatorCodeFits Code.packedColumnPhaseSumArgumentsCode
      [period, phase, column]
      [phase + column, period + period]
      (packedColumnPhaseSumArgumentsCost
        period phase column) := by
  simpa [Code.packedColumnPhaseSumArgumentsCode,
    packedColumnPhaseSumArgumentsCost,
    prependCost] using
    prepend
      (packedColumnPhaseOffset period phase column)
      (packedColumnPhaseDoublePeriod period phase column)

def packedColumnPhaseSumCost
    (period phase column : Nat) : Nat :=
  natAddCost (phase + column) (period + period) +
    packedColumnPhaseSumArgumentsCost
      period phase column

theorem packedColumnPhaseSum
    (period phase column : Nat) :
    EvaluatorCodeFits Code.packedColumnPhaseSumCode
      [period, phase, column]
      [Code.packedColumnPhaseSum period phase column]
      (packedColumnPhaseSumCost period phase column) := by
  simpa [Code.packedColumnPhaseSumCode,
    Code.packedColumnPhaseSum,
    packedColumnPhaseSumCost, Nat.add_assoc] using
    comp (natAdd (phase + column) (period + period))
      (packedColumnPhaseSumArguments period phase column)

def packedColumnPhaseNumeratorCost
    (period phase column : Nat) : Nat :=
  let sum := Code.packedColumnPhaseSum period phase column
  predCost [sum.pred] +
    (predCost [sum] +
      packedColumnPhaseSumCost period phase column)

theorem packedColumnPhaseNumerator
    (period phase column : Nat) :
    EvaluatorCodeFits Code.packedColumnPhaseNumeratorCode
      [period, phase, column]
      [Code.packedColumnPhaseNumerator period phase column]
      (packedColumnPhaseNumeratorCost
        period phase column) := by
  let sum := Code.packedColumnPhaseSum period phase column
  have once :=
    comp (pred_named [sum])
      (packedColumnPhaseSum period phase column)
  have twice :=
    comp (pred_named [sum.pred]) once
  have numeratorEq :
      sum.pred.pred =
        Code.packedColumnPhaseNumerator
          period phase column := by
    simp [sum, Code.packedColumnPhaseNumerator]
    omega
  rw [← numeratorEq]
  simpa [Code.packedColumnPhaseNumeratorCode,
    Code.subtractStepList,
    packedColumnPhaseNumeratorCost, sum] using twice

def packedColumnPhaseDivisionArgumentsCost
    (period phase column : Nat) : Nat :=
  let numerator :=
    Code.packedColumnPhaseNumerator period phase column
  prependCost [period, phase, column]
    [numerator] [period]
    (packedColumnPhaseNumeratorCost period phase column)
    (getCost 0 [period, phase, column])

theorem packedColumnPhaseDivisionArguments
    (period phase column : Nat) :
    EvaluatorCodeFits
      Code.packedColumnPhaseDivisionArgumentsCode
      [period, phase, column]
      [Code.packedColumnPhaseNumerator period phase column,
        period]
      (packedColumnPhaseDivisionArgumentsCost
        period phase column) := by
  simpa [Code.packedColumnPhaseDivisionArgumentsCode,
    packedColumnPhaseDivisionArgumentsCost,
    prependCost] using
    prepend
      (packedColumnPhaseNumerator period phase column)
      (get 0 [period, phase, column])

def packedColumnPhaseDivisionCost
    (period phase column : Nat) : Nat :=
  let numerator :=
    Code.packedColumnPhaseNumerator period phase column
  divisionSpaceBound numerator period +
    packedColumnPhaseDivisionArgumentsCost
      period phase column

theorem packedColumnPhaseDivision
    (period phase column : Nat) :
    let numerator :=
      Code.packedColumnPhaseNumerator period phase column
    EvaluatorCodeFits Code.packedColumnPhaseDivisionCode
      [period, phase, column]
      [numerator / period, numerator % period]
      (packedColumnPhaseDivisionCost
        period phase column) := by
  simp only
  simpa [Code.packedColumnPhaseDivisionCode,
    packedColumnPhaseDivisionCost] using
    comp
      (division
        (Code.packedColumnPhaseNumerator period phase column)
        period)
      (packedColumnPhaseDivisionArguments
        period phase column)

def packedColumnPhaseCost
    (period phase column : Nat) : Nat :=
  let numerator :=
    Code.packedColumnPhaseNumerator period phase column
  getCost 1 [numerator / period, numerator % period] +
    packedColumnPhaseDivisionCost period phase column

theorem packedColumnPhase
    (period phase column : Nat) :
    EvaluatorCodeFits Code.packedColumnPhaseCode
      [period, phase, column]
      [Code.packedColumnPhaseNumerator period phase column % period]
      (packedColumnPhaseCost period phase column) := by
  let numerator :=
    Code.packedColumnPhaseNumerator period phase column
  simpa [Code.packedColumnPhaseCode,
    packedColumnPhaseCost, numerator] using
    comp (get 1 [numerator / period, numerator % period])
      (packedColumnPhaseDivision period phase column)

set_option maxHeartbeats 1600000 in
theorem packedColumnPhaseCost_le_linear
    (period phase column : Nat) :
    packedColumnPhaseCost period phase column ≤
      10000000000000000 *
        (encodedListSpace
          [128 * (period + phase + column + 32) + 200] + 1) := by
  let doublePeriod := period + period
  let offset := phase + column
  let sum := Code.packedColumnPhaseSum period phase column
  let numerator :=
    Code.packedColumnPhaseNumerator period phase column
  let limit := 128 * (period + phase + column + 32) + 200
  change
    packedColumnPhaseCost period phase column ≤
      10000000000000000 *
        (encodedListSpace [limit] + 1)
  have sumEq : sum = offset + doublePeriod := by
    simp [sum, offset, doublePeriod,
      Code.packedColumnPhaseSum, Nat.add_assoc]
  have numeratorLe : numerator ≤ sum := by
    simp only [numerator,
      Code.packedColumnPhaseNumerator, sum]
    exact Nat.sub_le _ _
  have periodBound : period ≤ limit := by
    simp only [limit]
    omega
  have phaseBound : phase ≤ limit := by
    simp only [limit]
    omega
  have columnBound : column ≤ limit := by
    simp only [limit]
    omega
  have doubleBound : doublePeriod ≤ limit := by
    simp only [doublePeriod, limit]
    omega
  have offsetBound : offset ≤ limit := by
    simp only [offset, limit]
    omega
  have sumBound : sum ≤ limit := by
    simp only [sumEq, offset, doublePeriod, limit]
    omega
  have sumPredBound : sum.pred ≤ limit :=
    (Nat.pred_le sum).trans sumBound
  have numeratorBound : numerator ≤ limit :=
    numeratorLe.trans sumBound
  have quotientBound : numerator / period ≤ limit :=
    (Nat.div_le_self numerator period).trans numeratorBound
  have remainderBound : numerator % period ≤ limit :=
    (Nat.mod_le numerator period).trans numeratorBound
  have periodBits := encodeNat_length_mono periodBound
  have phaseBits := encodeNat_length_mono phaseBound
  have columnBits := encodeNat_length_mono columnBound
  have doubleBits := encodeNat_length_mono doubleBound
  have offsetBits := encodeNat_length_mono offsetBound
  have sumBits := encodeNat_length_mono sumBound
  have sumPredBits := encodeNat_length_mono sumPredBound
  have numeratorBits := encodeNat_length_mono numeratorBound
  have quotientBits := encodeNat_length_mono quotientBound
  have remainderBits := encodeNat_length_mono remainderBound
  have periodSuccBits :=
    encodeNat_length_mono
      (show period + 1 ≤ limit by
        simp only [limit]
        omega)
  have phaseSuccBits :=
    encodeNat_length_mono
      (show phase + 1 ≤ limit by
        simp only [limit]
        omega)
  have columnSuccBits :=
    encodeNat_length_mono
      (show column + 1 ≤ limit by
        simp only [limit]
        omega)
  have doubleSuccBits :=
    encodeNat_length_mono
      (show doublePeriod + 1 ≤ limit by
        simp only [doublePeriod, limit]
        omega)
  have offsetSuccBits :=
    encodeNat_length_mono
      (show offset + 1 ≤ limit by
        simp only [offset, limit]
        omega)
  have sumSuccBits :=
    encodeNat_length_mono
      (show sum + 1 ≤ limit by
        simp only [sum, Code.packedColumnPhaseSum, limit]
        omega)
  have sumPredSuccBits :=
    encodeNat_length_mono
      (show sum.pred + 1 ≤ limit by
        have predLe := Nat.pred_le sum
        simp only [sum, Code.packedColumnPhaseSum, limit] at *
        omega)
  have numeratorSuccBits :=
    encodeNat_length_mono
      (show numerator + 1 ≤ limit by
        simp only [numerator,
          Code.packedColumnPhaseNumerator,
          Code.packedColumnPhaseSum, limit]
        omega)
  have quotientSuccBits :=
    encodeNat_length_mono
      (show numerator / period + 1 ≤ limit by
        have quotientLe := Nat.div_le_self numerator period
        omega)
  have remainderSuccBits :=
    encodeNat_length_mono
      (show numerator % period + 1 ≤ limit by
        have remainderLe := Nat.mod_le numerator period
        omega)
  have addDoubleLocal := natAddCost_le_linear period period
  have addDoubleArgument :
      2 * (period + period) + 4 ≤ limit := by
    simp only [limit]
    omega
  have addDoubleArgumentBits :=
    encodeNat_length_mono addDoubleArgument
  have addDouble :
      natAddCost period period ≤
        100000000 * (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at addDoubleLocal ⊢
    omega
  have addOffsetLocal := natAddCost_le_linear phase column
  have addOffsetArgument :
      2 * (phase + column) + 4 ≤ limit := by
    simp only [limit]
    omega
  have addOffsetArgumentBits :=
    encodeNat_length_mono addOffsetArgument
  have addOffset :
      natAddCost phase column ≤
        100000000 * (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at addOffsetLocal ⊢
    omega
  have addSumLocal :=
    natAddCost_le_linear offset doublePeriod
  have addSumArgument :
      2 * (offset + doublePeriod) + 4 ≤ limit := by
    simp only [offset, doublePeriod, limit]
    omega
  have addSumArgumentBits :=
    encodeNat_length_mono addSumArgument
  have addSum :
      natAddCost offset doublePeriod ≤
        100000000 * (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at addSumLocal ⊢
    omega
  have predSumLocal := predCost_singleton_le_linear sum
  have predSumArgument : 2 * sum + 4 ≤ limit := by
    simp only [sum, Code.packedColumnPhaseSum, limit]
    omega
  have predSumArgumentBits :=
    encodeNat_length_mono predSumArgument
  have predSum :
      predCost [sum] ≤
        1000000 * (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at predSumLocal ⊢
    omega
  have predSumPredLocal :=
    predCost_singleton_le_linear sum.pred
  have predSumPredArgument :
      2 * sum.pred + 4 ≤ limit := by
    have predLe := Nat.pred_le sum
    simp only [sum, Code.packedColumnPhaseSum, limit] at *
    omega
  have predSumPredArgumentBits :=
    encodeNat_length_mono predSumPredArgument
  have predSumPred :
      predCost [sum.pred] ≤
        1000000 * (encodedListSpace [limit] + 1) := by
    simp only [encodedListSpace_cons,
      encodedListSpace_nil] at predSumPredLocal ⊢
    omega
  have divisionArgument :
      8 * (numerator + period) + 16 ≤ limit := by
    simp only [numerator, Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum, limit]
    omega
  have divisionArgumentBits :=
    encodeNat_length_mono divisionArgument
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  simp [packedColumnPhaseCost,
    packedColumnPhaseDivisionCost,
    packedColumnPhaseDivisionArgumentsCost,
    packedColumnPhaseNumeratorCost,
    packedColumnPhaseSumCost,
    packedColumnPhaseSumArgumentsCost,
    packedColumnPhaseOffsetCost,
    packedColumnPhaseOffsetArgumentsCost,
    packedColumnPhaseDoublePeriodCost,
    packedColumnPhaseDoublePeriodArgumentsCost,
    divisionSpaceBound, prependCost, getCost,
    dropCost, headCost, idCost, nilCost, tailCost,
    zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    doublePeriod, offset, sum, numerator,
    zeroBits, oneBits] at *
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
