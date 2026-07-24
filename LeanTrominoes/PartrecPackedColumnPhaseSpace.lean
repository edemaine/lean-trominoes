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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
