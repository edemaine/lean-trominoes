import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecIntOffsetSpace
import LeanTrominoes.PartrecPackedColumnPhaseSpace
import LeanTrominoes.PartrecPackedTargetCell
import LeanTrominoes.PartrecPairSpace

/-!
# Evaluator-space certificate for canonical packed target cells

This file fits the complete target constructor: fixed-field projection,
wrapped column arithmetic, nonnegative integer encoding, fixed vertical
offset, and forward pairing into a `Cell` code.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedTargetColumnArgumentsTailCost
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  prependCost values [phase] [column]
    (getCost 1 values) (getCost 2 values)

def packedTargetColumnArgumentsCost
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  prependCost values [period] [phase, column]
    (getCost 0 values)
    (packedTargetColumnArgumentsTailCost
      period phase column rowCode)

theorem packedTargetColumnArguments
    (period phase column rowCode : Nat) :
    EvaluatorCodeFits Code.packedTargetColumnArgumentsCode
      [period, phase, column, rowCode]
      [period, phase, column]
      (packedTargetColumnArgumentsCost
        period phase column rowCode) := by
  let values := [period, phase, column, rowCode]
  have tailFit :
      EvaluatorCodeFits (Code.prepend (Code.get 1) (Code.get 2))
        values [phase, column]
        (packedTargetColumnArgumentsTailCost
          period phase column rowCode) := by
    simpa [packedTargetColumnArgumentsTailCost, values,
      prependCost] using
      prepend (get 1 values) (get 2 values)
  simpa [Code.packedTargetColumnArgumentsCode,
    packedTargetColumnArgumentsCost, values,
    prependCost] using
    prepend (get 0 values) tailFit

def packedTargetColumnPhaseCost
    (period phase column rowCode : Nat) : Nat :=
  packedColumnPhaseCost period phase column +
    packedTargetColumnArgumentsCost period phase column rowCode

theorem packedTargetColumnPhase
    (period phase column rowCode : Nat) :
    EvaluatorCodeFits Code.packedTargetColumnPhaseCode
      [period, phase, column, rowCode]
      [Code.packedColumnPhaseNumerator period phase column % period]
      (packedTargetColumnPhaseCost
        period phase column rowCode) := by
  simpa [Code.packedTargetColumnPhaseCode,
    packedTargetColumnPhaseCost] using
    comp (packedColumnPhase period phase column)
      (packedTargetColumnArguments period phase column rowCode)

def packedTargetXArgumentsCost
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  let x := Code.packedColumnPhaseNumerator period phase column % period
  prependCost values [x] [x]
    (packedTargetColumnPhaseCost period phase column rowCode)
    (packedTargetColumnPhaseCost period phase column rowCode)

theorem packedTargetXArguments
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits Code.packedTargetXArgumentsCode
      [period, phase, column, rowCode] [x, x]
      (packedTargetXArgumentsCost
        period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetXArgumentsCode,
    packedTargetXArgumentsCost, prependCost] using
    prepend
      (packedTargetColumnPhase period phase column rowCode)
      (packedTargetColumnPhase period phase column rowCode)

def packedTargetXCost
    (period phase column rowCode : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column % period
  natAddCost x x +
    packedTargetXArgumentsCost period phase column rowCode

theorem packedTargetX
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits Code.packedTargetXCode
      [period, phase, column, rowCode] [2 * x]
      (packedTargetXCost period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetXCode, packedTargetXCost,
    Nat.two_mul] using
    comp
      (natAdd
        (Code.packedColumnPhaseNumerator period phase column % period)
        (Code.packedColumnPhaseNumerator period phase column % period))
      (packedTargetXArguments period phase column rowCode)

def packedTargetYCost
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  intOffsetCost verticalOffset rowCode +
    getCost 3 [period, phase, column, rowCode]

theorem packedTargetY
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    EvaluatorCodeFits (Code.packedTargetYCode verticalOffset)
      [period, phase, column, rowCode]
      [intOffsetResultCode verticalOffset rowCode]
      (packedTargetYCost verticalOffset
        period phase column rowCode) := by
  simpa [Code.packedTargetYCode,
    packedTargetYCost] using
    comp (intOffset verticalOffset rowCode)
      (get 3 [period, phase, column, rowCode])

def packedTargetCellArgumentsCost
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  let values := [period, phase, column, rowCode]
  let x := Code.packedColumnPhaseNumerator period phase column % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  prependCost values [2 * x] [yCode]
    (packedTargetXCost period phase column rowCode)
    (packedTargetYCost verticalOffset period phase column rowCode)

theorem packedTargetCellArguments
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    let yCode := intOffsetResultCode verticalOffset rowCode
    EvaluatorCodeFits
      (Code.packedTargetCellArgumentsCode verticalOffset)
      [period, phase, column, rowCode]
      [2 * x, yCode]
      (packedTargetCellArgumentsCost verticalOffset
        period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetCellArgumentsCode,
    packedTargetCellArgumentsCost, prependCost] using
    prepend (packedTargetX period phase column rowCode)
      (packedTargetY verticalOffset period phase column rowCode)

def packedTargetCellCost
    (verticalOffset : Int)
    (period phase column rowCode : Nat) : Nat :=
  let x := Code.packedColumnPhaseNumerator period phase column % period
  let yCode := intOffsetResultCode verticalOffset rowCode
  natPairCost (2 * x) yCode +
    packedTargetCellArgumentsCost verticalOffset
      period phase column rowCode

theorem packedTargetCell
    (verticalOffset : Int)
    (period phase column rowCode : Nat) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    let yCode := intOffsetResultCode verticalOffset rowCode
    EvaluatorCodeFits (Code.packedTargetCellCode verticalOffset)
      [period, phase, column, rowCode]
      [Nat.pair (2 * x) yCode]
      (packedTargetCellCost verticalOffset
        period phase column rowCode) := by
  simp only
  simpa [Code.packedTargetCellCode,
    packedTargetCellCost] using
    comp
      (natPair
        (2 * (Code.packedColumnPhaseNumerator
          period phase column % period))
        (intOffsetResultCode verticalOffset rowCode))
      (packedTargetCellArguments verticalOffset
        period phase column rowCode)

theorem packedTargetCell_encode
    (verticalOffset : Int)
    (period phase column : Nat) (row : Int) :
    let x := Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits (Code.packedTargetCellCode verticalOffset)
      [period, phase, column, Encodable.encode row]
      [Encodable.encode
        ((Int.ofNat x, row + verticalOffset) : Cell)]
      (packedTargetCellCost verticalOffset
        period phase column (Encodable.encode row)) := by
  simp only
  have fitted := packedTargetCell verticalOffset
    period phase column (Encodable.encode row)
  simpa only [intOffsetResultCode_encode,
    Encodable.encode_prod_val,
    IntEncoding.encode_ofNat] using fitted

end EvaluatorCodeFits

end PartrecToTM2
end Turing
