import LeanTrominoes.PartrecFlatStripWellFormed
import LeanTrominoes.PartrecPairSpace
import LeanTrominoes.PartrecStripCellBoundsSpace

/-!
# Evaluator-space certificates for flat strip well-formedness

This module fits the individual coordinate-pair step used by the flat motif
scanner.  The exact certificates retain the unconsumed coordinate suffix as a
native list; subsequent uniform bounds can therefore charge that suffix
directly to the original flat input stream.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def flatStripMotifCellPairArgumentsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  prependCost state [Encodable.encode cell.1] [Encodable.encode cell.2]
    (getCost 3 state) (getCost 4 state)

theorem flatStripMotifCellPairArguments
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifCellPairArgumentsCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [Encodable.encode cell.1, Encodable.encode cell.2]
      (flatStripMotifCellPairArgumentsCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [Code.flatStripMotifCellPairArgumentsCode,
    flatStripMotifCellPairArgumentsCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 3 state) (get 4 state)

def flatStripMotifCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  natPairCost (Encodable.encode cell.1) (Encodable.encode cell.2) +
    flatStripMotifCellPairArgumentsCost width period valid cell remaining

theorem flatStripMotifCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifCellCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [Encodable.encode cell]
      (flatStripMotifCellCost width period valid cell remaining) := by
  rcases cell with ⟨x, y⟩
  simpa [Code.flatStripMotifCellCode, flatStripMotifCellCost] using
    comp (natPair (Encodable.encode x) (Encodable.encode y))
      (flatStripMotifCellPairArguments width period valid (x, y) remaining)

def flatStripMotifPeriodAndCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  prependCost state [period] [Encodable.encode cell]
    (getCost 2 state)
    (flatStripMotifCellCost width period valid cell remaining)

theorem flatStripMotifPeriodAndCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) Code.flatStripMotifCellCode)
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [period, Encodable.encode cell]
      (flatStripMotifPeriodAndCellCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [flatStripMotifPeriodAndCellCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 2 state)
      (flatStripMotifCell width period valid cell remaining)

def flatStripMotifCellArgumentsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  prependCost state [width] [period, Encodable.encode cell]
    (getCost 1 state)
    (flatStripMotifPeriodAndCellCost width period valid cell remaining)

theorem flatStripMotifCellArguments
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifCellArgumentsCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [width, period, Encodable.encode cell]
      (flatStripMotifCellArgumentsCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [Code.flatStripMotifCellArgumentsCode,
    flatStripMotifCellArgumentsCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 1 state)
      (flatStripMotifPeriodAndCell width period valid cell remaining)

def flatStripMotifHeadInBoundsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  stripCellInBoundsCost width period cell +
    flatStripMotifCellArgumentsCost width period valid cell remaining

theorem flatStripMotifHeadInBounds
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifHeadInBoundsCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [if cell.InStripBounds width period then 1 else 0]
      (flatStripMotifHeadInBoundsCost
        width period valid cell remaining) := by
  simpa [Code.flatStripMotifHeadInBoundsCode,
    flatStripMotifHeadInBoundsCost] using
    comp (stripCellInBounds width period cell)
      (flatStripMotifCellArguments width period valid cell remaining)

def flatStripMotifUpdatedValidCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let cellTag := if cell.InStripBounds width period then 1 else 0
  boolAndCost state valid.toNat cellTag
    (getCost 0 state)
    (flatStripMotifHeadInBoundsCost width period valid cell remaining)

theorem flatStripMotifUpdatedValid
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifUpdatedValidCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [(valid && decide (cell.InStripBounds width period)).toNat]
      (flatStripMotifUpdatedValidCost
        width period valid cell remaining) := by
  have combined :=
    boolAnd
      (get 0
        (Code.flatStripMotifState width period valid (cell :: remaining)))
      (flatStripMotifHeadInBounds width period valid cell remaining)
  cases valid <;>
    by_cases inBounds : cell.InStripBounds width period <;>
    simpa [Code.flatStripMotifUpdatedValidCode,
      flatStripMotifUpdatedValidCost, Code.flatStripMotifState,
      PeriodicStripFlatEncoding.cellFields, inBounds] using combined

def flatStripMotifPeriodAndRestCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost state [period] rest
    (getCost 2 state) (dropCost 5 state)

theorem flatStripMotifPeriodAndRest
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) (Code.drop 5))
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (period ::
        remaining.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripMotifPeriodAndRestCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [flatStripMotifPeriodAndRestCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 2 state) (drop 5 state)

def flatStripMotifDimensionsAndRestCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost state [width] (period :: rest)
    (getCost 1 state)
    (flatStripMotifPeriodAndRestCost width period valid cell remaining)

theorem flatStripMotifDimensionsAndRest
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 1) <|
        Code.prepend (Code.get 2) (Code.drop 5))
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (width :: period ::
        remaining.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripMotifDimensionsAndRestCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [flatStripMotifDimensionsAndRestCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 1 state)
      (flatStripMotifPeriodAndRest width period valid cell remaining)

def flatStripMotifStepCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let nextValid := valid && decide (cell.InStripBounds width period)
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost state [nextValid.toNat] (width :: period :: rest)
    (flatStripMotifUpdatedValidCost width period valid cell remaining)
    (flatStripMotifDimensionsAndRestCost width period valid cell remaining)

theorem flatStripMotifStep
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifStepCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (Code.flatStripMotifState width period
        (valid && decide (cell.InStripBounds width period)) remaining)
      (flatStripMotifStepCost width period valid cell remaining) := by
  have fitted :=
    prepend
      (flatStripMotifUpdatedValid width period valid cell remaining)
      (flatStripMotifDimensionsAndRest width period valid cell remaining)
  simpa [Code.flatStripMotifStepCode, flatStripMotifStepCost,
    Code.flatStripMotifState, PeriodicStripFlatEncoding.cellFields,
    prependCost] using fitted

def flatStripMotifBodyCost
    (remainingCount width period : Nat)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  flatCountdownBodyCost Code.flatStripMotifNativeStep
    (fun _ => flatStripMotifStepCost width period valid cell remaining)
    remainingCount
    (Code.flatStripMotifState width period valid (cell :: remaining))

theorem flatStripMotifBodySucc
    (remainingCount width period : Nat)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatStripMotifStepCode)
      ((remainingCount + 1) ::
        Code.flatStripMotifState width period valid (cell :: remaining))
      (flatCountdownOutput Code.flatStripMotifNativeStep
        (remainingCount + 1)
        (Code.flatStripMotifState width period valid (cell :: remaining)))
      (flatStripMotifBodyCost
        (remainingCount + 1) width period valid cell remaining) := by
  let payload :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let values := remainingCount :: payload
  have transformed :=
    comp (flatStripMotifStep width period valid cell remaining)
      (tail_named values)
  have payloadResult := prepend (head values) transformed
  have branch := prepend (one values) payloadResult
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatStripMotifBodyCost, flatCountdownBodyCost,
    flatCountdownSuccBranchCost, payload, values, prependCost,
    Code.prepend] using
    EvaluatorCodeFits.case_succ
      (zeroBranch := Code.zero')
      (values := (remainingCount + 1) :: payload)
      (predecessor := remainingCount) (by rfl) branch

end EvaluatorCodeFits

end PartrecToTM2
end Turing
