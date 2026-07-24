import LeanTrominoes.PartrecStripWellFormed
import LeanTrominoes.PartrecStripCellBoundsSpace
import LeanTrominoes.PartrecEncodedListDecodeSpace
import LeanTrominoes.PartrecPeriodicStripDecodeSpace
import LeanTrominoes.PartrecNatCompareSpace

/-!
# Evaluator-space certificate for strip well-formedness

This module first fits every reachable typed motif step and then lifts those
certificates through the flat countdown using its reachable-state rule.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def stripMotifViewCost
    (width period : Nat) (valid : Bool)
    (motif : List Cell) : Nat :=
  encodedListViewCost motif +
    getCost 0
      (Code.stripMotifState width period valid motif)

theorem stripMotifView
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits Code.stripMotifViewCode
      (Code.stripMotifState width period valid motif)
      (match motif with
      | [] => [0, 0, 0]
      | cell :: remaining =>
          [1, Encodable.encode cell,
            Encodable.encode remaining])
      (stripMotifViewCost width period valid motif) := by
  cases motif with
  | nil =>
      simpa [Code.stripMotifViewCode,
        stripMotifViewCost] using
        comp (encodedListView ([] : List Cell))
          (get 0
            (Code.stripMotifState width period valid []))
  | cons cell remaining =>
      simpa [Code.stripMotifViewCode,
        stripMotifViewCost] using
        comp (encodedListView (cell :: remaining))
          (get 0
            (Code.stripMotifState width period valid
              (cell :: remaining)))

def stripMotifHeadCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 1
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    stripMotifViewCost width period valid
      (cell :: remaining)

theorem stripMotifHeadCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.stripMotifHeadCellCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [Encodable.encode cell]
      (stripMotifHeadCellCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifHeadCellCode,
    stripMotifHeadCellCost] using
    comp
      (get 1
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (stripMotifView width period valid
        (cell :: remaining))

def stripMotifTailCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 2
      [1, Encodable.encode cell,
        Encodable.encode remaining] +
    stripMotifViewCost width period valid
      (cell :: remaining)

theorem stripMotifTail
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.stripMotifTailCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [Encodable.encode remaining]
      (stripMotifTailCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifTailCode,
    stripMotifTailCost] using
    comp
      (get 2
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (stripMotifView width period valid
        (cell :: remaining))

def stripMotifPeriodAndCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  prependCost state [period] [Encodable.encode cell]
    (getCost 3 state)
    (stripMotifHeadCellCost
      width period valid cell remaining)

theorem stripMotifPeriodAndCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 3)
        Code.stripMotifHeadCellCode)
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [period, Encodable.encode cell]
      (stripMotifPeriodAndCellCost
        width period valid cell remaining) := by
  simpa [stripMotifPeriodAndCellCost,
    prependCost, Code.stripMotifState] using
    prepend
      (get 3
        (Code.stripMotifState width period valid
          (cell :: remaining)))
      (stripMotifHeadCell width period valid
        cell remaining)

def stripMotifCellArgumentsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  prependCost state [width]
    [period, Encodable.encode cell]
    (getCost 2 state)
    (stripMotifPeriodAndCellCost
      width period valid cell remaining)

theorem stripMotifCellArguments
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      Code.stripMotifCellArgumentsCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [width, period, Encodable.encode cell]
      (stripMotifCellArgumentsCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifCellArgumentsCode,
    stripMotifCellArgumentsCost, prependCost,
    Code.stripMotifState] using
    prepend
      (get 2
        (Code.stripMotifState width period valid
          (cell :: remaining)))
      (stripMotifPeriodAndCell width period valid
        cell remaining)

def stripMotifHeadInBoundsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  stripCellInBoundsCost width period cell +
    stripMotifCellArgumentsCost
      width period valid cell remaining

theorem stripMotifHeadInBounds
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      Code.stripMotifHeadInBoundsCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [if cell.InStripBounds width period then 1 else 0]
      (stripMotifHeadInBoundsCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifHeadInBoundsCode,
    stripMotifHeadInBoundsCost] using
    comp (stripCellInBounds width period cell)
      (stripMotifCellArguments width period valid
        cell remaining)

def stripMotifUpdatedValidCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  let cellTag :=
    if cell.InStripBounds width period then 1 else 0
  boolAndCost state valid.toNat cellTag
    (getCost 1 state)
    (stripMotifHeadInBoundsCost
      width period valid cell remaining)

theorem stripMotifUpdatedValid
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      Code.stripMotifUpdatedValidCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [(valid &&
        decide (cell.InStripBounds width period)).toNat]
      (stripMotifUpdatedValidCost
        width period valid cell remaining) := by
  have combined :=
    boolAnd
      (get 1
        (Code.stripMotifState width period valid
          (cell :: remaining)))
      (stripMotifHeadInBounds width period valid
        cell remaining)
  cases valid <;>
    by_cases inBounds :
      cell.InStripBounds width period <;>
    simpa [Code.stripMotifUpdatedValidCode,
      stripMotifUpdatedValidCost,
      Code.stripMotifState, inBounds] using combined

def stripMotifDimensionsCost
    (width period : Nat) (valid : Bool)
    (motif : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid motif
  prependCost state [width] [period]
    (getCost 2 state) (getCost 3 state)

theorem stripMotifDimensions
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) (Code.get 3))
      (Code.stripMotifState width period valid motif)
      [width, period]
      (stripMotifDimensionsCost
        width period valid motif) := by
  simpa [stripMotifDimensionsCost,
    prependCost, Code.stripMotifState] using
    prepend
      (get 2
        (Code.stripMotifState width period valid motif))
      (get 3
        (Code.stripMotifState width period valid motif))

def stripMotifValidAndDimensionsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  let nextValid :=
    valid && decide (cell.InStripBounds width period)
  prependCost state [nextValid.toNat] [width, period]
    (stripMotifUpdatedValidCost
      width period valid cell remaining)
    (stripMotifDimensionsCost
      width period valid (cell :: remaining))

theorem stripMotifValidAndDimensions
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    let nextValid :=
      valid && decide (cell.InStripBounds width period)
    EvaluatorCodeFits
      (Code.prepend Code.stripMotifUpdatedValidCode
        (Code.prepend (Code.get 2) (Code.get 3)))
      (Code.stripMotifState width period valid
        (cell :: remaining))
      [nextValid.toNat, width, period]
      (stripMotifValidAndDimensionsCost
        width period valid cell remaining) := by
  simpa [stripMotifValidAndDimensionsCost,
    prependCost] using
    prepend
      (stripMotifUpdatedValid width period valid
        cell remaining)
      (stripMotifDimensions width period valid
        (cell :: remaining))

def stripMotifConsStepCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.stripMotifState width period valid
      (cell :: remaining)
  let nextValid :=
    valid && decide (cell.InStripBounds width period)
  prependCost state [Encodable.encode remaining]
    [nextValid.toNat, width, period]
    (stripMotifTailCost
      width period valid cell remaining)
    (stripMotifValidAndDimensionsCost
      width period valid cell remaining)

theorem stripMotifConsStep
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    let nextValid :=
      valid && decide (cell.InStripBounds width period)
    EvaluatorCodeFits Code.stripMotifConsStepCode
      (Code.stripMotifState width period valid
        (cell :: remaining))
      (Code.stripMotifState width period
        nextValid remaining)
      (stripMotifConsStepCost
        width period valid cell remaining) := by
  simpa [Code.stripMotifConsStepCode,
    stripMotifConsStepCost, prependCost,
    Code.stripMotifState] using
    prepend
      (stripMotifTail width period valid
        cell remaining)
      (stripMotifValidAndDimensions width period valid
        cell remaining)

def stripMotifStepCost
    (width period : Nat) (valid : Bool) :
    List Cell → Nat
  | [] =>
      let state :=
        Code.stripMotifState width period valid []
      branchZeroZeroCost state state 0
        (getCost 0 state) (idCost state)
  | cell :: remaining =>
      let state :=
        Code.stripMotifState width period valid
          (cell :: remaining)
      let nextValid :=
        valid && decide (cell.InStripBounds width period)
      branchZeroSuccCost state
        (Code.stripMotifState width period
          nextValid remaining)
        (Encodable.encode (cell :: remaining))
        (getCost 0 state)
        (stripMotifConsStepCost
          width period valid cell remaining)

theorem stripMotifStep
    (width period : Nat) (valid : Bool)
    (motif : List Cell) :
    EvaluatorCodeFits Code.stripMotifStepCode
      (Code.stripMotifState width period valid motif)
      (Code.stripMotifNativeStep
        (Code.stripMotifState width period valid motif))
      (stripMotifStepCost
        width period valid motif) := by
  cases motif with
  | nil =>
      simpa [Code.stripMotifStepCode,
        stripMotifStepCost] using
        branchZero_zero rfl
          (get 0
            (Code.stripMotifState width period valid []))
          (id
            (Code.stripMotifState width period valid []))
  | cons cell remaining =>
      have positive :
          0 < Encodable.encode (cell :: remaining) := by
        simp
      simpa [Code.stripMotifStepCode,
        stripMotifStepCost] using
        branchZero_succ positive
          (get 0
            (Code.stripMotifState width period valid
              (cell :: remaining)))
          (stripMotifConsStep width period valid
            cell remaining)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
