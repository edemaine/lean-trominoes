import LeanTrominoes.PartrecPackedAssignmentAt
import LeanTrominoes.PartrecPackedAssignmentLookupSpace

/-!
# Evaluator-space certificate for five-column packed lookup

The number of frontier columns is the fixed constant five.  This module fits
one numbered stage compositionally and then unrolls five copies.  Every scan
reuses the uniform one-column workspace certificate; the repeated field
projections affect only the constant factor.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedAssignmentLookupColumnEqArgumentsCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  prependCost state [queriedColumn] [currentColumn]
    (getCost 1 state) (numeralCost currentColumn state)

theorem packedAssignmentLookupColumnEqArguments
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnEqArgumentsCode
        currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [queriedColumn, currentColumn]
      (packedAssignmentLookupColumnEqArgumentsCost
        currentColumn motif queriedColumn target accumulator) := by
  simpa [Code.packedAssignmentLookupColumnEqArgumentsCode,
    packedAssignmentLookupColumnEqArgumentsCost,
    prependCost, Code.packedAssignmentLookupState] using
    prepend
      (get 1
        (Code.packedAssignmentLookupState motif queriedColumn
          target accumulator))
      (numeral currentColumn
        (Code.packedAssignmentLookupState motif queriedColumn
          target accumulator))

def packedAssignmentLookupColumnSelectedCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  natEqCost queriedColumn currentColumn +
    packedAssignmentLookupColumnEqArgumentsCost
      currentColumn motif queriedColumn target accumulator

theorem packedAssignmentLookupColumnSelected
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnSelectedCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [(decide (queriedColumn = currentColumn)).toNat]
      (packedAssignmentLookupColumnSelectedCost
        currentColumn motif queriedColumn target accumulator) := by
  have selected :=
    comp (natEq queriedColumn currentColumn)
      (packedAssignmentLookupColumnEqArguments
        currentColumn motif queriedColumn target accumulator)
  by_cases equal : queriedColumn = currentColumn
  · subst queriedColumn
    simpa [Code.packedAssignmentLookupColumnSelectedCode,
      packedAssignmentLookupColumnSelectedCost] using selected
  · simpa [Code.packedAssignmentLookupColumnSelectedCode,
      packedAssignmentLookupColumnSelectedCost, equal] using selected

def packedAssignmentLookupColumnInputCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  let selected :=
    (decide (queriedColumn = currentColumn)).toNat
  let rest5 :=
    prependCost state [accumulator.2.2.toNat] [selected]
      (getCost 5 state)
      (packedAssignmentLookupColumnSelectedCost
        currentColumn motif queriedColumn target accumulator)
  let rest4 :=
    prependCost state [accumulator.2.1]
      [accumulator.2.2.toNat, selected]
      (getCost 4 state) rest5
  let rest3 :=
    prependCost state [accumulator.1]
      [accumulator.2.1, accumulator.2.2.toNat, selected]
      (getCost 3 state) rest4
  let rest2 :=
    prependCost state [Encodable.encode target]
      [accumulator.1, accumulator.2.1,
        accumulator.2.2.toNat, selected]
      (getCost 2 state) rest3
  prependCost state [Encodable.encode motif]
    [Encodable.encode target, accumulator.1,
      accumulator.2.1, accumulator.2.2.toNat, selected]
    (getCost 0 state) rest2

theorem packedAssignmentLookupColumnInput
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnInputCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [Encodable.encode motif, Encodable.encode target,
        accumulator.1, accumulator.2.1,
        accumulator.2.2.toNat,
        (decide (queriedColumn = currentColumn)).toNat]
      (packedAssignmentLookupColumnInputCost
        currentColumn motif queriedColumn target accumulator) := by
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  have rest5 :=
    prepend (get 5 state)
      (packedAssignmentLookupColumnSelected currentColumn motif
        queriedColumn target accumulator)
  have rest4 := prepend (get 4 state) rest5
  have rest3 := prepend (get 3 state) rest4
  have rest2 := prepend (get 2 state) rest3
  have result := prepend (get 0 state) rest2
  simpa [Code.packedAssignmentLookupColumnInputCode,
    packedAssignmentLookupColumnInputCost,
    Code.packedAssignmentLookupState, prependCost,
    state] using result

def packedAssignmentLookupColumnCallCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let selected := decide (queriedColumn = currentColumn)
  packedLookupColumnCodeCost motif target
      accumulator.1 accumulator.2.1 accumulator.2.2 selected +
    packedAssignmentLookupColumnInputCost currentColumn motif
      queriedColumn target accumulator

theorem packedAssignmentLookupColumnCall
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnCallCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      (Code.packedLookupColumnResult motif target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide (queriedColumn = currentColumn)))
      (packedAssignmentLookupColumnCallCost
        currentColumn motif queriedColumn target accumulator) := by
  simpa [Code.packedAssignmentLookupColumnCallCode,
    packedAssignmentLookupColumnCallCost] using
    comp
      (packedLookupColumn motif target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide (queriedColumn = currentColumn)))
      (packedAssignmentLookupColumnInput currentColumn motif
        queriedColumn target accumulator)

def packedAssignmentLookupColumnResultFieldCost
    (currentColumn outputField : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let result :=
    Code.packedLookupColumnResult motif target
      accumulator.1 accumulator.2.1 accumulator.2.2
      (decide (queriedColumn = currentColumn))
  getCost outputField result +
    packedAssignmentLookupColumnCallCost currentColumn motif
      queriedColumn target accumulator

theorem packedAssignmentLookupColumnResultField
    (currentColumn outputField : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnResultFieldCode
        currentColumn outputField)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      [(Code.packedLookupColumnResult motif target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide
          (queriedColumn = currentColumn)))[outputField]?.getD 0]
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn outputField motif queriedColumn
        target accumulator) := by
  let result :=
    Code.packedLookupColumnResult motif target
      accumulator.1 accumulator.2.1 accumulator.2.2
      (decide (queriedColumn = currentColumn))
  simpa [Code.packedAssignmentLookupColumnResultFieldCode,
    packedAssignmentLookupColumnResultFieldCost, result] using
    comp (get outputField result)
      (packedAssignmentLookupColumnCall currentColumn motif
        queriedColumn target accumulator)

def packedAssignmentLookupColumnStageCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  let next :=
    Code.packedAssignmentLookupApplyColumn currentColumn motif
      queriedColumn target accumulator
  let rest6 :=
    prependCost state [next.2.1] [next.2.2.toNat]
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn 3 motif queriedColumn target accumulator)
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn 4 motif queriedColumn target accumulator)
  let rest5 :=
    prependCost state [next.1]
      [next.2.1, next.2.2.toNat]
      (packedAssignmentLookupColumnResultFieldCost
        currentColumn 2 motif queriedColumn target accumulator)
      rest6
  let rest3 :=
    prependCost state [Encodable.encode target]
      [next.1, next.2.1, next.2.2.toNat]
      (getCost 2 state) rest5
  let rest2 :=
    prependCost state [queriedColumn]
      [Encodable.encode target, next.1,
        next.2.1, next.2.2.toNat]
      (getCost 1 state) rest3
  prependCost state [Encodable.encode motif]
    [queriedColumn, Encodable.encode target,
      next.1, next.2.1, next.2.2.toNat]
    (getCost 0 state) rest2

theorem packedAssignmentLookupColumnStage
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.packedAssignmentLookupColumnStageCode currentColumn)
      (Code.packedAssignmentLookupState motif queriedColumn
        target accumulator)
      (Code.packedAssignmentLookupState motif queriedColumn target
        (Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator))
      (packedAssignmentLookupColumnStageCost
        currentColumn motif queriedColumn target accumulator) := by
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn
      target accumulator
  have rest6 :=
    prepend
      (packedAssignmentLookupColumnResultField currentColumn 3 motif
        queriedColumn target accumulator)
      (packedAssignmentLookupColumnResultField currentColumn 4 motif
        queriedColumn target accumulator)
  have rest5 :=
    prepend
      (packedAssignmentLookupColumnResultField currentColumn 2 motif
        queriedColumn target accumulator)
      rest6
  have rest3 := prepend (get 2 state) rest5
  have rest2 := prepend (get 1 state) rest3
  have result := prepend (get 0 state) rest2
  simpa [Code.packedAssignmentLookupColumnStageCode,
    packedAssignmentLookupColumnStageCost,
    Code.packedAssignmentLookupState,
    Code.packedAssignmentLookupApplyColumn,
    Code.packedLookupColumnResult_eq_outcome,
    prependCost, state] using result

def packedAssignmentLookupStagesCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    Code.packedAssignmentLookupApplyColumn 0 motif queriedColumn
      target initial
  let second :=
    Code.packedAssignmentLookupApplyColumn 1 motif queriedColumn
      target first
  let third :=
    Code.packedAssignmentLookupApplyColumn 2 motif queriedColumn
      target second
  let fourth :=
    Code.packedAssignmentLookupApplyColumn 3 motif queriedColumn
      target third
  packedAssignmentLookupColumnStageCost 4 motif queriedColumn
      target fourth +
    (packedAssignmentLookupColumnStageCost 3 motif queriedColumn
        target third +
      (packedAssignmentLookupColumnStageCost 2 motif queriedColumn
          target second +
        (packedAssignmentLookupColumnStageCost 1 motif queriedColumn
            target first +
          packedAssignmentLookupColumnStageCost 0 motif queriedColumn
            target initial)))

theorem packedAssignmentLookupStages
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupStagesCode
      (Code.packedAssignmentLookupState motif queriedColumn target
        (word, 0, false))
      (Code.packedAssignmentLookupState motif queriedColumn target
        (Code.packedAssignmentLookupOutcome motif queriedColumn
          target word))
      (packedAssignmentLookupStagesCost motif queriedColumn
        target word) := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    Code.packedAssignmentLookupApplyColumn 0 motif queriedColumn
      target initial
  let second :=
    Code.packedAssignmentLookupApplyColumn 1 motif queriedColumn
      target first
  let third :=
    Code.packedAssignmentLookupApplyColumn 2 motif queriedColumn
      target second
  let fourth :=
    Code.packedAssignmentLookupApplyColumn 3 motif queriedColumn
      target third
  have firstTwo :=
    comp
      (packedAssignmentLookupColumnStage 1 motif queriedColumn
        target first)
      (packedAssignmentLookupColumnStage 0 motif queriedColumn
        target initial)
  have firstThree :=
    comp
      (packedAssignmentLookupColumnStage 2 motif queriedColumn
        target second)
      firstTwo
  have firstFour :=
    comp
      (packedAssignmentLookupColumnStage 3 motif queriedColumn
        target third)
      firstThree
  have allFive :=
    comp
      (packedAssignmentLookupColumnStage 4 motif queriedColumn
        target fourth)
      firstFour
  simpa [Code.packedAssignmentLookupStagesCode,
    packedAssignmentLookupStagesCost,
    Code.packedAssignmentLookupOutcome,
    initial, first, second, third, fourth] using allFive

def packedAssignmentLookupInputCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  let rest6 :=
    prependCost values [0] [0]
      (zeroCost values) (zeroCost values)
  let rest5 :=
    prependCost values [word] [0, 0]
      (getCost 3 values) rest6
  let rest3 :=
    prependCost values [Encodable.encode target]
      [word, 0, 0]
      (getCost 2 values) rest5
  let rest2 :=
    prependCost values [queriedColumn]
      [Encodable.encode target, word, 0, 0]
      (getCost 1 values) rest3
  prependCost values [Encodable.encode motif]
    [queriedColumn, Encodable.encode target, word, 0, 0]
    (getCost 0 values) rest2

theorem packedAssignmentLookupInput
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupInputCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      (Code.packedAssignmentLookupState motif queriedColumn target
        (word, 0, false))
      (packedAssignmentLookupInputCost motif queriedColumn
        target word) := by
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  have rest6 := prepend (zero values) (zero values)
  have rest5 := prepend (get 3 values) rest6
  have rest3 := prepend (get 2 values) rest5
  have rest2 := prepend (get 1 values) rest3
  have result := prepend (get 0 values) rest2
  simpa [Code.packedAssignmentLookupInputCode,
    packedAssignmentLookupInputCost,
    Code.packedAssignmentLookupState,
    prependCost, values] using result

def packedAssignmentLookupProjectionCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (outcome : Nat × Nat × Bool) : Nat :=
  let state :=
    Code.packedAssignmentLookupState motif queriedColumn target outcome
  prependCost state [outcome.2.1] [outcome.2.2.toNat]
    (getCost 4 state) (getCost 5 state)

theorem packedAssignmentLookupProjection
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (outcome : Nat × Nat × Bool) :
    EvaluatorCodeFits (Code.prepend (Code.get 4) (Code.get 5))
      (Code.packedAssignmentLookupState motif queriedColumn
        target outcome)
      [outcome.2.1, outcome.2.2.toNat]
      (packedAssignmentLookupProjectionCost motif queriedColumn
        target outcome) := by
  simpa [packedAssignmentLookupProjectionCost,
    Code.packedAssignmentLookupState, prependCost] using
    prepend
      (get 4
        (Code.packedAssignmentLookupState motif queriedColumn
          target outcome))
      (get 5
        (Code.packedAssignmentLookupState motif queriedColumn
          target outcome))

def packedAssignmentLookupCodeCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  packedAssignmentLookupProjectionCost motif queriedColumn
      target outcome +
    (packedAssignmentLookupStagesCost motif queriedColumn target word +
      packedAssignmentLookupInputCost motif queriedColumn target word)

theorem packedAssignmentLookup
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [(Code.packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1,
        (Code.packedAssignmentLookupOutcome motif queriedColumn
          target word).2.2.toNat]
      (packedAssignmentLookupCodeCost motif queriedColumn
        target word) := by
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  have stages :=
    comp
      (packedAssignmentLookupStages motif queriedColumn target word)
      (packedAssignmentLookupInput motif queriedColumn target word)
  have result :=
    comp
      (packedAssignmentLookupProjection motif queriedColumn
        target outcome)
      stages
  simpa [Code.packedAssignmentLookupCode,
    packedAssignmentLookupCodeCost, outcome] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
