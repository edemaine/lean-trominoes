import LeanTrominoes.PartrecFlatPackedAssignmentAt
import LeanTrominoes.PartrecFlatPackedLookupColumnSpace

/-!
# Evaluator-space certificate for five-column flat packed lookup

This module composes the exact one-column flat scanner certificate through the
five assignment columns.  The coordinate stream remains in native flat fields
throughout; each numbered stage restores it after updating the packed word,
selected digit, and found flag.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def flatPackedAssignmentColumnSelectedCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target accumulator
  natEqCost queriedColumn currentColumn +
    prependCost state [queriedColumn] [currentColumn]
      (getCost 1 state) (numeralCost currentColumn state)

theorem flatPackedAssignmentColumnSelected
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.flatPackedAssignmentColumnSelectedCode currentColumn)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        accumulator)
      [(decide (queriedColumn = currentColumn)).toNat]
      (flatPackedAssignmentColumnSelectedCost currentColumn motif
        queriedColumn target accumulator) := by
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target accumulator
  have arguments := prepend (get 1 state) (numeral currentColumn state)
  have selected := comp (natEq queriedColumn currentColumn) arguments
  by_cases equal : queriedColumn = currentColumn
  · subst queriedColumn
    simpa [Code.flatPackedAssignmentColumnSelectedCode,
      flatPackedAssignmentColumnSelectedCost, prependCost,
      Code.flatPackedAssignmentLookupState, state] using selected
  · simpa [Code.flatPackedAssignmentColumnSelectedCode,
      flatPackedAssignmentColumnSelectedCost, prependCost,
      Code.flatPackedAssignmentLookupState, state, equal] using selected

def flatPackedAssignmentColumnInputCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target accumulator
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let selected := (decide (queriedColumn = currentColumn)).toNat
  let rest7 := prependCost state [selected] coordinates
    (flatPackedAssignmentColumnSelectedCost currentColumn motif
      queriedColumn target accumulator) (dropCost 7 state)
  let rest6 := prependCost state [accumulator.2.2.toNat]
    (selected :: coordinates) (getCost 6 state) rest7
  let rest5 := prependCost state [accumulator.2.1]
    (accumulator.2.2.toNat :: selected :: coordinates)
    (getCost 5 state) rest6
  let rest4 := prependCost state [accumulator.1]
    (accumulator.2.1 :: accumulator.2.2.toNat :: selected :: coordinates)
    (getCost 4 state) rest5
  let rest3 := prependCost state [Encodable.encode target.2]
    (accumulator.1 :: accumulator.2.1 :: accumulator.2.2.toNat ::
      selected :: coordinates) (getCost 3 state) rest4
  let rest2 := prependCost state [Encodable.encode target.1]
    (Encodable.encode target.2 :: accumulator.1 :: accumulator.2.1 ::
      accumulator.2.2.toNat :: selected :: coordinates)
    (getCost 2 state) rest3
  prependCost state [motif.length]
    (Encodable.encode target.1 :: Encodable.encode target.2 ::
      accumulator.1 :: accumulator.2.1 :: accumulator.2.2.toNat ::
      selected :: coordinates) (getCost 0 state) rest2

theorem flatPackedAssignmentColumnInput
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.flatPackedAssignmentColumnInputCode currentColumn)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        accumulator)
      (motif.length :: Code.flatPackedLookupColumnState target
        accumulator.1 accumulator.2.1 accumulator.2.2
        (decide (queriedColumn = currentColumn)) motif)
      (flatPackedAssignmentColumnInputCost currentColumn motif
        queriedColumn target accumulator) := by
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target accumulator
  have rest7 := prepend
    (flatPackedAssignmentColumnSelected currentColumn motif queriedColumn
      target accumulator)
    (drop 7 state)
  have rest6 := prepend (get 6 state) rest7
  have rest5 := prepend (get 5 state) rest6
  have rest4 := prepend (get 4 state) rest5
  have rest3 := prepend (get 3 state) rest4
  have rest2 := prepend (get 2 state) rest3
  have result := prepend (get 0 state) rest2
  simpa [Code.flatPackedAssignmentColumnInputCode,
    flatPackedAssignmentColumnInputCost,
    Code.flatPackedAssignmentLookupState,
    Code.flatPackedLookupColumnState, prependCost, state] using result

def flatPackedAssignmentColumnCallCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  flatPackedLookupFlatCost target
      (decide (queriedColumn = currentColumn)) motif
      accumulator.1 accumulator.2.1 accumulator.2.2 +
    flatPackedAssignmentColumnInputCost currentColumn motif queriedColumn
      target accumulator

theorem flatPackedAssignmentColumnCall
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.flatPackedAssignmentColumnCallCode currentColumn)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        accumulator)
      (Code.flatPackedLookupColumnProcess target
        (decide (queriedColumn = currentColumn)) motif
        accumulator.1 accumulator.2.1 accumulator.2.2)
      (flatPackedAssignmentColumnCallCost currentColumn motif
        queriedColumn target accumulator) := by
  simpa [Code.flatPackedAssignmentColumnCallCode,
    flatPackedAssignmentColumnCallCost] using
    comp
      (flatPackedLookupFlat target
        (decide (queriedColumn = currentColumn)) motif
        accumulator.1 accumulator.2.1 accumulator.2.2)
      (flatPackedAssignmentColumnInput currentColumn motif queriedColumn
        target accumulator)

def flatPackedAssignmentColumnResultFieldCost
    (currentColumn : Nat) (outputField : Fin 3) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let result := Code.flatPackedLookupColumnProcess target
    (decide (queriedColumn = currentColumn)) motif
    accumulator.1 accumulator.2.1 accumulator.2.2
  getCost (outputField.val + 2) result +
    flatPackedAssignmentColumnCallCost currentColumn motif queriedColumn
      target accumulator

theorem flatPackedAssignmentColumnResultField
    (currentColumn : Nat) (outputField : Fin 3) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.flatPackedAssignmentColumnResultFieldCode
        currentColumn outputField)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        accumulator)
      [(Code.flatPackedAssignmentAccumulatorFields
        (Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator))[outputField.val]?.getD 0]
      (flatPackedAssignmentColumnResultFieldCost currentColumn outputField
        motif queriedColumn target accumulator) := by
  let final := Code.flatPackedLookupColumnProcess target
    (decide (queriedColumn = currentColumn)) motif
    accumulator.1 accumulator.2.1 accumulator.2.2
  let outcome := Code.packedAssignmentLookupApplyColumn currentColumn motif
    queriedColumn target accumulator
  have fitted := comp
    (get (outputField.val + 2) final)
    (flatPackedAssignmentColumnCall currentColumn motif queriedColumn
      target accumulator)
  have fields :
      [final[2]?.getD 0, final[3]?.getD 0, final[4]?.getD 0] =
        Code.flatPackedAssignmentAccumulatorFields outcome := by
    simpa [final, outcome,
      Code.flatPackedAssignmentAccumulatorFields,
      Code.packedAssignmentLookupApplyColumn] using
      (Code.flatPackedLookupColumnProcess_outcome_fields
        target (decide (queriedColumn = currentColumn)) motif
        accumulator.1 accumulator.2.1 accumulator.2.2)
  have indexed := congrArg
    (fun values => values[outputField.val]?.getD 0) fields
  have outputEq :
      final[outputField.val + 2]?.getD 0 =
        (Code.flatPackedAssignmentAccumulatorFields outcome)[outputField.val]?.getD 0 := by
    fin_cases outputField <;> simpa using indexed
  simpa [Code.flatPackedAssignmentColumnResultFieldCode,
    flatPackedAssignmentColumnResultFieldCost, final, outcome, outputEq] using fitted

def flatPackedAssignmentColumnStageCost
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat :=
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target accumulator
  let next := Code.packedAssignmentLookupApplyColumn currentColumn motif
    queriedColumn target accumulator
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let rest7 := prependCost state [next.2.2.toNat] coordinates
    (flatPackedAssignmentColumnResultFieldCost currentColumn (2 : Fin 3)
      motif queriedColumn target accumulator) (dropCost 7 state)
  let rest6 := prependCost state [next.2.1]
    (next.2.2.toNat :: coordinates)
    (flatPackedAssignmentColumnResultFieldCost currentColumn (1 : Fin 3)
      motif queriedColumn target accumulator) rest7
  let rest5 := prependCost state [next.1]
    (next.2.1 :: next.2.2.toNat :: coordinates)
    (flatPackedAssignmentColumnResultFieldCost currentColumn (0 : Fin 3)
      motif queriedColumn target accumulator) rest6
  let rest3 := prependCost state [Encodable.encode target.2]
    (next.1 :: next.2.1 :: next.2.2.toNat :: coordinates)
    (getCost 3 state) rest5
  let rest2 := prependCost state [Encodable.encode target.1]
    (Encodable.encode target.2 :: next.1 :: next.2.1 ::
      next.2.2.toNat :: coordinates) (getCost 2 state) rest3
  let rest1 := prependCost state [queriedColumn]
    (Encodable.encode target.1 :: Encodable.encode target.2 :: next.1 ::
      next.2.1 :: next.2.2.toNat :: coordinates) (getCost 1 state) rest2
  prependCost state [motif.length]
    (queriedColumn :: Encodable.encode target.1 ::
      Encodable.encode target.2 :: next.1 :: next.2.1 ::
      next.2.2.toNat :: coordinates) (getCost 0 state) rest1

theorem flatPackedAssignmentColumnStage
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    EvaluatorCodeFits
      (Code.flatPackedAssignmentColumnStageCode currentColumn)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        accumulator)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        (Code.packedAssignmentLookupApplyColumn currentColumn motif
          queriedColumn target accumulator))
      (flatPackedAssignmentColumnStageCost currentColumn motif
        queriedColumn target accumulator) := by
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target accumulator
  have rest7 := prepend
    (flatPackedAssignmentColumnResultField currentColumn (2 : Fin 3) motif
      queriedColumn target accumulator)
    (drop 7 state)
  have rest6 := prepend
    (flatPackedAssignmentColumnResultField currentColumn (1 : Fin 3) motif
      queriedColumn target accumulator) rest7
  have rest5 := prepend
    (flatPackedAssignmentColumnResultField currentColumn (0 : Fin 3) motif
      queriedColumn target accumulator) rest6
  have rest3 := prepend (get 3 state) rest5
  have rest2 := prepend (get 2 state) rest3
  have rest1 := prepend (get 1 state) rest2
  have result := prepend (get 0 state) rest1
  simpa [Code.flatPackedAssignmentColumnStageCode,
    flatPackedAssignmentColumnStageCost,
    Code.flatPackedAssignmentLookupState,
    Code.flatPackedAssignmentAccumulatorFields, prependCost, state] using result

def flatPackedAssignmentLookupStagesCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first := Code.packedAssignmentLookupApplyColumn
    0 motif queriedColumn target initial
  let second := Code.packedAssignmentLookupApplyColumn
    1 motif queriedColumn target first
  let third := Code.packedAssignmentLookupApplyColumn
    2 motif queriedColumn target second
  let fourth := Code.packedAssignmentLookupApplyColumn
    3 motif queriedColumn target third
  flatPackedAssignmentColumnStageCost 4 motif queriedColumn target fourth +
    (flatPackedAssignmentColumnStageCost 3 motif queriedColumn target third +
      (flatPackedAssignmentColumnStageCost 2 motif queriedColumn target second +
        (flatPackedAssignmentColumnStageCost 1 motif queriedColumn target first +
          flatPackedAssignmentColumnStageCost 0 motif queriedColumn target
            initial)))

theorem flatPackedAssignmentLookupStages
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentLookupStagesCode
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        (word, 0, false))
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        (Code.packedAssignmentLookupOutcome motif queriedColumn target word))
      (flatPackedAssignmentLookupStagesCost motif queriedColumn target word) := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first := Code.packedAssignmentLookupApplyColumn
    0 motif queriedColumn target initial
  let second := Code.packedAssignmentLookupApplyColumn
    1 motif queriedColumn target first
  let third := Code.packedAssignmentLookupApplyColumn
    2 motif queriedColumn target second
  let fourth := Code.packedAssignmentLookupApplyColumn
    3 motif queriedColumn target third
  have firstTwo := comp
    (flatPackedAssignmentColumnStage 1 motif queriedColumn target first)
    (flatPackedAssignmentColumnStage 0 motif queriedColumn target initial)
  have firstThree := comp
    (flatPackedAssignmentColumnStage 2 motif queriedColumn target second)
    firstTwo
  have firstFour := comp
    (flatPackedAssignmentColumnStage 3 motif queriedColumn target third)
    firstThree
  have allFive := comp
    (flatPackedAssignmentColumnStage 4 motif queriedColumn target fourth)
    firstFour
  simpa [Code.flatPackedAssignmentLookupStagesCode,
    flatPackedAssignmentLookupStagesCost,
    Code.packedAssignmentLookupOutcome,
    initial, first, second, third, fourth] using allFive

def flatPackedAssignmentLookupInputCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values := [motif.length, queriedColumn,
    Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let rest7 := prependCost values [0] coordinates
    (zeroCost values) (dropCost 5 values)
  let rest6 := prependCost values [0] (0 :: coordinates)
    (zeroCost values) rest7
  let rest4 := prependCost values [word] (0 :: 0 :: coordinates)
    (getCost 4 values) rest6
  let rest3 := prependCost values [Encodable.encode target.2]
    (word :: 0 :: 0 :: coordinates) (getCost 3 values) rest4
  let rest2 := prependCost values [Encodable.encode target.1]
    (Encodable.encode target.2 :: word :: 0 :: 0 :: coordinates)
    (getCost 2 values) rest3
  let rest1 := prependCost values [queriedColumn]
    (Encodable.encode target.1 :: Encodable.encode target.2 :: word ::
      0 :: 0 :: coordinates) (getCost 1 values) rest2
  prependCost values [motif.length]
    (queriedColumn :: Encodable.encode target.1 ::
      Encodable.encode target.2 :: word :: 0 :: 0 :: coordinates)
    (getCost 0 values) rest1

theorem flatPackedAssignmentLookupInput
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentLookupInputCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (Code.flatPackedAssignmentLookupState motif queriedColumn target
        (word, 0, false))
      (flatPackedAssignmentLookupInputCost motif queriedColumn target word) := by
  let values := [motif.length, queriedColumn,
    Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  have rest7 := prepend (zero values) (drop 5 values)
  have rest6 := prepend (zero values) rest7
  have rest4 := prepend (get 4 values) rest6
  have rest3 := prepend (get 3 values) rest4
  have rest2 := prepend (get 2 values) rest3
  have rest1 := prepend (get 1 values) rest2
  have result := prepend (get 0 values) rest1
  simpa [Code.flatPackedAssignmentLookupInputCode,
    flatPackedAssignmentLookupInputCost,
    Code.flatPackedAssignmentLookupState, prependCost, values] using result

def flatPackedAssignmentLookupProjectionCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (outcome : Nat × Nat × Bool) : Nat :=
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target outcome
  prependCost state [outcome.2.1] [outcome.2.2.toNat]
    (getCost 5 state) (getCost 6 state)

theorem flatPackedAssignmentLookupProjection
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (outcome : Nat × Nat × Bool) :
    EvaluatorCodeFits (Code.prepend (Code.get 5) (Code.get 6))
      (Code.flatPackedAssignmentLookupState motif queriedColumn target outcome)
      [outcome.2.1, outcome.2.2.toNat]
      (flatPackedAssignmentLookupProjectionCost motif queriedColumn
        target outcome) := by
  let state := Code.flatPackedAssignmentLookupState motif queriedColumn
    target outcome
  simpa [flatPackedAssignmentLookupProjectionCost,
    Code.flatPackedAssignmentLookupState, prependCost, state] using
    prepend (get 5 state) (get 6 state)

def flatPackedAssignmentLookupCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn
    target word
  flatPackedAssignmentLookupProjectionCost motif queriedColumn target outcome +
    (flatPackedAssignmentLookupStagesCost motif queriedColumn target word +
      flatPackedAssignmentLookupInputCost motif queriedColumn target word)

/-- The complete five-column lookup has an exact additive evaluator-space
certificate over the native flat motif representation. -/
theorem flatPackedAssignmentLookup
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentLookupCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [(Code.packedAssignmentLookupOutcome motif queriedColumn target word).2.1,
        (Code.packedAssignmentLookupOutcome motif queriedColumn target
          word).2.2.toNat]
      (flatPackedAssignmentLookupCost motif queriedColumn target word) := by
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn
    target word
  have stages := comp
    (flatPackedAssignmentLookupStages motif queriedColumn target word)
    (flatPackedAssignmentLookupInput motif queriedColumn target word)
  have result := comp
    (flatPackedAssignmentLookupProjection motif queriedColumn target outcome)
    stages
  simpa [Code.flatPackedAssignmentLookupCode,
    flatPackedAssignmentLookupCost, outcome] using result

end EvaluatorCodeFits
end PartrecToTM2
end Turing
