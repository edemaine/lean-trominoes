import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecFrontierIndexDecodeSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecFlatPackedLookupColumn

/-!
# Evaluator-space certificates for one flat packed lookup pass

This module fits every component of one coordinate-pair lookup step.  The
scanner keeps its target and accumulator fields in front of the unconsumed
native coordinate suffix, so no recursively paired motif code is introduced.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def flatPackedLookupXEqualityArgumentsCost
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  prependCost state [Encodable.encode cell.1]
    [Encodable.encode target.1] (getCost 6 state) (getCost 0 state)

theorem flatPackedLookupXEqualityArguments
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 6) (Code.get 0))
      (Code.flatPackedLookupColumnState target word digit
        found selected (cell :: remaining))
      [Encodable.encode cell.1, Encodable.encode target.1]
      (flatPackedLookupXEqualityArgumentsCost target cell word digit
        found selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  simpa [flatPackedLookupXEqualityArgumentsCost, state, prependCost,
    Code.flatPackedLookupColumnState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 6 state) (get 0 state)

def flatPackedLookupXEqualityCost
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) : Nat :=
  natEqCost (Encodable.encode cell.1) (Encodable.encode target.1) +
    flatPackedLookupXEqualityArgumentsCost target cell word digit
      found selected remaining

theorem flatPackedLookupXEquality
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupXEqualityCode
      (Code.flatPackedLookupColumnState target word digit
        found selected (cell :: remaining))
      [(decide (cell.1 = target.1)).toNat]
      (flatPackedLookupXEqualityCost target cell word digit
        found selected remaining) := by
  have fitted := comp
    (natEq (Encodable.encode cell.1) (Encodable.encode target.1))
    (flatPackedLookupXEqualityArguments target cell word digit
      found selected remaining)
  by_cases equal : cell.1 = target.1
  · simp [Code.flatPackedLookupXEqualityCode,
      flatPackedLookupXEqualityCost, equal] at fitted ⊢
    exact fitted
  · have encodedNe :
        Encodable.encode cell.1 ≠ Encodable.encode target.1 := by
      intro encodedEqual
      exact equal (Encodable.encode_injective encodedEqual)
    simp [Code.flatPackedLookupXEqualityCode,
      flatPackedLookupXEqualityCost, equal, encodedNe] at fitted ⊢
    exact fitted

def flatPackedLookupYEqualityArgumentsCost
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  prependCost state [Encodable.encode cell.2]
    [Encodable.encode target.2] (getCost 7 state) (getCost 1 state)

theorem flatPackedLookupYEqualityArguments
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 7) (Code.get 1))
      (Code.flatPackedLookupColumnState target word digit
        found selected (cell :: remaining))
      [Encodable.encode cell.2, Encodable.encode target.2]
      (flatPackedLookupYEqualityArgumentsCost target cell word digit
        found selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  simpa [flatPackedLookupYEqualityArgumentsCost, state, prependCost,
    Code.flatPackedLookupColumnState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 7 state) (get 1 state)

def flatPackedLookupYEqualityCost
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) : Nat :=
  natEqCost (Encodable.encode cell.2) (Encodable.encode target.2) +
    flatPackedLookupYEqualityArgumentsCost target cell word digit
      found selected remaining

theorem flatPackedLookupYEquality
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupYEqualityCode
      (Code.flatPackedLookupColumnState target word digit
        found selected (cell :: remaining))
      [(decide (cell.2 = target.2)).toNat]
      (flatPackedLookupYEqualityCost target cell word digit
        found selected remaining) := by
  have fitted := comp
    (natEq (Encodable.encode cell.2) (Encodable.encode target.2))
    (flatPackedLookupYEqualityArguments target cell word digit
      found selected remaining)
  by_cases equal : cell.2 = target.2
  · simp [Code.flatPackedLookupYEqualityCode,
      flatPackedLookupYEqualityCost, equal] at fitted ⊢
    exact fitted
  · have encodedNe :
        Encodable.encode cell.2 ≠ Encodable.encode target.2 := by
      intro encodedEqual
      exact equal (Encodable.encode_injective encodedEqual)
    simp [Code.flatPackedLookupYEqualityCode,
      flatPackedLookupYEqualityCost, equal, encodedNe] at fitted ⊢
    exact fitted

def flatPackedLookupCoordinateMatchCost
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  boolAndCost state
    (decide (cell.1 = target.1)).toNat
    (decide (cell.2 = target.2)).toNat
    (flatPackedLookupXEqualityCost target cell word digit
      found selected remaining)
    (flatPackedLookupYEqualityCost target cell word digit
      found selected remaining)

theorem flatPackedLookupCoordinateMatch
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.boolAnd Code.flatPackedLookupXEqualityCode
        Code.flatPackedLookupYEqualityCode)
      (Code.flatPackedLookupColumnState target word digit
        found selected (cell :: remaining))
      [(decide (cell = target)).toNat]
      (flatPackedLookupCoordinateMatchCost target cell word digit
        found selected remaining) := by
  have fitted := boolAnd
    (flatPackedLookupXEquality target cell word digit
      found selected remaining)
    (flatPackedLookupYEquality target cell word digit
      found selected remaining)
  rcases target with ⟨targetX, targetY⟩
  rcases cell with ⟨cellX, cellY⟩
  by_cases xEqual : cellX = targetX <;>
    by_cases yEqual : cellY = targetY <;>
    simp [flatPackedLookupCoordinateMatchCost,
      xEqual, yEqual] at fitted ⊢ <;>
    exact fitted

def flatPackedLookupMatchCost
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  boolAndCost state selected.toNat (decide (cell = target)).toNat
    (getCost 5 state)
    (flatPackedLookupCoordinateMatchCost target cell word digit
      found selected remaining)

theorem flatPackedLookupMatch
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupMatchCode
      (Code.flatPackedLookupColumnState target word digit
        found selected (cell :: remaining))
      [(selected && decide (cell = target)).toNat]
      (flatPackedLookupMatchCost target cell word digit
        found selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  have fitted := boolAnd (get 5 state)
    (flatPackedLookupCoordinateMatch target cell word digit
      found selected remaining)
  cases selected <;>
    by_cases equal : cell = target <;>
    simp [Code.flatPackedLookupMatchCode,
      flatPackedLookupMatchCost, state, equal] at fitted ⊢ <;>
    exact fitted

def flatPackedLookupContinueCost
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let rest5 := prependCost state [selected.toNat]
    (remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 5 state) (dropCost 8 state)
  let rest4 := prependCost state [0]
    (selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 4 state) rest5
  let rest3 := prependCost state [digit]
    (0 :: selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 3 state) rest4
  let rest2 := prependCost state [word / 9]
    (digit :: 0 :: selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (assignmentWordStepFieldAtCost 2 0 state) rest3
  let rest1 := prependCost state [Encodable.encode target.2]
    (word / 9 :: digit :: 0 :: selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 1 state) rest2
  prependCost state [Encodable.encode target.1]
    (Encodable.encode target.2 :: word / 9 :: digit :: 0 ::
      selected.toNat ::
        remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 0 state) rest1

theorem flatPackedLookupContinue
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupContinueCode
      (Code.flatPackedLookupColumnState target word digit
        false selected (cell :: remaining))
      (Code.flatPackedLookupColumnState target (word / 9) digit
        false selected remaining)
      (flatPackedLookupContinueCost target cell word digit
        selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  have rest5 := prepend (get 5 state) (drop 8 state)
  have rest4 := prepend (get 4 state) rest5
  have rest3 := prepend (get 3 state) rest4
  have rest2 := prepend (assignmentWordStepFieldAt 2 0 state) rest3
  have rest1 := prepend (get 1 state) rest2
  have result := prepend (get 0 state) rest1
  simpa [Code.flatPackedLookupContinueCode,
    flatPackedLookupContinueCost, Code.flatPackedLookupColumnState,
    PeriodicStripFlatEncoding.cellFields, prependCost, state] using result

def flatPackedLookupFoundCost
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let rest5 := prependCost state [selected.toNat]
    (remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 5 state) (dropCost 8 state)
  let rest4 := prependCost state [1]
    (selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (oneCost state) rest5
  let rest3 := prependCost state [word % 9]
    (1 :: selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (assignmentWordStepFieldAtCost 2 1 state) rest4
  let rest2 := prependCost state [word / 9]
    (word % 9 :: 1 :: selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (assignmentWordStepFieldAtCost 2 0 state) rest3
  let rest1 := prependCost state [Encodable.encode target.2]
    (word / 9 :: word % 9 :: 1 :: selected.toNat ::
      remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 1 state) rest2
  prependCost state [Encodable.encode target.1]
    (Encodable.encode target.2 :: word / 9 :: word % 9 :: 1 ::
      selected.toNat ::
        remaining.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 0 state) rest1

theorem flatPackedLookupFound
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupFoundCode
      (Code.flatPackedLookupColumnState target word digit
        false selected (cell :: remaining))
      (Code.flatPackedLookupColumnState target (word / 9) (word % 9)
        true selected remaining)
      (flatPackedLookupFoundCost target cell word digit
        selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  have rest5 := prepend (get 5 state) (drop 8 state)
  have rest4 := prepend (one state) rest5
  have rest3 := prepend (assignmentWordStepFieldAt 2 1 state) rest4
  have rest2 := prepend (assignmentWordStepFieldAt 2 0 state) rest3
  have rest1 := prepend (get 1 state) rest2
  have result := prepend (get 0 state) rest1
  simpa [Code.flatPackedLookupFoundCode,
    flatPackedLookupFoundCost, Code.flatPackedLookupColumnState,
    PeriodicStripFlatEncoding.cellFields, prependCost, state] using result

def flatPackedLookupConsStepCost
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  if selected && decide (cell = target) then
    branchZeroSuccCost state
      (Code.flatPackedLookupColumnState target (word / 9) (word % 9)
        true selected remaining)
      1 (flatPackedLookupMatchCost target cell word digit
        false selected remaining)
      (flatPackedLookupFoundCost target cell word digit selected remaining)
  else
    branchZeroZeroCost state
      (Code.flatPackedLookupColumnState target (word / 9) digit
        false selected remaining)
      0 (flatPackedLookupMatchCost target cell word digit
        false selected remaining)
      (flatPackedLookupContinueCost target cell word digit
        selected remaining)

theorem flatPackedLookupConsStep
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupConsStepCode
      (Code.flatPackedLookupColumnState target word digit
        false selected (cell :: remaining))
      (if selected && decide (cell = target) then
        Code.flatPackedLookupColumnState target
          (word / 9) (word % 9) true selected remaining
      else
        Code.flatPackedLookupColumnState target
          (word / 9) digit false selected remaining)
      (flatPackedLookupConsStepCost target cell word digit
        selected remaining) := by
  by_cases hit : selected && decide (cell = target)
  · simpa [Code.flatPackedLookupConsStepCode,
      flatPackedLookupConsStepCost, hit] using
      branchZero_succ (show 0 < (selected && decide (cell = target)).toNat by
        simp [hit])
        (flatPackedLookupMatch target cell word digit
          false selected remaining)
        (flatPackedLookupFound target cell word digit selected remaining)
  · simpa [Code.flatPackedLookupConsStepCode,
      flatPackedLookupConsStepCost, hit] using
      branchZero_zero (show (selected && decide (cell = target)).toNat = 0 by
        simp [hit])
        (flatPackedLookupMatch target cell word digit
          false selected remaining)
        (flatPackedLookupContinue target cell word digit selected remaining)

def flatPackedLookupStepFoundCost
    (target : Cell) (word digit : Nat) (selected : Bool)
    (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    true selected remaining
  branchZeroSuccCost state state 1
    (getCost 4 state) (idCost state)

theorem flatPackedLookupStepFound
    (target : Cell) (word digit : Nat) (selected : Bool)
    (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupStepCode
      (Code.flatPackedLookupColumnState target word digit
        true selected remaining)
      (Code.flatPackedLookupColumnState target word digit
        true selected remaining)
      (flatPackedLookupStepFoundCost target word digit
        selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    true selected remaining
  simpa [Code.flatPackedLookupStepCode,
    flatPackedLookupStepFoundCost, state] using
    branchZero_succ (show 0 < (true : Bool).toNat by decide)
      (get 4 state) (id state)

def flatPackedLookupStepConsCost
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let output := if selected && decide (cell = target) then
      Code.flatPackedLookupColumnState target
        (word / 9) (word % 9) true selected remaining
    else
      Code.flatPackedLookupColumnState target
        (word / 9) digit false selected remaining
  branchZeroZeroCost state output 0 (getCost 4 state)
    (flatPackedLookupConsStepCost target cell word digit
      selected remaining)

theorem flatPackedLookupStepCons
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatPackedLookupStepCode
      (Code.flatPackedLookupColumnState target word digit
        false selected (cell :: remaining))
      (if selected && decide (cell = target) then
        Code.flatPackedLookupColumnState target
          (word / 9) (word % 9) true selected remaining
      else
        Code.flatPackedLookupColumnState target
          (word / 9) digit false selected remaining)
      (flatPackedLookupStepConsCost target cell word digit
        selected remaining) := by
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  simpa [Code.flatPackedLookupStepCode,
    flatPackedLookupStepConsCost, state] using
    branchZero_zero (show (false : Bool).toNat = 0 by rfl)
      (get 4 state)
      (flatPackedLookupConsStep target cell word digit selected remaining)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
