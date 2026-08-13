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

/-- Exact countdown-body cost after a lookup has already found its first
matching occurrence. -/
def flatPackedLookupBodyFoundSuccCost
    (remainingCount : Nat) (target : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    true selected remaining
  flatCountdownBodyCost (fun _ => state)
    (fun _ => flatPackedLookupStepFoundCost target word digit
      selected remaining)
    (remainingCount + 1) state

theorem flatPackedLookupBodyFoundSucc
    (remainingCount : Nat) (target : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatPackedLookupStepCode)
      ((remainingCount + 1) ::
        Code.flatPackedLookupColumnState target word digit
          true selected remaining)
      (flatCountdownOutput
        (fun _ => Code.flatPackedLookupColumnState target word digit
          true selected remaining)
        (remainingCount + 1)
        (Code.flatPackedLookupColumnState target word digit
          true selected remaining))
      (flatPackedLookupBodyFoundSuccCost remainingCount target word digit
        selected remaining) := by
  simpa [flatPackedLookupBodyFoundSuccCost] using
    flatCountdownBody_of_fit
      (flatPackedLookupStepFound target word digit selected remaining)
      (remainingCount + 1)

/-- Exact countdown-body cost for a not-yet-found nonempty coordinate
suffix. -/
def flatPackedLookupBodyConsCost
    (remainingCount : Nat) (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) : Nat :=
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let output := if selected && decide (cell = target) then
      Code.flatPackedLookupColumnState target
        (word / 9) (word % 9) true selected remaining
    else
      Code.flatPackedLookupColumnState target
        (word / 9) digit false selected remaining
  flatCountdownBodyCost (fun _ => output)
    (fun _ => flatPackedLookupStepConsCost target cell word digit
      selected remaining)
    (remainingCount + 1) state

theorem flatPackedLookupBodyCons
    (remainingCount : Nat) (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    let state := Code.flatPackedLookupColumnState target word digit
      false selected (cell :: remaining)
    let output := if selected && decide (cell = target) then
        Code.flatPackedLookupColumnState target
          (word / 9) (word % 9) true selected remaining
      else
        Code.flatPackedLookupColumnState target
          (word / 9) digit false selected remaining
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatPackedLookupStepCode)
      ((remainingCount + 1) :: state)
      (flatCountdownOutput (fun _ => output)
        (remainingCount + 1) state)
      (flatPackedLookupBodyConsCost remainingCount target cell word digit
        selected remaining) := by
  dsimp only
  simpa [flatPackedLookupBodyConsCost] using
    flatCountdownBody_of_fit
      (flatPackedLookupStepCons target cell word digit selected remaining)
      (remainingCount + 1)

/-- A zero countdown immediately returns its payload, independently of the
lookup step's unreachable behavior on an empty suffix. -/
def flatPackedLookupBodyZeroCost (state : List Nat) : Nat :=
  flatCountdownBodyCost (fun _ => state) (fun _ => 0) 0 state

theorem flatPackedLookupBodyZero (state : List Nat) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatPackedLookupStepCode)
      (0 :: state)
      (flatCountdownOutput (fun _ => state) 0 state)
      (flatPackedLookupBodyZeroCost state) := by
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedLookupBodyZeroCost, flatCountdownBodyCost,
    zeroPrimeCost] using
    EvaluatorCodeFits.case_zero
      (successorBranch :=
        .cons Code.one
          (.cons Code.head
            (Code.flatPackedLookupStepCode.comp Code.tail)))
      (values := 0 :: state) (by rfl) (zero'_named state)

/-- Additive exact cost of the frozen suffix of a lookup countdown. -/
def flatPackedLookupFoundFlatCost :
    Nat → Cell → Nat → Nat → Bool → List Cell → Nat
  | 0, target, word, digit, selected, remaining =>
      flatPackedLookupBodyZeroCost
        (Code.flatPackedLookupColumnState target word digit
          true selected remaining)
  | steps + 1, target, word, digit, selected, remaining =>
      flatPackedLookupBodyFoundSuccCost steps target word digit
          selected remaining +
        flatPackedLookupFoundFlatCost steps target word digit
          selected remaining

theorem flatPackedLookupFlatFoundBodyCall
    (steps : Nat) (target : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell)
    (continuation : ToPartrec.Cont) (bound : Nat)
    (budget : flatPackedLookupFoundFlatCost steps target word digit
        selected remaining + continuationSpace continuation ≤ bound)
    (after : EvaluatorExecutionFits bound
      (.ret continuation
        (Code.flatPackedLookupColumnState target word digit
          true selected remaining))) :
    EvaluatorCallFits
      (Code.flatCountdownBody Code.flatPackedLookupStepCode)
      (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
        continuation)
      (steps :: Code.flatPackedLookupColumnState target word digit
        true selected remaining) bound := by
  let state := Code.flatPackedLookupColumnState target word digit
    true selected remaining
  induction steps with
  | zero =>
      let body := flatPackedLookupBodyZero state
      have fixedAfter :
          EvaluatorExecutionFits bound
            (.ret (.fix
              (Code.flatCountdownBody Code.flatPackedLookupStepCode)
              continuation)
              (flatCountdownOutput (fun _ => state) 0 state)) := by
        apply EvaluatorExecutionFits.ret_fix_zero
        · rfl
        · simp only [continuationSpace_fix]
          have output := body.output_space
          have costBudget : flatPackedLookupBodyZeroCost state +
              continuationSpace continuation ≤ bound := by
            simpa only [flatPackedLookupFoundFlatCost] using budget
          omega
        · simpa [flatCountdownOutput, state] using after
      exact body.call
        (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
          continuation) bound
        (by
          simp only [continuationSpace_fix]
          change flatPackedLookupBodyZeroCost state +
              continuationSpace continuation ≤ bound
          exact budget)
        fixedAfter
  | succ steps induction =>
      let body := flatPackedLookupBodyFoundSucc steps target word digit
        selected remaining
      have recursiveBudget :
          flatPackedLookupFoundFlatCost steps target word digit
              selected remaining + continuationSpace continuation ≤
            bound := by
        simp only [flatPackedLookupFoundFlatCost] at budget
        omega
      have recursiveCall := induction recursiveBudget
      have fixedAfter :
          EvaluatorExecutionFits bound
            (.ret (.fix
              (Code.flatCountdownBody Code.flatPackedLookupStepCode)
              continuation)
              (flatCountdownOutput (fun _ => state) (steps + 1)
                state)) := by
        apply EvaluatorExecutionFits.ret_fix_succ
        · simp [flatCountdownOutput]
        · simp only [continuationSpace_fix]
          have output := body.output_space
          simp only [flatPackedLookupFoundFlatCost] at budget
          simp only [state] at *
          omega
        · simpa [flatCountdownOutput, state] using recursiveCall
      exact body.call
        (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
          continuation) bound
        (by
          simp only [continuationSpace_fix,
            flatPackedLookupFoundFlatCost] at *
          omega)
        fixedAfter

theorem flatPackedLookupFlatFound
    (steps : Nat) (target : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatIterate Code.flatPackedLookupStepCode)
      (steps :: Code.flatPackedLookupColumnState target word digit
        true selected remaining)
      (Code.flatPackedLookupColumnState target word digit
        true selected remaining)
      (flatPackedLookupFoundFlatCost steps target word digit
        selected remaining) where
  input_space := by
    cases steps with
    | zero =>
        exact (flatPackedLookupBodyZero
          (Code.flatPackedLookupColumnState target word digit
            true selected remaining)).input_space
    | succ steps =>
        exact (flatPackedLookupBodyFoundSucc steps target word digit
          selected remaining).input_space.trans (by
            simp [flatPackedLookupFoundFlatCost])
  output_space := by
    induction steps with
    | zero =>
        have body := (flatPackedLookupBodyZero
          (Code.flatPackedLookupColumnState target word digit
            true selected remaining)).output_space
        exact (listCodeEncodedListSpace_tail_le
          (0 :: Code.flatPackedLookupColumnState target word digit
            true selected remaining)).trans (by
              simpa [flatPackedLookupFoundFlatCost,
                flatCountdownOutput] using body)
    | succ steps induction =>
        exact induction.trans (by
          simp [flatPackedLookupFoundFlatCost])
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    exact flatPackedLookupFlatFoundBodyCall steps target word digit
      selected remaining continuation bound budget after

/-- Additive exact cost of one complete typed coordinate-stream pass. -/
def flatPackedLookupFlatCost
    (target : Cell) (selected : Bool) :
    List Cell → Nat → Nat → Bool → Nat
  | remaining, word, digit, true =>
      flatPackedLookupFoundFlatCost remaining.length target word digit
        selected remaining
  | [], word, digit, false =>
      flatPackedLookupBodyZeroCost
        (Code.flatPackedLookupColumnState target word digit
          false selected [])
  | cell :: remaining, word, digit, false =>
      flatPackedLookupBodyConsCost remaining.length target cell word digit
          selected remaining +
        if selected && decide (cell = target) then
          flatPackedLookupFoundFlatCost remaining.length target
            (word / 9) (word % 9) selected remaining
        else
          flatPackedLookupFlatCost target selected remaining
            (word / 9) digit false

theorem flatPackedLookupFlatInputSpace
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    encodedListSpace
        (motif.length ::
          Code.flatPackedLookupColumnState target word digit found selected
            motif) ≤
      flatPackedLookupFlatCost target selected motif word digit found := by
  cases found with
  | true =>
      simpa only [flatPackedLookupFlatCost] using
        (flatPackedLookupFlatFound motif.length target word digit
          selected motif).input_space
  | false =>
      cases motif with
      | nil =>
          exact (flatPackedLookupBodyZero
            (Code.flatPackedLookupColumnState target word digit
              false selected [])).input_space
      | cons cell remaining =>
          exact (flatPackedLookupBodyCons remaining.length target cell
            word digit selected remaining).input_space.trans (by
              simp [flatPackedLookupFlatCost])

theorem flatPackedLookupFlatOutputSpace
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    encodedListSpace
        (Code.flatPackedLookupColumnProcess target selected motif
          word digit found) ≤
      flatPackedLookupFlatCost target selected motif word digit found := by
  cases found with
  | true =>
      simpa only [flatPackedLookupFlatCost,
        Code.flatPackedLookupColumnProcess] using
        (flatPackedLookupFlatFound motif.length target word digit
          selected motif).output_space
  | false =>
      induction motif generalizing word digit with
      | nil =>
          let state := Code.flatPackedLookupColumnState target word digit
            false selected []
          have body := (flatPackedLookupBodyZero state).output_space
          exact (listCodeEncodedListSpace_tail_le (0 :: state)).trans (by
            simpa [flatPackedLookupFlatCost,
              Code.flatPackedLookupColumnProcess,
              flatCountdownOutput, state] using body)
      | cons cell remaining induction =>
          by_cases hit : selected && decide (cell = target)
          · have recursive := (flatPackedLookupFlatFound remaining.length
              target (word / 9) (word % 9) selected remaining).output_space
            have costEq :
                flatPackedLookupFlatCost target selected (cell :: remaining)
                    word digit false =
                  flatPackedLookupBodyConsCost remaining.length target cell
                      word digit selected remaining +
                    flatPackedLookupFoundFlatCost remaining.length target
                      (word / 9) (word % 9) selected remaining := by
              simp [flatPackedLookupFlatCost, hit]
            rw [Code.flatPackedLookupColumnProcess, if_pos hit, costEq]
            exact recursive.trans (Nat.le_add_left _ _)
          · have recursive := induction (word / 9) digit
            have costEq :
                flatPackedLookupFlatCost target selected (cell :: remaining)
                    word digit false =
                  flatPackedLookupBodyConsCost remaining.length target cell
                      word digit selected remaining +
                    flatPackedLookupFlatCost target selected remaining
                      (word / 9) digit false := by
              simp [flatPackedLookupFlatCost, hit]
            rw [Code.flatPackedLookupColumnProcess, if_neg hit, costEq]
            exact recursive.trans (Nat.le_add_left _ _)

theorem flatPackedLookupFlatBodyCall
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool)
    (continuation : ToPartrec.Cont) (bound : Nat)
    (budget : flatPackedLookupFlatCost target selected motif word digit found +
        continuationSpace continuation ≤ bound)
    (after : EvaluatorExecutionFits bound
      (.ret continuation
        (Code.flatPackedLookupColumnProcess target selected motif
          word digit found))) :
    EvaluatorCallFits
      (Code.flatCountdownBody Code.flatPackedLookupStepCode)
      (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
        continuation)
      (motif.length :: Code.flatPackedLookupColumnState target word digit
        found selected motif) bound := by
  cases found with
  | true =>
      exact flatPackedLookupFlatFoundBodyCall motif.length target word digit
        selected motif continuation bound
        (by simpa only [flatPackedLookupFlatCost] using budget)
        (by simpa [Code.flatPackedLookupColumnProcess] using after)
  | false =>
      induction motif generalizing word digit with
      | nil =>
          let state := Code.flatPackedLookupColumnState target word digit
            false selected []
          let body := flatPackedLookupBodyZero state
          have fixedAfter :
              EvaluatorExecutionFits bound
                (.ret (.fix
                  (Code.flatCountdownBody Code.flatPackedLookupStepCode)
                  continuation)
                  (flatCountdownOutput (fun _ => state) 0 state)) := by
            apply EvaluatorExecutionFits.ret_fix_zero
            · rfl
            · simp only [continuationSpace_fix]
              have output := body.output_space
              have costBudget : flatPackedLookupBodyZeroCost state +
                  continuationSpace continuation ≤ bound := by
                simpa only [flatPackedLookupFlatCost] using budget
              omega
            · simpa [flatCountdownOutput, state,
                Code.flatPackedLookupColumnProcess] using after
          exact body.call
            (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
              continuation) bound
            (by
              simp only [continuationSpace_fix]
              change flatPackedLookupBodyZeroCost state +
                  continuationSpace continuation ≤ bound
              exact budget)
            fixedAfter
      | cons cell remaining induction =>
          let state := Code.flatPackedLookupColumnState target word digit
            false selected (cell :: remaining)
          let output := if selected && decide (cell = target) then
              Code.flatPackedLookupColumnState target
                (word / 9) (word % 9) true selected remaining
            else
              Code.flatPackedLookupColumnState target
                (word / 9) digit false selected remaining
          let body := flatPackedLookupBodyCons remaining.length target cell
            word digit selected remaining
          by_cases hit : selected && decide (cell = target)
          · have recursiveBudget :
                flatPackedLookupFoundFlatCost remaining.length target
                      (word / 9) (word % 9) selected remaining +
                    continuationSpace continuation ≤ bound := by
              simp only [flatPackedLookupFlatCost, hit, if_true] at budget
              omega
            have recursiveCall := flatPackedLookupFlatFoundBodyCall
              remaining.length target (word / 9) (word % 9) selected
              remaining continuation bound recursiveBudget
              (by simpa [Code.flatPackedLookupColumnProcess, hit] using after)
            have fixedAfter :
                EvaluatorExecutionFits bound
                  (.ret (.fix
                    (Code.flatCountdownBody Code.flatPackedLookupStepCode)
                    continuation)
                    (flatCountdownOutput (fun _ => output)
                      (remaining.length + 1) state)) := by
              apply EvaluatorExecutionFits.ret_fix_succ
              · simp [flatCountdownOutput, output, hit]
              · simp only [continuationSpace_fix]
                have outputSpace := body.output_space
                simp only [flatPackedLookupFlatCost, hit, if_true] at budget
                simp only [state, output] at *
                omega
              · simpa [flatCountdownOutput, output, hit] using recursiveCall
            exact body.call
              (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
                continuation) bound
              (by
                simp only [continuationSpace_fix,
                  flatPackedLookupFlatCost, hit, if_true] at *
                omega)
              fixedAfter
          · have recursiveBudget :
                flatPackedLookupFlatCost target selected remaining
                      (word / 9) digit false +
                    continuationSpace continuation ≤ bound := by
              simp [flatPackedLookupFlatCost, hit] at budget
              omega
            have recursiveCall := induction (word / 9) digit
              recursiveBudget (by
                simpa [Code.flatPackedLookupColumnProcess, hit] using after)
            have fixedAfter :
                EvaluatorExecutionFits bound
                  (.ret (.fix
                    (Code.flatCountdownBody Code.flatPackedLookupStepCode)
                    continuation)
                    (flatCountdownOutput (fun _ => output)
                      (remaining.length + 1) state)) := by
              apply EvaluatorExecutionFits.ret_fix_succ
              · simp [flatCountdownOutput, output, hit]
              · simp only [continuationSpace_fix]
                have outputSpace := body.output_space
                simp [flatPackedLookupFlatCost, hit] at budget
                simp only [state, output] at *
                omega
              · simpa [flatCountdownOutput, output, hit] using recursiveCall
            exact body.call
              (.fix (Code.flatCountdownBody Code.flatPackedLookupStepCode)
                continuation) bound
              (by
                simp [continuationSpace_fix,
                  flatPackedLookupFlatCost, hit] at *
                omega)
              fixedAfter

/-- One complete typed flat motif pass has an exact additive evaluator-space
certificate. -/
theorem flatPackedLookupFlat
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    EvaluatorCodeFits
      (Code.flatIterate Code.flatPackedLookupStepCode)
      (motif.length ::
        Code.flatPackedLookupColumnState target word digit found selected
          motif)
      (Code.flatPackedLookupColumnProcess target selected motif
        word digit found)
      (flatPackedLookupFlatCost target selected motif word digit found) where
  input_space := flatPackedLookupFlatInputSpace
    target selected motif word digit found
  output_space := flatPackedLookupFlatOutputSpace
    target selected motif word digit found
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    exact flatPackedLookupFlatBodyCall target selected motif word digit found
      continuation bound budget after

end EvaluatorCodeFits
end PartrecToTM2
end Turing
