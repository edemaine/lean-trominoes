/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedLookupColumn
import LeanTrominoes.PartrecPackedAssignmentAt

/-!
# Five-column packed assignment lookup on a flat motif

This module restores the original coordinate stream between five calls to the
flat one-column scanner.  Its public input is

`[motif length, queried column, target x, target y, word, coordinates...]`

and its output is `[digit, found]`, exactly matching
`packedAssignmentLookupCode` without constructing a nested motif code.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Fixed state retained between the five flat motif passes. -/
def flatPackedAssignmentLookupState
    (motif : List Cell) (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : List Nat :=
  [motif.length, queriedColumn,
    Encodable.encode target.1, Encodable.encode target.2,
    accumulator.1, accumulator.2.1, accumulator.2.2.toNat] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields

/-- Test whether the current numbered pass is the queried column. -/
def flatPackedAssignmentColumnSelectedCode
    (currentColumn : Nat) : Code :=
  natEqCode.comp (prepend (get 1) (numeral currentColumn))

@[simp]
theorem flatPackedAssignmentColumnSelectedCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (flatPackedAssignmentColumnSelectedCode currentColumn).eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          accumulator) =
      pure [(decide (queriedColumn = currentColumn)).toNat] := by
  by_cases equal : queriedColumn = currentColumn <;>
    simp [flatPackedAssignmentColumnSelectedCode,
      flatPackedAssignmentLookupState, equal]

/-- Build the countdown plus one-column scanner state, copying the coordinate
stream after the six scalar scanner fields. -/
def flatPackedAssignmentColumnInputCode
    (currentColumn : Nat) : Code :=
  prepend (get 0) <|
    prepend (get 2) <|
      prepend (get 3) <|
        prepend (get 4) <|
          prepend (get 5) <|
            prepend (get 6) <|
              prepend (flatPackedAssignmentColumnSelectedCode currentColumn)
                (drop 7)

@[simp]
theorem flatPackedAssignmentColumnInputCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (flatPackedAssignmentColumnInputCode currentColumn).eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          accumulator) =
      pure
        (motif.length ::
          flatPackedLookupColumnState target
            accumulator.1 accumulator.2.1 accumulator.2.2
            (decide (queriedColumn = currentColumn)) motif) := by
  have selectedRun :=
    flatPackedAssignmentColumnSelectedCode_eval
      currentColumn motif queriedColumn target accumulator
  rcases target with ⟨targetX, targetY⟩
  rcases accumulator with ⟨word, digit, found⟩
  let state := flatPackedAssignmentLookupState motif queriedColumn
    (targetX, targetY) (word, digit, found)
  simp only [flatPackedAssignmentColumnInputCode, prepend_eval_eq]
  rw [show (get 0).eval state = pure [motif.length] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 2).eval state = pure [Encodable.encode targetX] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 3).eval state = pure [Encodable.encode targetY] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 4).eval state = pure [word] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 5).eval state = pure [digit] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 6).eval state = pure [found.toNat] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [selectedRun]
  simp [flatPackedAssignmentLookupState,
    flatPackedLookupColumnState]

/-- Invoke one complete flat motif pass. -/
def flatPackedAssignmentColumnCallCode
    (currentColumn : Nat) : Code :=
  (flatIterate flatPackedLookupStepCode).comp
    (flatPackedAssignmentColumnInputCode currentColumn)

@[simp]
theorem flatPackedAssignmentColumnCallCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (flatPackedAssignmentColumnCallCode currentColumn).eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          accumulator) =
      pure
        (flatPackedLookupColumnProcess target
          (decide (queriedColumn = currentColumn)) motif
          accumulator.1 accumulator.2.1 accumulator.2.2) := by
  calc
    _ = (flatIterate flatPackedLookupStepCode).eval
        (motif.length ::
          flatPackedLookupColumnState target
            accumulator.1 accumulator.2.1 accumulator.2.2
            (decide (queriedColumn = currentColumn)) motif) :=
      comp_eval_pure _ _ _ _
        (flatPackedAssignmentColumnInputCode_eval
          currentColumn motif queriedColumn target accumulator)
    _ = _ := flatPackedLookupIterateCode_eval target
      (decide (queriedColumn = currentColumn)) motif
      accumulator.1 accumulator.2.1 accumulator.2.2

/-- Read one of the updated `(word, digit, found)` fields from a pass. -/
def flatPackedAssignmentColumnResultFieldCode
    (currentColumn : Nat) (outputField : Fin 3) : Code :=
  (get (outputField.val + 2)).comp
    (flatPackedAssignmentColumnCallCode currentColumn)

def flatPackedAssignmentAccumulatorFields
    (accumulator : Nat × Nat × Bool) : List Nat :=
  [accumulator.1, accumulator.2.1, accumulator.2.2.toNat]

@[simp]
theorem flatPackedAssignmentColumnResultFieldCode_eval
    (currentColumn : Nat) (outputField : Fin 3) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (flatPackedAssignmentColumnResultFieldCode
      currentColumn outputField).eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          accumulator) =
      pure
        [(flatPackedAssignmentAccumulatorFields
          (packedAssignmentLookupApplyColumn currentColumn motif
            queriedColumn target accumulator))[outputField.val]?.getD 0] := by
  let final := flatPackedLookupColumnProcess target
    (decide (queriedColumn = currentColumn)) motif
    accumulator.1 accumulator.2.1 accumulator.2.2
  let outcome := packedAssignmentLookupApplyColumn currentColumn motif
    queriedColumn target accumulator
  have callRun :
      (flatPackedAssignmentColumnCallCode currentColumn).eval
          (flatPackedAssignmentLookupState motif queriedColumn target
            accumulator) = pure final := by
    simp [final]
  have fields :
      [final[2]?.getD 0, final[3]?.getD 0, final[4]?.getD 0] =
        flatPackedAssignmentAccumulatorFields outcome := by
    simpa [final, outcome, flatPackedAssignmentAccumulatorFields,
      packedAssignmentLookupApplyColumn] using
      (flatPackedLookupColumnProcess_outcome_fields
        target (decide (queriedColumn = currentColumn)) motif
        accumulator.1 accumulator.2.1 accumulator.2.2)
  have indexed := congrArg
    (fun values => values[outputField.val]?.getD 0) fields
  rw [flatPackedAssignmentColumnResultFieldCode]
  calc
    _ = (get (outputField.val + 2)).eval final :=
      comp_eval_pure _ _ _ _ callRun
    _ = pure [final[outputField.val + 2]?.getD 0] := by simp
    _ = pure
        [(flatPackedAssignmentAccumulatorFields outcome)[outputField.val]?.getD 0] := by
      fin_cases outputField <;> simpa using
        indexed
    _ = _ := by rfl

/-- One numbered pass, restoring the original coordinates around the updated
three-field accumulator. -/
def flatPackedAssignmentColumnStageCode
    (currentColumn : Nat) : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend (flatPackedAssignmentColumnResultFieldCode
            currentColumn (0 : Fin 3)) <|
            prepend (flatPackedAssignmentColumnResultFieldCode
              currentColumn (1 : Fin 3)) <|
              prepend (flatPackedAssignmentColumnResultFieldCode
                currentColumn (2 : Fin 3)) (drop 7)

@[simp]
theorem flatPackedAssignmentColumnStageCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (flatPackedAssignmentColumnStageCode currentColumn).eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          accumulator) =
      pure
        (flatPackedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupApplyColumn currentColumn motif
            queriedColumn target accumulator)) := by
  have wordRun := flatPackedAssignmentColumnResultFieldCode_eval
    currentColumn (0 : Fin 3) motif queriedColumn target accumulator
  have digitRun := flatPackedAssignmentColumnResultFieldCode_eval
    currentColumn (1 : Fin 3) motif queriedColumn target accumulator
  have foundRun := flatPackedAssignmentColumnResultFieldCode_eval
    currentColumn (2 : Fin 3) motif queriedColumn target accumulator
  rcases target with ⟨targetX, targetY⟩
  rcases accumulator with ⟨word, digit, found⟩
  let state := flatPackedAssignmentLookupState motif queriedColumn
    (targetX, targetY) (word, digit, found)
  simp only [flatPackedAssignmentColumnStageCode, prepend_eval_eq]
  rw [show (get 0).eval state = pure [motif.length] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 1).eval state = pure [queriedColumn] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 2).eval state = pure [Encodable.encode targetX] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [show (get 3).eval state = pure [Encodable.encode targetY] by
    simp [state, flatPackedAssignmentLookupState]]
  rw [wordRun, digitRun, foundRun]
  simp [flatPackedAssignmentLookupState,
    flatPackedAssignmentAccumulatorFields]

/-- Apply columns zero through four in assignment-key order. -/
def flatPackedAssignmentLookupStagesCode : Code :=
  (flatPackedAssignmentColumnStageCode 4).comp <|
    (flatPackedAssignmentColumnStageCode 3).comp <|
      (flatPackedAssignmentColumnStageCode 2).comp <|
        (flatPackedAssignmentColumnStageCode 1).comp
          (flatPackedAssignmentColumnStageCode 0)

@[simp]
theorem flatPackedAssignmentLookupStagesCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentLookupStagesCode.eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          (word, 0, false)) =
      pure
        (flatPackedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupOutcome motif queriedColumn target word)) := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first := packedAssignmentLookupApplyColumn
    0 motif queriedColumn target initial
  let second := packedAssignmentLookupApplyColumn
    1 motif queriedColumn target first
  let third := packedAssignmentLookupApplyColumn
    2 motif queriedColumn target second
  let fourth := packedAssignmentLookupApplyColumn
    3 motif queriedColumn target third
  have run0 := flatPackedAssignmentColumnStageCode_eval
    0 motif queriedColumn target initial
  have run1 := flatPackedAssignmentColumnStageCode_eval
    1 motif queriedColumn target first
  have run2 := flatPackedAssignmentColumnStageCode_eval
    2 motif queriedColumn target second
  have run3 := flatPackedAssignmentColumnStageCode_eval
    3 motif queriedColumn target third
  have run4 := flatPackedAssignmentColumnStageCode_eval
    4 motif queriedColumn target fourth
  calc
    _ = (flatPackedAssignmentColumnStageCode 4).eval
        (flatPackedAssignmentLookupState motif queriedColumn target fourth) := by
      simp [flatPackedAssignmentLookupStagesCode, run0, run1, run2, run3,
        initial, first, second, third, fourth]
    _ = pure
        (flatPackedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupApplyColumn
            4 motif queriedColumn target fourth)) := run4
    _ = _ := by
      rfl

/-- Initialize lookup state from the public flat input. -/
def flatPackedAssignmentLookupInputCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend (get 4) <|
            prepend zero <|
              prepend zero (drop 5)

@[simp]
theorem flatPackedAssignmentLookupInputCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentLookupInputCode.eval
        ([motif.length, queriedColumn,
            Encodable.encode target.1, Encodable.encode target.2, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure
        (flatPackedAssignmentLookupState motif queriedColumn target
          (word, 0, false)) := by
  rcases target with ⟨targetX, targetY⟩
  simp [flatPackedAssignmentLookupInputCode,
    flatPackedAssignmentLookupState]

/-- Complete native-field lookup returning `[digit, found]`. -/
def flatPackedAssignmentLookupCode : Code :=
  (prepend (get 5) (get 6)).comp <|
    flatPackedAssignmentLookupStagesCode.comp
      flatPackedAssignmentLookupInputCode

@[simp]
theorem flatPackedAssignmentLookupCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentLookupCode.eval
        ([motif.length, queriedColumn,
            Encodable.encode target.1, Encodable.encode target.2, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure
        [(packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1,
          (packedAssignmentLookupOutcome motif queriedColumn
            target word).2.2.toNat] := by
  have inputRun := flatPackedAssignmentLookupInputCode_eval
    motif queriedColumn target word
  have stagesRun := flatPackedAssignmentLookupStagesCode_eval
    motif queriedColumn target word
  have composed :
      (flatPackedAssignmentLookupStagesCode.comp
        flatPackedAssignmentLookupInputCode).eval
          ([motif.length, queriedColumn,
              Encodable.encode target.1, Encodable.encode target.2, word] ++
            motif.flatMap PeriodicStripFlatEncoding.cellFields) =
        pure
          (flatPackedAssignmentLookupState motif queriedColumn target
            (packedAssignmentLookupOutcome motif queriedColumn target word)) := by
    calc
      _ = flatPackedAssignmentLookupStagesCode.eval
          (flatPackedAssignmentLookupState motif queriedColumn target
            (word, 0, false)) := comp_eval_pure _ _ _ _ inputRun
      _ = _ := stagesRun
  calc
    _ = (prepend (get 5) (get 6)).eval
        (flatPackedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupOutcome motif queriedColumn target word)) :=
      comp_eval_pure _ _ _ _ composed
    _ = _ := by
      rcases target with ⟨targetX, targetY⟩
      simp [flatPackedAssignmentLookupState]

end Turing.ToPartrec.Code
