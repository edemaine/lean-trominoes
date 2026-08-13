/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatIteration
import LeanTrominoes.PartrecFrontierIndexDecode
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecPackedAssignmentLookup
import LeanTrominoes.PeriodicStripFlatEncoding

/-!
# One packed-assignment lookup pass over flat motif coordinates

The standard packed lookup scans an encoded motif list.  This module performs
the same one-column pass directly on

`x₀, y₀, x₁, y₁, ...`.

Its state is

`[target x, target y, word, digit, found, selected, coordinates...]`.

Every unsuccessful step consumes one coordinate pair and one base-nine digit.
The first successful step records the exposed digit and freezes the state, so
repeated motif cells obey exactly the established first-occurrence semantics.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

/-- Reachable state of one flat coordinate-stream lookup pass. -/
def flatPackedLookupColumnState
    (target : Cell) (word digit : Nat) (found selected : Bool)
    (remaining : List Cell) : List Nat :=
  [Encodable.encode target.1, Encodable.encode target.2,
    word, digit, found.toNat, selected.toNat] ++
    remaining.flatMap PeriodicStripFlatEncoding.cellFields

/-- Compare the leading horizontal coordinate with the target. -/
def flatPackedLookupXEqualityCode : Code :=
  natEqCode.comp (prepend (get 6) (get 0))

/-- Compare the leading vertical coordinate with the target. -/
def flatPackedLookupYEqualityCode : Code :=
  natEqCode.comp (prepend (get 7) (get 1))

/-- The selected pass has reached the target cell. -/
def flatPackedLookupMatchCode : Code :=
  boolAnd (get 5) <|
    boolAnd flatPackedLookupXEqualityCode
      flatPackedLookupYEqualityCode

@[simp]
theorem flatPackedLookupXEqualityCode_eval
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    flatPackedLookupXEqualityCode.eval
        (flatPackedLookupColumnState target word digit found selected
          (cell :: remaining)) =
      pure [(decide (cell.1 = target.1)).toNat] := by
  rcases target with ⟨targetX, targetY⟩
  rcases cell with ⟨cellX, cellY⟩
  by_cases equal : cellX = targetX
  · subst targetX
    simp [flatPackedLookupXEqualityCode,
      flatPackedLookupColumnState,
      PeriodicStripFlatEncoding.cellFields]
  · have encodedNe :
        Encodable.encode cellX ≠ Encodable.encode targetX := by
      intro encodedEqual
      exact equal (Encodable.encode_injective encodedEqual)
    simp [flatPackedLookupXEqualityCode,
      flatPackedLookupColumnState,
      PeriodicStripFlatEncoding.cellFields, equal, encodedNe]

@[simp]
theorem flatPackedLookupYEqualityCode_eval
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    flatPackedLookupYEqualityCode.eval
        (flatPackedLookupColumnState target word digit found selected
          (cell :: remaining)) =
      pure [(decide (cell.2 = target.2)).toNat] := by
  rcases target with ⟨targetX, targetY⟩
  rcases cell with ⟨cellX, cellY⟩
  by_cases equal : cellY = targetY
  · subst targetY
    simp [flatPackedLookupYEqualityCode,
      flatPackedLookupColumnState,
      PeriodicStripFlatEncoding.cellFields]
  · have encodedNe :
        Encodable.encode cellY ≠ Encodable.encode targetY := by
      intro encodedEqual
      exact equal (Encodable.encode_injective encodedEqual)
    simp [flatPackedLookupYEqualityCode,
      flatPackedLookupColumnState,
      PeriodicStripFlatEncoding.cellFields, equal, encodedNe]

@[simp]
theorem flatPackedLookupMatchCode_eval
    (target cell : Cell) (word digit : Nat)
    (found selected : Bool) (remaining : List Cell) :
    flatPackedLookupMatchCode.eval
        (flatPackedLookupColumnState target word digit found selected
          (cell :: remaining)) =
      pure [(selected && decide (cell = target)).toNat] := by
  have coordinates := boolAnd_eval_at
    flatPackedLookupXEqualityCode flatPackedLookupYEqualityCode
    (flatPackedLookupColumnState target word digit found selected
      (cell :: remaining))
    (decide (cell.1 = target.1)).toNat
    (decide (cell.2 = target.2)).toNat
    (flatPackedLookupXEqualityCode_eval
      target cell word digit found selected remaining)
    (flatPackedLookupYEqualityCode_eval
      target cell word digit found selected remaining)
  have coordinateEval :
      (boolAnd flatPackedLookupXEqualityCode
        flatPackedLookupYEqualityCode).eval
          (flatPackedLookupColumnState target word digit found selected
            (cell :: remaining)) =
        pure [(decide (cell = target)).toNat] := by
    rcases target with ⟨targetX, targetY⟩
    rcases cell with ⟨cellX, cellY⟩
    simp only [Prod.mk.injEq]
    by_cases xEqual : cellX = targetX <;>
      by_cases yEqual : cellY = targetY <;>
      simp [xEqual, yEqual] at coordinates ⊢ <;>
      exact coordinates
  have combined := boolAnd_eval_at
    (get 5)
    (boolAnd flatPackedLookupXEqualityCode
      flatPackedLookupYEqualityCode)
    (flatPackedLookupColumnState target word digit found selected
      (cell :: remaining))
    selected.toNat
    (decide (cell = target)).toNat
    (by simp [flatPackedLookupColumnState,
      PeriodicStripFlatEncoding.cellFields])
    coordinateEval
  cases selected with
  | false =>
      simpa [flatPackedLookupMatchCode] using combined
  | true =>
      by_cases equal : cell = target <;>
        simpa [flatPackedLookupMatchCode, equal] using combined

/-- Consume one cell after an unsuccessful comparison. -/
def flatPackedLookupContinueCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (assignmentWordStepFieldAtCode 2 0) <|
        prepend (get 3) <|
          prepend (get 4) <|
            prepend (get 5) (drop 8)

@[simp]
theorem flatPackedLookupContinueCode_eval
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    flatPackedLookupContinueCode.eval
        (flatPackedLookupColumnState target word digit false selected
          (cell :: remaining)) =
      pure
        (flatPackedLookupColumnState target (word / 9) digit false
          selected remaining) := by
  rcases target with ⟨targetX, targetY⟩
  rcases cell with ⟨cellX, cellY⟩
  simp [flatPackedLookupContinueCode,
    flatPackedLookupColumnState,
    PeriodicStripFlatEncoding.cellFields]

/-- Consume the first matching cell, recording its exposed digit. -/
def flatPackedLookupFoundCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (assignmentWordStepFieldAtCode 2 0) <|
        prepend (assignmentWordStepFieldAtCode 2 1) <|
          prepend one <|
            prepend (get 5) (drop 8)

@[simp]
theorem flatPackedLookupFoundCode_eval
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    flatPackedLookupFoundCode.eval
        (flatPackedLookupColumnState target word digit false selected
          (cell :: remaining)) =
      pure
        (flatPackedLookupColumnState target (word / 9) (word % 9) true
          selected remaining) := by
  rcases target with ⟨targetX, targetY⟩
  rcases cell with ⟨cellX, cellY⟩
  simp [flatPackedLookupFoundCode,
    flatPackedLookupColumnState,
    PeriodicStripFlatEncoding.cellFields]

/-- One not-yet-found coordinate step. -/
def flatPackedLookupConsStepCode : Code :=
  branchZero flatPackedLookupMatchCode
    flatPackedLookupContinueCode flatPackedLookupFoundCode

@[simp]
theorem flatPackedLookupConsStepCode_eval
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    flatPackedLookupConsStepCode.eval
        (flatPackedLookupColumnState target word digit false selected
          (cell :: remaining)) =
      pure
        (if selected && decide (cell = target) then
          flatPackedLookupColumnState target
            (word / 9) (word % 9) true selected remaining
        else
          flatPackedLookupColumnState target
            (word / 9) digit false selected remaining) := by
  by_cases hit : selected && decide (cell = target)
  · rw [if_pos hit]
    exact branchZero_eval_succ_at flatPackedLookupMatchCode
      flatPackedLookupContinueCode flatPackedLookupFoundCode
      (flatPackedLookupColumnState target word digit false selected
        (cell :: remaining))
      (selected && decide (cell = target)).toNat
      (flatPackedLookupMatchCode_eval
        target cell word digit false selected remaining)
      (flatPackedLookupColumnState target
        (word / 9) (word % 9) true selected remaining)
      (flatPackedLookupFoundCode_eval
        target cell word digit selected remaining)
      (by simp [hit])
  · rw [if_neg hit]
    exact branchZero_eval_zero_at flatPackedLookupMatchCode
      flatPackedLookupContinueCode flatPackedLookupFoundCode
      (flatPackedLookupColumnState target word digit false selected
        (cell :: remaining))
      (selected && decide (cell = target)).toNat
      (flatPackedLookupMatchCode_eval
        target cell word digit false selected remaining)
      (flatPackedLookupColumnState target
        (word / 9) digit false selected remaining)
      (flatPackedLookupContinueCode_eval
        target cell word digit selected remaining)
      (by simp [hit])

/-- Once a first occurrence is found, later countdown steps are fixed points. -/
def flatPackedLookupStepCode : Code :=
  branchZero (get 4) flatPackedLookupConsStepCode id

@[simp]
theorem flatPackedLookupStepCode_eval_found
    (target : Cell) (word digit : Nat) (selected : Bool)
    (remaining : List Cell) :
    flatPackedLookupStepCode.eval
        (flatPackedLookupColumnState target word digit true selected
          remaining) =
      pure
        (flatPackedLookupColumnState target word digit true selected
          remaining) := by
  exact branchZero_eval_succ_at (get 4)
    flatPackedLookupConsStepCode id
    (flatPackedLookupColumnState target word digit true selected remaining)
    1 (by simp [flatPackedLookupColumnState])
    (flatPackedLookupColumnState target word digit true selected remaining)
    (by simp) (by omega)

@[simp]
theorem flatPackedLookupStepCode_eval_cons
    (target cell : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    flatPackedLookupStepCode.eval
        (flatPackedLookupColumnState target word digit false selected
          (cell :: remaining)) =
      pure
        (if selected && decide (cell = target) then
          flatPackedLookupColumnState target
            (word / 9) (word % 9) true selected remaining
        else
          flatPackedLookupColumnState target
            (word / 9) digit false selected remaining) := by
  apply branchZero_eval_zero_at (get 4)
    flatPackedLookupConsStepCode id
    (flatPackedLookupColumnState target word digit false selected
      (cell :: remaining))
    0 (by simp [flatPackedLookupColumnState,
      PeriodicStripFlatEncoding.cellFields])
    (if selected && decide (cell = target) then
      flatPackedLookupColumnState target
        (word / 9) (word % 9) true selected remaining
    else
      flatPackedLookupColumnState target
        (word / 9) digit false selected remaining)
  · exact flatPackedLookupConsStepCode_eval
      target cell word digit selected remaining
  · rfl

/-- Exact final state of one semantic flat pass. -/
def flatPackedLookupColumnProcess
    (target : Cell) (selected : Bool) :
    List Cell → Nat → Nat → Bool → List Nat
  | remaining, word, digit, true =>
      flatPackedLookupColumnState target word digit true selected remaining
  | [], word, digit, false =>
      flatPackedLookupColumnState target word digit false selected []
  | cell :: remaining, word, digit, false =>
      if selected && decide (cell = target) then
        flatPackedLookupColumnState target
          (word / 9) (word % 9) true selected remaining
      else
        flatPackedLookupColumnProcess target selected remaining
          (word / 9) digit false

theorem flatPackedLookupIterateCode_eval_found
    (steps : Nat) (target : Cell) (word digit : Nat)
    (selected : Bool) (remaining : List Cell) :
    (flatIterate flatPackedLookupStepCode).eval
        (steps :: flatPackedLookupColumnState target word digit true
          selected remaining) =
      pure
        (flatPackedLookupColumnState target word digit true selected
          remaining) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      refine ⟨steps :: flatPackedLookupColumnState target word digit true
          selected remaining, ?_, induction⟩
      simp [flatCountdownBody,
        flatPackedLookupStepCode_eval_found]

/-- A countdown of exactly the motif length implements the semantic lookup
process on native coordinate fields. -/
theorem flatPackedLookupIterateCode_eval
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    (flatIterate flatPackedLookupStepCode).eval
        (motif.length ::
          flatPackedLookupColumnState target word digit found selected
            motif) =
      pure
        (flatPackedLookupColumnProcess target selected motif
          word digit found) := by
  cases found with
  | true =>
      simpa [flatPackedLookupColumnProcess] using
        flatPackedLookupIterateCode_eval_found motif.length target
          word digit selected motif
  | false =>
      rw [flatIterate, fix_eval]
      apply Part.eq_some_iff.mpr
      induction motif generalizing word digit with
      | nil =>
          apply PFun.mem_fix_iff.mpr
          left
          simp [flatCountdownBody_zero_eval,
            flatPackedLookupColumnProcess]
      | cons cell remaining induction =>
          apply PFun.mem_fix_iff.mpr
          right
          by_cases hit : selected && decide (cell = target)
          · refine ⟨remaining.length ::
                flatPackedLookupColumnState target
                  (word / 9) (word % 9) true selected remaining,
              ?_, ?_⟩
            · simp [flatCountdownBody,
                flatPackedLookupStepCode_eval_cons, hit]
            · have foundRun :=
                flatPackedLookupIterateCode_eval_found
                  remaining.length target (word / 9) (word % 9)
                    selected remaining
              rw [flatIterate, fix_eval] at foundRun
              simpa [flatPackedLookupColumnProcess, hit] using
                Part.eq_some_iff.mp foundRun
          · refine ⟨remaining.length ::
                flatPackedLookupColumnState target
                  (word / 9) digit false selected remaining,
              ?_, ?_⟩
            · simp [flatCountdownBody,
                flatPackedLookupStepCode_eval_cons, hit]
            · simpa [flatPackedLookupColumnProcess, hit] using
                induction (word / 9) digit

/-- The three accumulator fields of the flat process are exactly those of
the established encoded-list lookup semantics. -/
theorem flatPackedLookupColumnProcess_outcome_fields
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    let final := flatPackedLookupColumnProcess target selected motif
      word digit found
    let outcome := packedLookupColumnOutcome target selected motif
      word digit found
    [final[2]?.getD 0, final[3]?.getD 0, final[4]?.getD 0] =
      [outcome.1, outcome.2.1, outcome.2.2.toNat] := by
  induction motif generalizing word digit found with
  | nil =>
      cases found <;>
        simp [flatPackedLookupColumnProcess,
          flatPackedLookupColumnState, packedLookupColumnOutcome]
  | cons cell remaining induction =>
      cases found with
      | true =>
          simp [flatPackedLookupColumnProcess,
            flatPackedLookupColumnState, packedLookupColumnOutcome,
            PeriodicStripFlatEncoding.cellFields]
      | false =>
          by_cases hit : selected && decide (cell = target)
          · simp [flatPackedLookupColumnProcess,
              flatPackedLookupColumnState, packedLookupColumnOutcome,
              PeriodicStripFlatEncoding.cellFields, hit]
          · simpa [flatPackedLookupColumnProcess,
              packedLookupColumnOutcome, hit] using
              induction (word / 9) digit false

end Turing.ToPartrec.Code
