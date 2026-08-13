import LeanTrominoes.PartrecFlatPackedAssignmentAt
import LeanTrominoes.PartrecPackedAssignmentPredicates

/-!
# Predicates on flat packed-assignment lookups

These wrappers expose the digit, `none`, and fixed-assignment tests needed by
the flat transition checker.  Their common input is

`[motif length, column, target x, target y, word, coordinates...]`.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Project the digit returned by the flat five-column lookup. -/
def flatPackedAssignmentLookupDigitCode : Code :=
  (get 0).comp flatPackedAssignmentLookupCode

@[simp]
theorem flatPackedAssignmentLookupDigitCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentLookupDigitCode.eval
        ([motif.length, queriedColumn,
            Encodable.encode target.1, Encodable.encode target.2, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure
        [(packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1] := by
  calc
    _ = (get 0).eval
        [(packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1,
          (packedAssignmentLookupOutcome motif queriedColumn
            target word).2.2.toNat] :=
      comp_eval_pure _ _ _ _
        (flatPackedAssignmentLookupCode_eval
          motif queriedColumn target word)
    _ = _ := by simp

/-- Return one exactly when the selected assignment is `none`. -/
def flatPackedAssignmentIsNoneCode : Code :=
  isZero flatPackedAssignmentLookupDigitCode

@[simp]
theorem flatPackedAssignmentIsNoneCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentIsNoneCode.eval
        ([motif.length, queriedColumn,
            Encodable.encode target.1, Encodable.encode target.2, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure
        [if (packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1 = 0 then 1 else 0] := by
  exact isZero_eval_at flatPackedAssignmentLookupDigitCode _ _
    (flatPackedAssignmentLookupDigitCode_eval
      motif queriedColumn target word)

@[simp]
theorem flatPackedAssignmentIsNoneCode_eval_semantic
    (periodicStrip : PeriodicStrip) (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    flatPackedAssignmentIsNoneCode.eval
        ([periodicStrip.motif.length, column.val,
            Encodable.encode target.1, Encodable.encode target.2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) =
      pure
        [(decide
          (packed.assignmentAtCell periodicStrip column target =
            none)).toNat] := by
  rw [flatPackedAssignmentIsNoneCode_eval]
  have digitBound := packedAssignmentLookupOutcome_digit_lt
    periodicStrip.motif column.val target packed.assignmentWord
  have decoded := assignmentOfDigit_packedAssignmentLookupOutcome
    periodicStrip packed column target
  have equivalent :
      (packedAssignmentLookupOutcome periodicStrip.motif column.val
          target packed.assignmentWord).2.1 = 0 ↔
        packed.assignmentAtCell periodicStrip column target = none := by
    rw [← decoded]
    exact (assignmentOfDigit_eq_none_iff _ digitBound).symm
  by_cases isNone :
      packed.assignmentAtCell periodicStrip column target = none
  · have selectedRaw :
        (packed.toRaw periodicStrip).assignmentAtCell
            periodicStrip column target = none := by
      simpa using isNone
    simp [equivalent.mpr isNone, selectedRaw]
  · have digitNonzero : ¬
        (packedAssignmentLookupOutcome periodicStrip.motif column.val
          target packed.assignmentWord).2.1 = 0 :=
      fun digitZero => isNone (equivalent.mp digitZero)
    have selectedRaw : ¬
        (packed.toRaw periodicStrip).assignmentAtCell
            periodicStrip column target = none := by
      simpa using isNone
    simp [digitNonzero, selectedRaw]

/-- Pair the selected digit with the canonical digit of a fixed semantic
assignment state. -/
def flatPackedAssignmentIsArgumentsCode
    (state : Option SquareSymmetry) : Code :=
  prepend flatPackedAssignmentLookupDigitCode
    (numeral (assignmentDigit state))

/-- Return one exactly when the selected assignment equals `state`. -/
def flatPackedAssignmentIsCode
    (state : Option SquareSymmetry) : Code :=
  natEqCode.comp (flatPackedAssignmentIsArgumentsCode state)

@[simp]
theorem flatPackedAssignmentIsCode_eval
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    (flatPackedAssignmentIsCode state).eval
        ([motif.length, queriedColumn,
            Encodable.encode target.1, Encodable.encode target.2, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure
        [if (packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1 = assignmentDigit state
          then 1 else 0] := by
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  have digitRun := flatPackedAssignmentLookupDigitCode_eval
    motif queriedColumn target word
  have arguments :
      (flatPackedAssignmentIsArgumentsCode state).eval values =
        pure
          [(packedAssignmentLookupOutcome motif queriedColumn
              target word).2.1,
            assignmentDigit state] := by
    simp only [flatPackedAssignmentIsArgumentsCode, prepend_eval_eq]
    rw [digitRun]
    simp
  calc
    _ = natEqCode.eval
        [(packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1,
          assignmentDigit state] :=
      comp_eval_pure _ _ _ _ arguments
    _ = _ := by simp

@[simp]
theorem flatPackedAssignmentIsCode_eval_semantic
    (state : Option SquareSymmetry)
    (periodicStrip : PeriodicStrip) (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    (flatPackedAssignmentIsCode state).eval
        ([periodicStrip.motif.length, column.val,
            Encodable.encode target.1, Encodable.encode target.2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) =
      pure
        [(decide
          (packed.assignmentAtCell periodicStrip column target =
            state)).toNat] := by
  rw [flatPackedAssignmentIsCode_eval]
  let digit :=
    (packedAssignmentLookupOutcome periodicStrip.motif column.val
      target packed.assignmentWord).2.1
  have digitBound : digit < 9 := by
    simpa [digit] using packedAssignmentLookupOutcome_digit_lt
      periodicStrip.motif column.val target packed.assignmentWord
  have decoded := assignmentOfDigit_packedAssignmentLookupOutcome
    periodicStrip packed column target
  have equivalent :
      digit = assignmentDigit state ↔
        packed.assignmentAtCell periodicStrip column target = state := by
    rw [← decoded]
    exact (assignmentOfDigit_eq_state_iff
      digit digitBound state).symm
  change pure [if digit = assignmentDigit state then 1 else 0] = _
  by_cases selected :
      packed.assignmentAtCell periodicStrip column target = state
  · have selectedRaw :
        (packed.toRaw periodicStrip).assignmentAtCell
            periodicStrip column target = state := by
      simpa using selected
    simp [equivalent.mpr selected, selectedRaw]
  · have digitNe : digit ≠ assignmentDigit state :=
      fun equal => selected (equivalent.mp equal)
    have selectedRaw : ¬
        (packed.toRaw periodicStrip).assignmentAtCell
            periodicStrip column target = state := by
      simpa using selected
    simp [digitNe, selectedRaw]

end Turing.ToPartrec.Code
