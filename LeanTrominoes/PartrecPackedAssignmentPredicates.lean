/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecPackedAssignmentAt

/-!
# Predicates on packed assignment lookups

The first consumer of the five-column lookup is the test that an assignment
is absent.  Since digit zero is the canonical `none` symbol and every exposed
base-nine digit is below nine, this is one fitted zero test after lookup.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState

/-- Every completed lookup returns a genuine base-nine digit. -/
theorem packedAssignmentLookupOutcome_digit_lt
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    (packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 < 9 := by
  by_cases member : target ∈ motif
  · by_cases columnBound : queriedColumn < 5
    · let column : Fin 5 := ⟨queriedColumn, columnBound⟩
      rw [show queriedColumn = column.val from rfl]
      rw [packedAssignmentLookupOutcome_digit_of_mem
        motif target word column member]
      exact Nat.mod_lt _ (by omega)
    · have outcome :=
        show (packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1 = 0 by
          have ne0 : queriedColumn ≠ 0 := by omega
          have ne1 : queriedColumn ≠ 1 := by omega
          have ne2 : queriedColumn ≠ 2 := by omega
          have ne3 : queriedColumn ≠ 3 := by omega
          have ne4 : queriedColumn ≠ 4 := by omega
          simp [packedAssignmentLookupOutcome,
            packedAssignmentLookupApplyColumn,
            ne0, ne1, ne2, ne3, ne4,
            packedLookupColumnOutcome_not_selected]
      rw [outcome]
      omega
  · have outcome :=
      packedAssignmentLookupOutcome_of_not_mem
        motif queriedColumn target word member
    rw [show
      (packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 = 0 from congrArg Prod.fst outcome]
    omega

/-- Below base nine, digit zero is the unique encoding of `none`. -/
theorem assignmentOfDigit_eq_none_iff
    (digit : Nat) (bound : digit < 9) :
    assignmentOfDigit digit = none ↔ digit = 0 := by
  interval_cases digit <;>
    native_decide

/-- Project the digit returned by the complete five-column lookup. -/
def packedAssignmentLookupDigitCode : Code :=
  (get 0).comp packedAssignmentLookupCode

@[simp]
theorem packedAssignmentLookupDigitCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupDigitCode.eval
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target, word] =
      pure
        [(packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1] := by
  simp [packedAssignmentLookupDigitCode]

/-- Return one exactly when the selected packed assignment is `none`. -/
def packedAssignmentIsNoneCode : Code :=
  isZero packedAssignmentLookupDigitCode

@[simp]
theorem packedAssignmentIsNoneCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentIsNoneCode.eval
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target, word] =
      pure
        [if (packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1 = 0 then 1 else 0] := by
  exact isZero_eval_at packedAssignmentLookupDigitCode _
    _ (packedAssignmentLookupDigitCode_eval
      motif queriedColumn target word)

theorem packedAssignmentIsNoneCode_eval_semantic
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    packedAssignmentIsNoneCode.eval
        [Encodable.encode periodicStrip.motif, column.val,
          Encodable.encode target, packed.assignmentWord] =
      pure
        [(decide
          (packed.assignmentAtCell periodicStrip column target =
            none)).toNat] := by
  rw [packedAssignmentIsNoneCode_eval]
  have digitBound :=
    packedAssignmentLookupOutcome_digit_lt
      periodicStrip.motif column.val target packed.assignmentWord
  have decoded :=
    assignmentOfDigit_packedAssignmentLookupOutcome
      periodicStrip packed column target
  have equivalence :
      (packedAssignmentLookupOutcome periodicStrip.motif
          column.val target packed.assignmentWord).2.1 = 0 ↔
        packed.assignmentAtCell periodicStrip column target = none := by
    rw [← decoded]
    exact (assignmentOfDigit_eq_none_iff _ digitBound).symm
  by_cases isNone :
      packed.assignmentAtCell periodicStrip column target = none
  · have digitZero := equivalence.mpr isNone
    rw [if_pos digitZero]
    have tag :
        decide
            (packed.assignmentAtCell periodicStrip column target =
              none) =
          true := by
      rw [decide_eq_true_eq]
      exact isNone
    rw [tag]
    rfl
  · have digitNonzero : ¬
        (packedAssignmentLookupOutcome periodicStrip.motif
          column.val target packed.assignmentWord).2.1 = 0 := by
      exact fun digitZero => isNone (equivalence.mp digitZero)
    rw [if_neg digitNonzero]
    have notTag :
        ¬ decide
            (packed.assignmentAtCell periodicStrip column target =
              none) =
          true := by
      rw [decide_eq_true_eq]
      exact isNone
    have tag :
        decide
            (packed.assignmentAtCell periodicStrip column target =
              none) =
          false :=
      Bool.eq_false_of_not_eq_true notTag
    rw [tag]
    rfl

/-- Assemble the selected packed digit and the fixed digit representing one
semantic assignment state. -/
def packedAssignmentIsArgumentsCode
    (state : Option SquareSymmetry) : Code :=
  prepend packedAssignmentLookupDigitCode
    (numeral (assignmentDigit state))

@[simp]
theorem packedAssignmentIsArgumentsCode_eval
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    (packedAssignmentIsArgumentsCode state).eval
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target, word] =
      pure
        [(packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1,
          assignmentDigit state] := by
  simp [packedAssignmentIsArgumentsCode]

/-- Return one exactly when the selected packed assignment is the fixed
semantic state. -/
def packedAssignmentIsCode
    (state : Option SquareSymmetry) : Code :=
  natEqCode.comp (packedAssignmentIsArgumentsCode state)

@[simp]
theorem packedAssignmentIsCode_eval
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    (packedAssignmentIsCode state).eval
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target, word] =
      pure
        [if (packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1 = assignmentDigit state
          then 1 else 0] := by
  simp [packedAssignmentIsCode]

/-- A genuine base-nine digit decodes to a fixed state exactly when it is the
state's canonical assignment digit. -/
theorem assignmentOfDigit_eq_state_iff
    (digit : Nat) (bound : digit < 9)
    (state : Option SquareSymmetry) :
    assignmentOfDigit digit = state ↔
      digit = assignmentDigit state := by
  interval_cases digit <;>
    cases state with
    | none => native_decide
    | some symmetry => cases symmetry <;> native_decide

/-- Semantic correctness of the fixed-state packed assignment predicate. -/
theorem packedAssignmentIsCode_eval_semantic
    (state : Option SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    (packedAssignmentIsCode state).eval
        [Encodable.encode periodicStrip.motif, column.val,
          Encodable.encode target, packed.assignmentWord] =
      pure
        [(decide
          (packed.assignmentAtCell periodicStrip column target =
            state)).toNat] := by
  let digit :=
    (packedAssignmentLookupOutcome periodicStrip.motif
      column.val target packed.assignmentWord).2.1
  have digitBound : digit < 9 := by
    simpa [digit] using
      packedAssignmentLookupOutcome_digit_lt
        periodicStrip.motif column.val target packed.assignmentWord
  have decoded :=
    assignmentOfDigit_packedAssignmentLookupOutcome
      periodicStrip packed column target
  have equivalent :
      digit = assignmentDigit state ↔
        packed.assignmentAtCell periodicStrip column target = state := by
    rw [← decoded]
    exact (assignmentOfDigit_eq_state_iff
      digit digitBound state).symm
  rw [packedAssignmentIsCode_eval]
  change pure [if digit = assignmentDigit state then 1 else 0] =
    pure [(decide
      (packed.assignmentAtCell periodicStrip column target = state)).toNat]
  by_cases selected :
      packed.assignmentAtCell periodicStrip column target = state
  · rw [if_pos (equivalent.mpr selected)]
    have selectedRaw :
        (packed.toRaw periodicStrip).assignmentAtCell
            periodicStrip column target = state := by
      simpa using selected
    simp [selectedRaw]
  · rw [if_neg (fun equal => selected (equivalent.mp equal))]
    have selectedRaw : ¬
        (packed.toRaw periodicStrip).assignmentAtCell
            periodicStrip column target = state := by
      simpa using selected
    simp [selectedRaw]

end Turing.ToPartrec.Code
