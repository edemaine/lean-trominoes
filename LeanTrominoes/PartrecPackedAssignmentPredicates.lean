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

end Turing.ToPartrec.Code
