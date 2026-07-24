import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecPackedAssignmentPredicates

/-!
# Explicit packed-overlap predicate at one motif occurrence

The four shared columns of adjacent packed windows are compared one motif
occurrence at a time.  This module performs the two arithmetic assignment
lookups and compares their base-nine digits without decoding either complete
frontier state.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState

def packedOverlapAtInput
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : List Nat :=
  [Encodable.encode motif, currentColumn, nextColumn,
    Encodable.encode base, currentWord, nextWord]

/-- Inputs for the assignment lookup in the current window. -/
def packedOverlapCurrentArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 3) (get 4)

@[simp]
theorem packedOverlapCurrentArgumentsCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapCurrentArgumentsCode.eval
        (packedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [Encodable.encode motif, currentColumn,
          Encodable.encode base, currentWord] := by
  simp [packedOverlapCurrentArgumentsCode,
    packedOverlapAtInput]

/-- Inputs for the assignment lookup in the next window. -/
def packedOverlapNextArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 2) <|
      prepend (get 3) (get 5)

@[simp]
theorem packedOverlapNextArgumentsCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapNextArgumentsCode.eval
        (packedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [Encodable.encode motif, nextColumn,
          Encodable.encode base, nextWord] := by
  simp [packedOverlapNextArgumentsCode,
    packedOverlapAtInput]

def packedOverlapCurrentDigitCode : Code :=
  packedAssignmentLookupDigitCode.comp
    packedOverlapCurrentArgumentsCode

@[simp]
theorem packedOverlapCurrentDigitCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapCurrentDigitCode.eval
        (packedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [(packedAssignmentLookupOutcome motif currentColumn
          base currentWord).2.1] := by
  simp [packedOverlapCurrentDigitCode]

def packedOverlapNextDigitCode : Code :=
  packedAssignmentLookupDigitCode.comp
    packedOverlapNextArgumentsCode

@[simp]
theorem packedOverlapNextDigitCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapNextDigitCode.eval
        (packedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [(packedAssignmentLookupOutcome motif nextColumn
          base nextWord).2.1] := by
  simp [packedOverlapNextDigitCode]

/-- Assemble the two selected base-nine digits for natural equality. -/
def packedOverlapEqualityArgumentsCode : Code :=
  prepend packedOverlapCurrentDigitCode
    packedOverlapNextDigitCode

@[simp]
theorem packedOverlapEqualityArgumentsCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapEqualityArgumentsCode.eval
        (packedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [(packedAssignmentLookupOutcome motif currentColumn
            base currentWord).2.1,
          (packedAssignmentLookupOutcome motif nextColumn
            base nextWord).2.1] := by
  simp [packedOverlapEqualityArgumentsCode]

/-- Return one exactly when the two packed assignments agree at one shared
motif occurrence. -/
def packedOverlapAtCode : Code :=
  natEqCode.comp packedOverlapEqualityArgumentsCode

@[simp]
theorem packedOverlapAtCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapAtCode.eval
        (packedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [if
          (packedAssignmentLookupOutcome motif currentColumn
              base currentWord).2.1 =
            (packedAssignmentLookupOutcome motif nextColumn
              base nextWord).2.1
        then 1 else 0] := by
  simp [packedOverlapAtCode]

theorem assignmentOfDigit_eq_iff_of_lt_nine
    (left right : Nat) (leftBound : left < 9)
    (rightBound : right < 9) :
    assignmentOfDigit left = assignmentOfDigit right ↔
      left = right := by
  interval_cases left <;>
    interval_cases right <;>
    native_decide

/-- The arithmetic digit comparison is the semantic packed overlap test. -/
theorem packedOverlapAtCode_eval_semantic
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState)
    (column : Fin 4) (base : Cell) :
    packedOverlapAtCode.eval
        (packedOverlapAtInput periodicStrip.motif
          column.succ.val column.castSucc.val base
          current.assignmentWord next.assignmentWord) =
      pure
        [(current.overlapsAtBool periodicStrip
          next column base).toNat] := by
  let currentDigit :=
    (packedAssignmentLookupOutcome periodicStrip.motif
      column.succ.val base current.assignmentWord).2.1
  let nextDigit :=
    (packedAssignmentLookupOutcome periodicStrip.motif
      column.castSucc.val base next.assignmentWord).2.1
  have currentBound : currentDigit < 9 := by
    simpa [currentDigit] using
      packedAssignmentLookupOutcome_digit_lt
        periodicStrip.motif column.succ.val base
        current.assignmentWord
  have nextBound : nextDigit < 9 := by
    simpa [nextDigit] using
      packedAssignmentLookupOutcome_digit_lt
        periodicStrip.motif column.castSucc.val base
        next.assignmentWord
  have currentDecoded :=
    assignmentOfDigit_packedAssignmentLookupOutcome
      periodicStrip current column.succ base
  have nextDecoded :=
    assignmentOfDigit_packedAssignmentLookupOutcome
      periodicStrip next column.castSucc base
  have equivalent :
      currentDigit = nextDigit ↔
        current.assignmentAtCell periodicStrip column.succ base =
          next.assignmentAtCell periodicStrip column.castSucc base := by
    rw [← currentDecoded, ← nextDecoded]
    exact
      (assignmentOfDigit_eq_iff_of_lt_nine
        currentDigit nextDigit currentBound nextBound).symm
  rw [packedOverlapAtCode_eval]
  change
    pure [if currentDigit = nextDigit then 1 else 0] =
      pure
        [(decide
          (current.assignmentAtCell periodicStrip column.succ base =
            next.assignmentAtCell periodicStrip
              column.castSucc base)).toNat]
  by_cases same :
      current.assignmentAtCell periodicStrip column.succ base =
        next.assignmentAtCell periodicStrip column.castSucc base
  · have digits := equivalent.mpr same
    have tag :
        decide
            (current.assignmentAtCell periodicStrip column.succ base =
              next.assignmentAtCell periodicStrip
                column.castSucc base) =
          true := by
      rw [decide_eq_true_eq]
      exact same
    rw [if_pos digits, tag]
    rfl
  · have digits : currentDigit ≠ nextDigit :=
      fun equal => same (equivalent.mp equal)
    have tag :
        decide
            (current.assignmentAtCell periodicStrip column.succ base =
              next.assignmentAtCell periodicStrip
                column.castSucc base) =
          false := by
      apply Bool.eq_false_of_not_eq_true
      rw [decide_eq_true_eq]
      exact same
    rw [if_neg digits, tag]
    rfl

end Turing.ToPartrec.Code
