import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecFlatPackedAssignmentAtBound
import LeanTrominoes.PartrecFlatPackedAssignmentPredicates

/-!
# Evaluator-space certificates for flat packed-assignment predicates

This module lifts the complete native-field five-column lookup certificate
through digit projection, the `none` test, and comparison with a fixed
assignment state.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedAssignmentLookupDigitCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn
    target word
  getCost 0 [outcome.2.1, outcome.2.2.toNat] +
    flatPackedAssignmentLookupCost motif queriedColumn target word

theorem flatPackedAssignmentLookupDigit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentLookupDigitCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [(Code.packedAssignmentLookupOutcome motif queriedColumn target word).2.1]
      (flatPackedAssignmentLookupDigitCost motif queriedColumn target word) := by
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn target
    word
  simpa [Code.flatPackedAssignmentLookupDigitCode,
    flatPackedAssignmentLookupDigitCost, outcome] using
    comp (get 0 [outcome.2.1, outcome.2.2.toNat])
      (flatPackedAssignmentLookup motif queriedColumn target word)

def flatPackedAssignmentIsNoneCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
    target word).2.1
  isZeroCost values digit
    (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)

theorem flatPackedAssignmentIsNone
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentIsNoneCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [if (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 = 0 then 1 else 0]
      (flatPackedAssignmentIsNoneCost motif queriedColumn target word) := by
  simpa [Code.flatPackedAssignmentIsNoneCode,
    flatPackedAssignmentIsNoneCost] using
    isZero (flatPackedAssignmentLookupDigit motif queriedColumn target word)

def flatPackedAssignmentIsArgumentsCost
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
    target word).2.1
  prependCost values [digit] [RawWindowState.assignmentDigit state]
    (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)
    (numeralCost (RawWindowState.assignmentDigit state) values)

theorem flatPackedAssignmentIsArguments
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
    EvaluatorCodeFits (Code.flatPackedAssignmentIsArgumentsCode state)
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [digit, RawWindowState.assignmentDigit state]
      (flatPackedAssignmentIsArgumentsCost state motif queriedColumn target
        word) := by
  simp only
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  simpa [Code.flatPackedAssignmentIsArgumentsCode,
    flatPackedAssignmentIsArgumentsCost, prependCost, values] using
    prepend (flatPackedAssignmentLookupDigit motif queriedColumn target word)
      (numeral (RawWindowState.assignmentDigit state) values)

def flatPackedAssignmentIsCost
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
    target word).2.1
  natEqCost digit (RawWindowState.assignmentDigit state) +
    flatPackedAssignmentIsArgumentsCost state motif queriedColumn target word

theorem flatPackedAssignmentIs
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
    EvaluatorCodeFits (Code.flatPackedAssignmentIsCode state)
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [if digit = RawWindowState.assignmentDigit state then 1 else 0]
      (flatPackedAssignmentIsCost state motif queriedColumn target word) := by
  simp only
  simpa [Code.flatPackedAssignmentIsCode, flatPackedAssignmentIsCost] using
    comp
      (natEq
        (Code.packedAssignmentLookupOutcome motif queriedColumn target word).2.1
        (RawWindowState.assignmentDigit state))
      (flatPackedAssignmentIsArguments state motif queriedColumn target word)

theorem flatPackedAssignmentIs_semantic
    (state : Option SquareSymmetry)
    (periodicStrip : PeriodicStrip) (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    EvaluatorCodeFits (Code.flatPackedAssignmentIsCode state)
      ([periodicStrip.motif.length, column.val,
          Encodable.encode target.1, Encodable.encode target.2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [(decide (packed.assignmentAtCell periodicStrip column target =
        state)).toNat]
      (flatPackedAssignmentIsCost state periodicStrip.motif column.val target
        packed.assignmentWord) := by
  let digit := (Code.packedAssignmentLookupOutcome periodicStrip.motif
    column.val target packed.assignmentWord).2.1
  have digitBound : digit < 9 := by
    simpa [digit] using Code.packedAssignmentLookupOutcome_digit_lt
      periodicStrip.motif column.val target packed.assignmentWord
  have decoded := Code.assignmentOfDigit_packedAssignmentLookupOutcome
    periodicStrip packed column target
  have equivalent :
      digit = RawWindowState.assignmentDigit state ↔
        packed.assignmentAtCell periodicStrip column target = state := by
    rw [← decoded]
    exact (Code.assignmentOfDigit_eq_state_iff digit digitBound state).symm
  have outputEq :
      (if digit = RawWindowState.assignmentDigit state then 1 else 0) =
        (decide (packed.assignmentAtCell periodicStrip column target =
          state)).toNat := by
    by_cases selected :
        packed.assignmentAtCell periodicStrip column target = state
    · rw [if_pos (equivalent.mpr selected)]
      have selectedRaw :
          (packed.toRaw periodicStrip).assignmentAtCell periodicStrip column
            target = state := by simpa using selected
      simp [selectedRaw]
    · rw [if_neg (fun equal => selected (equivalent.mp equal))]
      have selectedRaw : ¬
          (packed.toRaw periodicStrip).assignmentAtCell periodicStrip column
            target = state := by simpa using selected
      simp [selectedRaw]
  have fitted := flatPackedAssignmentIs state periodicStrip.motif column.val
    target packed.assignmentWord
  simpa [digit, outputEq] using fitted

end EvaluatorCodeFits
end PartrecToTM2
end Turing
