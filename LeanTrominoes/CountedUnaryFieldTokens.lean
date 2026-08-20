/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramTokenFinalizer
import LeanTrominoes.UnaryFieldHeaderRotationMachineTime

/-! # Counted finite tokens for unary natural-number fields -/

namespace LeanTrominoes
namespace CountedUnaryFieldTokens

open UnaryFieldEncoderMachine
open PeriodicCNF.UnaryProgramTokens

/-- Finite tokens expanding to one delimiter-terminated unary natural. -/
def field (number : Nat) : List Token :=
  atomTokens number ++ [.atomEnd]

/-- Finite tokens expanding to a sequence of unary natural fields. -/
def fields (numbers : List Nat) : List Token :=
  numbers.flatMap field

@[simp] theorem unaryEncode_field (number : Nat) :
    unaryEncode (field number) = unaryField number := by
  simp [field, unaryField, unaryBlock]

@[simp] theorem unaryEncode_fields (numbers : List Nat) :
    unaryEncode (fields numbers) = unaryFields numbers := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      unfold fields at induction ⊢
      rw [List.flatMap_cons, unaryEncode_append, unaryEncode_field,
        induction]
      rfl

@[simp] theorem selectedCount_field (number : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (field number) = 0 := by
  simp [field, selectedCount_append,
    UnaryPolynomialPaddingMachine.selectedCount, isClauseMarker]

@[simp] theorem selectedCount_fields (numbers : List Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (fields numbers) = 0 := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      unfold fields at induction ⊢
      rw [List.flatMap_cons, selectedCount_append, selectedCount_field,
        induction]

/-- The existing generic token counter/finalizer prepends the exact number of
clause-marker tokens to the unary expansion of every other token. -/
theorem countAndFinalize_eq_count_unaryEncode (tokens : List Token) :
    PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize tokens =
      unaryField
          (UnaryPolynomialPaddingMachine.selectedCount isClauseMarker tokens) ++
        unaryEncode tokens := by
  simp [PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize,
    PeriodicCNF.UnaryProgramTokenFinalizer.finalize,
    UnaryPolynomialPaddingMachine.paddedOutput,
    PeriodicCNF.UnaryProgramTokens.evalCoefficients_identity,
    unaryField, List.append_assoc]

/-- Counting an explicit marker prefix and expanding explicit unary field
tokens yields that count as the first unary field. -/
theorem countAndFinalize_clauseTokens_fields
    (count : Nat) (numbers : List Nat) :
    PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize
        (clauseTokens count ++ fields numbers) =
      unaryFields (count :: numbers) := by
  rw [countAndFinalize_eq_count_unaryEncode]
  rw [PeriodicCNF.UnaryProgramTokens.selectedCount_append]
  simp

/-- One counted payload block: a marker ignored by unary expansion followed
by any finite sequence of unary fields. -/
def countedFieldBlock (numbers : List Nat) : List Token :=
  .clauseMarker :: fields numbers

/-- A streamable sequence of counted payload blocks. -/
def countedFieldBlocks (blocks : List (List Nat)) : List Token :=
  blocks.flatMap countedFieldBlock

@[simp] theorem unaryEncode_countedFieldBlock (numbers : List Nat) :
    unaryEncode (countedFieldBlock numbers) = unaryFields numbers := by
  simp [countedFieldBlock, unaryBlock]

@[simp] theorem selectedCount_countedFieldBlock (numbers : List Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (countedFieldBlock numbers) = 1 := by
  simp [countedFieldBlock, isClauseMarker]

@[simp] theorem unaryEncode_countedFieldBlocks
    (blocks : List (List Nat)) :
    unaryEncode (countedFieldBlocks blocks) =
      unaryFields blocks.flatten := by
  induction blocks with
  | nil => rfl
  | cons numbers blocks induction =>
      unfold countedFieldBlocks at induction ⊢
      rw [List.flatMap_cons, unaryEncode_append,
        unaryEncode_countedFieldBlock, induction]
      change unaryFields numbers ++ unaryFields blocks.flatten =
        unaryFields (numbers ++ blocks.flatten)
      exact (PeriodicCNF.UnaryProgramTokens.unaryFields_append
        numbers blocks.flatten).symm

@[simp] theorem selectedCount_countedFieldBlocks
    (blocks : List (List Nat)) :
    UnaryPolynomialPaddingMachine.selectedCount isClauseMarker
      (countedFieldBlocks blocks) = blocks.length := by
  induction blocks with
  | nil => rfl
  | cons numbers blocks induction =>
      unfold countedFieldBlocks at induction ⊢
      rw [List.flatMap_cons,
        PeriodicCNF.UnaryProgramTokens.selectedCount_append,
        selectedCount_countedFieldBlock, induction]
      simp [Nat.add_comm]

/-- Arbitrary uncounted header fields followed by streamable counted blocks
finalize to the block count followed by the flattened field payload. -/
theorem countAndFinalize_fields_countedFieldBlocks
    (header : List Nat) (blocks : List (List Nat)) :
    PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize
        (fields header ++ countedFieldBlocks blocks) =
      unaryFields (blocks.length :: header ++ blocks.flatten) := by
  rw [countAndFinalize_eq_count_unaryEncode]
  rw [PeriodicCNF.UnaryProgramTokens.selectedCount_append,
    PeriodicCNF.UnaryProgramTokens.unaryEncode_append]
  simp

end CountedUnaryFieldTokens
end LeanTrominoes
