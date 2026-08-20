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

end CountedUnaryFieldTokens
end LeanTrominoes
