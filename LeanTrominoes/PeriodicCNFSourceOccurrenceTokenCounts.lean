/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenData
import LeanTrominoes.UnaryPolynomialPaddingMachine

/-! # Exact dimensions carried by source occurrence tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

/-- Select the unique header of each source clause. -/
def isClause : Token → Bool
  | .clause _ => true
  | _ => false

/-- Select the unique header of each literal occurrence. -/
def isLiteral : Token → Bool
  | .literal _ => true
  | _ => false

theorem selectedCount_append (selected : Token → Bool)
    (first second : List Token) :
    UnaryPolynomialPaddingMachine.selectedCount selected (first ++ second) =
      UnaryPolynomialPaddingMachine.selectedCount selected first +
        UnaryPolynomialPaddingMachine.selectedCount selected second := by
  induction first with
  | nil => simp [UnaryPolynomialPaddingMachine.selectedCount]
  | cons token first induction =>
      simp only [List.cons_append,
        UnaryPolynomialPaddingMachine.selectedCount_cons, induction]
      omega

theorem selectedCount_map_of_false {Value : Type}
    (selected : Token → Bool) (values : List Value) (token : Value → Token)
    (unselected : ∀ value, selected (token value) = false) :
    UnaryPolynomialPaddingMachine.selectedCount selected
        (values.map token) = 0 := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [unselected, induction]

theorem selectedCount_flatMap (selected : Token → Bool)
    {Value : Type} (values : List Value) (block : Value → List Token) :
    UnaryPolynomialPaddingMachine.selectedCount selected
        (values.flatMap block) =
      (values.map fun value =>
        UnaryPolynomialPaddingMachine.selectedCount selected
          (block value)).sum := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.flatMap_cons, selectedCount_append, List.map_cons,
        List.sum_cons, induction]

@[simp] theorem selectedCount_isClause_literalTokens
    (index : Nat) (literal : PeriodicLiteral Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClause
        (literalTokens index literal) = 0 := by
  simp [literalTokens, selectedCount_append,
    UnaryPolynomialPaddingMachine.selectedCount, isClause, atomTokens,
    offsetTokens, selectedCount_map_of_false]

@[simp] theorem selectedCount_isLiteral_literalTokens
    (index : Nat) (literal : PeriodicLiteral Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isLiteral
        (literalTokens index literal) = 1 := by
  simp [literalTokens, selectedCount_append,
    UnaryPolynomialPaddingMachine.selectedCount, isLiteral, atomTokens,
    offsetTokens, selectedCount_map_of_false]

@[simp] theorem selectedCount_isClause_clauseTokens
    (clause : PeriodicClause Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClause
        (clauseTokens clause) = 1 := by
  simp [clauseTokens, selectedCount_flatMap,
    isClause]

@[simp] theorem selectedCount_isLiteral_clauseTokens
    (clause : PeriodicClause Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isLiteral
        (clauseTokens clause) = clause.length := by
  simp [clauseTokens, selectedCount_flatMap,
    isLiteral]

/-- Clause headers count exactly the presented clauses. -/
@[simp] theorem selectedCount_isClause_formulaTokens
    (formula : PeriodicCNF Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClause
        (formulaTokens formula) = formula.clauses.length := by
  rcases formula with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      rw [show formulaTokens ⟨clause :: clauses⟩ =
          clauseTokens clause ++ formulaTokens ⟨clauses⟩ by rfl,
        selectedCount_append, selectedCount_isClause_clauseTokens,
        induction]
      simp [Nat.add_comm]

/-- Literal headers count exactly the presented literal occurrences. -/
@[simp] theorem selectedCount_isLiteral_formulaTokens
    (formula : PeriodicCNF Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isLiteral
        (formulaTokens formula) = presentationLiteralCount formula := by
  rcases formula with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      rw [show formulaTokens ⟨clause :: clauses⟩ =
          clauseTokens clause ++ formulaTokens ⟨clauses⟩ by rfl,
        selectedCount_append, selectedCount_isLiteral_clauseTokens,
        induction]
      simp [presentationLiteralCount]

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes
