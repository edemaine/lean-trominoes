/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenFormulaSemantics
import LeanTrominoes.PeriodicThreeSATThreeSize
import LeanTrominoes.UnaryPolynomialPaddingMachine

/-! # Exact dimensions carried by source-occurrence route tokens -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

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
  simp [literalTokens, UnaryPolynomialPaddingMachine.selectedCount,
    isClause]

@[simp] theorem selectedCount_isLiteral_literalTokens
    (index : Nat) (literal : PeriodicLiteral Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isLiteral
        (literalTokens index literal) = 1 := by
  simp [literalTokens, UnaryPolynomialPaddingMachine.selectedCount,
    isLiteral]

@[simp] theorem selectedCount_isClause_clauseTokens
    (clause : PeriodicClause Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isClause
        (clauseTokens clause) = 1 := by
  simp [clauseTokens, selectedCount_flatMap, isClause]

@[simp] theorem selectedCount_isLiteral_clauseTokens
    (clause : PeriodicClause Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isLiteral
        (clauseTokens clause) = clause.length := by
  simp [clauseTokens, selectedCount_flatMap, isLiteral]

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

@[simp] theorem selectedCount_isLiteral_formulaTokens
    (formula : PeriodicCNF Nat) :
    UnaryPolynomialPaddingMachine.selectedCount isLiteral
        (formulaTokens formula) =
      PeriodicCNF.presentationLiteralCount formula := by
  rcases formula with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      rw [show formulaTokens ⟨clause :: clauses⟩ =
          clauseTokens clause ++ formulaTokens ⟨clauses⟩ by rfl,
        selectedCount_append, selectedCount_isLiteral_clauseTokens,
        induction]
      simp [PeriodicCNF.presentationLiteralCount]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens
