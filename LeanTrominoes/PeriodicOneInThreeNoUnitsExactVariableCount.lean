/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData
import LeanTrominoes.PeriodicIndexedFreshCount
import LeanTrominoes.PeriodicOneInThreeNoUnitsOccurrences
import LeanTrominoes.PeriodicSumVariableCount

/-! # Exact distinct-variable count after unit-clause elimination -/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- Unit elimination preserves the complete original-variable occurrence
list. -/
theorem formulaClausesFrom_originalVariables
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    PeriodicOneInThree.originalVariables
        (PeriodicCNF.variableOccurrences
          ⟨formulaClausesFrom start clauses⟩) =
      PeriodicCNF.variableOccurrences ⟨clauses⟩ := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        PeriodicOneInThree.SumVariableCount.originalVariables_append,
        clauseClauses_originalVariables,
        induction (start + 1)]
      rfl

/-- Its auxiliary projection is the explicit list of clause-indexed local
auxiliary kinds. -/
theorem formulaClausesFrom_auxiliaryVariables
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    PeriodicOneInThree.auxiliaryVariables
        (PeriodicCNF.variableOccurrences
          ⟨formulaClausesFrom start clauses⟩) =
      IndexedFreshCount.blocksFrom start clauses clauseAuxiliaryKinds := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        PeriodicOneInThree.SumVariableCount.auxiliaryVariables_append,
        clauseClauses_auxiliaryVariables,
        IndexedFreshCount.blocksFrom_cons,
        induction (start + 1)]

/-- Unit elimination retains every source variable and adds the sum of its
distinct clause-local auxiliary counts. -/
theorem formula_variableOccurrences_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      source.variableOccurrences.dedup.length +
        (source.clauses.map fun clause =>
          (clauseAuxiliaryKinds clause).dedup.length).sum := by
  change
    (PeriodicCNF.variableOccurrences
      ⟨formulaClausesFrom 0 source.clauses⟩).dedup.length = _
  rw [PeriodicOneInThree.SumVariableCount.dedup_length_eq_original_add_auxiliary,
    formulaClausesFrom_originalVariables,
    formulaClausesFrom_auxiliaryVariables,
    IndexedFreshCount.dedup_length_blocksFrom]

namespace ExactVariableCount

open PeriodicCNF.FormulaShapeFinalExactOne
open PeriodicCNF.ClauseProfileOccurrenceSplit

/-- The local unit-elimination auxiliary count agrees with its finite clause
profile. -/
theorem clauseAuxiliaryKinds_dedup_length_eq
    {Variable : Type} (source : PeriodicClause Variable)
    (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    (clauseAuxiliaryKinds source).dedup.length =
      noUnitFreshVariableCount profile := by
  cases profile with
  | unary literalProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil => rfl
        | cons second tail =>
            simp [ClauseProfile.literals, literalProfiles] at profileEq
  | binary firstProfile secondProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil => simp [ClauseProfile.literals, literalProfiles] at profileEq
        | cons second tail =>
            cases tail with
            | nil => rfl
            | cons third tail =>
                simp [ClauseProfile.literals, literalProfiles] at profileEq
  | ternary firstProfile secondProfile thirdProfile =>
      rcases source with _ | ⟨first, rest⟩
      · simp [ClauseProfile.literals, literalProfiles] at profileEq
      · cases rest with
        | nil => simp [ClauseProfile.literals, literalProfiles] at profileEq
        | cons second tail =>
            cases tail with
            | nil =>
                simp [ClauseProfile.literals, literalProfiles] at profileEq
            | cons third tail =>
                cases tail with
                | nil => rfl
                | cons fourth tail =>
                    simp [ClauseProfile.literals, literalProfiles] at profileEq

/-- Exact clause profiles convert the semantic fresh-variable sum to the
finite table's sum. -/
theorem auxiliaryCount_eq_profiles
    {Variable : Type} (clauses : List (PeriodicClause Variable))
    (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      clauses.map literalProfiles) :
    (clauses.map fun clause =>
        (clauseAuxiliaryKinds clause).dedup.length).sum =
      (profiles.map noUnitFreshVariableCount).sum := by
  induction clauses generalizing profiles with
  | nil => cases profiles <;> simp_all
  | cons clause clauses induction =>
      cases profiles with
      | nil => simp at correct
      | cons profile profiles =>
          simp only [List.map_cons, List.cons.injEq] at correct
          simp [clauseAuxiliaryKinds_dedup_length_eq
            clause profile correct.1,
            induction profiles correct.2]

/-- With exact input profiles, unit elimination adds exactly the fresh
variables predicted by the finite profile table. -/
theorem formula_variableOccurrences_dedup_length_of_profiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      source.variableOccurrences.dedup.length +
        (profiles.map noUnitFreshVariableCount).sum := by
  rw [formula_variableOccurrences_dedup_length]
  exact congrArg (source.variableOccurrences.dedup.length + ·)
    (auxiliaryCount_eq_profiles source.clauses profiles correct)

end ExactVariableCount
end PeriodicOneInThreeNoUnits
end LeanTrominoes
