/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicIndexedFreshCount
import LeanTrominoes.PeriodicOneInThreeOccurrences
import LeanTrominoes.PeriodicSumVariableCount

/-! # Exact distinct-variable count after Figure 9 -/

namespace LeanTrominoes
namespace PeriodicOneInThree

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- The original-variable projection of a generated suffix is exactly the
source occurrence list when every source clause has width at most three. -/
theorem formulaClausesFrom_originalVariables
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable))
    (width : ∀ clause ∈ clauses, clause.WidthAtMost 3) :
    originalVariables
        (PeriodicCNF.variableOccurrences
          ⟨formulaClausesFrom start clauses⟩) =
      PeriodicCNF.variableOccurrences ⟨clauses⟩ := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      have clauseWidth : clause.WidthAtMost 3 := width clause (by simp)
      have restWidth : ∀ tailClause ∈ rest,
          tailClause.WidthAtMost 3 := by
        intro tailClause member
        exact width tailClause (by simp [member])
      rw [formulaClausesFrom_cons, variableOccurrences_append,
        SumVariableCount.originalVariables_append,
        clauseClauses_originalVariables start clause clauseWidth,
        induction (start + 1) restWidth]
      rfl

/-- The auxiliary-variable projection of a generated suffix is its explicit
list of clause-indexed local auxiliary kinds. -/
theorem formulaClausesFrom_auxiliaryVariables
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    auxiliaryVariables
        (PeriodicCNF.variableOccurrences
          ⟨formulaClausesFrom start clauses⟩) =
      IndexedFreshCount.blocksFrom start clauses clauseAuxiliaryKinds := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons, variableOccurrences_append,
        SumVariableCount.auxiliaryVariables_append,
        clauseClauses_auxiliaryVariables,
        IndexedFreshCount.blocksFrom_cons,
        induction (start + 1)]

/-- Figure 9 adds the exact sum of the distinct local auxiliary counts. -/
theorem formula_variableOccurrences_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (width : source.WidthAtMost 3) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      source.variableOccurrences.dedup.length +
        (source.clauses.map fun clause =>
          (clauseAuxiliaryKinds clause).dedup.length).sum := by
  change
    (PeriodicCNF.variableOccurrences
      ⟨formulaClausesFrom 0 source.clauses⟩).dedup.length = _
  rw [SumVariableCount.dedup_length_eq_original_add_auxiliary,
    formulaClausesFrom_originalVariables 0 source.clauses width,
    formulaClausesFrom_auxiliaryVariables,
    IndexedFreshCount.dedup_length_blocksFrom]

namespace ExactVariableCount

open PeriodicCNF.FormulaShapeFinalExactOne
open PeriodicCNF.ClauseProfileOccurrenceSplit

/-- An exact finite clause profile proves the corresponding source clause has
width at most three. -/
theorem widthAtMost_three_of_profile
    {Variable : Type} (source : PeriodicClause Variable)
    (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    source.WidthAtMost 3 := by
  have lengthEq := congrArg List.length profileEq
  cases profile <;>
    simp [ClauseProfile.literals, literalProfiles,
      PeriodicClause.WidthAtMost] at lengthEq ⊢ <;>
    omega

/-- A complete exact profile stream certifies the source width-three bound. -/
theorem source_widthAtMost_three_of_profiles
    {Variable : Type} (source : PeriodicCNF Variable)
    (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    source.WidthAtMost 3 := by
  rcases source with ⟨clauses⟩
  intro clause member
  induction clauses generalizing profiles with
  | nil => simp at member
  | cons first rest induction =>
      cases profiles with
      | nil => simp at correct
      | cons profile profiles =>
          simp only [List.map_cons, List.cons.injEq] at correct
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact widthAtMost_three_of_profile _ profile correct.1
          · exact induction profiles correct.2 member

/-- The deduplicated local auxiliary-kind list has the finite count recorded
by the formula-shape table. -/
theorem clauseAuxiliaryKinds_dedup_length_eq
    {Variable : Type} (source : PeriodicClause Variable)
    (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    (clauseAuxiliaryKinds source).dedup.length =
      figureNineFreshVariableCount profile := by
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

/-- Exact profiles convert the semantic sum of local Figure 9 auxiliaries to
the finite table's sum. -/
theorem auxiliaryCount_eq_profiles
    {Variable : Type} (clauses : List (PeriodicClause Variable))
    (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      clauses.map literalProfiles) :
    (clauses.map fun clause =>
        (clauseAuxiliaryKinds clause).dedup.length).sum =
      (profiles.map figureNineFreshVariableCount).sum := by
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

/-- With exact source profiles, Figure 9 retains every source variable and
adds exactly the profile table's number of fresh variables. -/
theorem formula_variableOccurrences_dedup_length_of_profiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      source.variableOccurrences.dedup.length +
        (profiles.map figureNineFreshVariableCount).sum := by
  rw [formula_variableOccurrences_dedup_length source
    (source_widthAtMost_three_of_profiles source profiles correct)]
  exact congrArg (source.variableOccurrences.dedup.length + ·)
    (auxiliaryCount_eq_profiles source.clauses profiles correct)

end ExactVariableCount
end PeriodicOneInThree
end LeanTrominoes
