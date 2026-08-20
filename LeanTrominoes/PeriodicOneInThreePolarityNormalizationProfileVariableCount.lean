/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfilePolarityNormalizationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactVariableCount

/-! # Exact polarity-normalization variable counts from finite profiles -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization
namespace ExactVariableCount

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicCNF.FormulaShapeFinalExactOne
open PeriodicCNF.ClauseProfileOccurrenceSplit

/-- Fresh-variable length equals the number of appended semantic complement
clauses for the same literal suffix. -/
theorem freshVariablesFrom_length_eq_complementClausesFrom
    {Variable : Type*} (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (freshVariablesFrom clauseIndex literalStart source).length =
      (complementClausesFrom clauseIndex literalStart source).length := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [freshVariablesFrom_cons, complementClausesFrom_cons,
          compatible, induction (literalStart + 1)]
      · simp [freshVariablesFrom_cons, complementClausesFrom_cons,
          compatible, induction (literalStart + 1)]

/-- The finite profile table's appended-clause count is exactly the number of
fresh semantic complement variables. -/
theorem freshVariablesFrom_length_eq_profile
    {Variable : Type} (source : PeriodicClause Variable)
    (profile : ClauseProfile)
    (profileEq : profile.literals = literalProfiles source) :
    (freshVariablesFrom 0 0 source).length =
      polarityFreshVariableCount profile := by
  have generated :=
    PeriodicCNF.ClauseProfilePolarityNormalization.clauseClauses_literalProfiles
      0 source profile profileEq
  have generatedLength := congrArg List.length generated
  simp only [List.length_map] at generatedLength
  rw [polarityFreshVariableCount, ← generatedLength]
  simp [clauseClauses, complementClauses,
    freshVariablesFrom_length_eq_complementClausesFrom]

/-- Exact profiles convert the semantic incompatible-occurrence sum into the
finite profile table's sum. -/
theorem auxiliaryCount_eq_profiles
    {Variable : Type} (clauses : List (PeriodicClause Variable))
    (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      clauses.map literalProfiles) :
    (clauses.map fun clause =>
        (freshVariablesFrom 0 0 clause).length).sum =
      (profiles.map polarityFreshVariableCount).sum := by
  induction clauses generalizing profiles with
  | nil => cases profiles <;> simp_all
  | cons clause clauses induction =>
      cases profiles with
      | nil => simp at correct
      | cons profile profiles =>
          simp only [List.map_cons, List.cons.injEq] at correct
          simp [freshVariablesFrom_length_eq_profile
            clause profile correct.1,
            induction profiles correct.2]

/-- With exact input profiles, polarity normalization adds precisely the
fresh complement-variable markers predicted by the finite table. -/
theorem formula_variableOccurrences_dedup_length_of_profiles
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (profiles : List ClauseProfile)
    (correct : profiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      source.variableOccurrences.dedup.length +
        (profiles.map polarityFreshVariableCount).sum := by
  rw [formula_variableOccurrences_dedup_length]
  exact congrArg (source.variableOccurrences.dedup.length + ·)
    (auxiliaryCount_eq_profiles source.clauses profiles correct)

end ExactVariableCount
end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
