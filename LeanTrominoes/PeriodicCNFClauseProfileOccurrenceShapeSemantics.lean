/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceShapeData
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount

/-! # Semantic correctness of occurrence-split formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileOccurrenceShape

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

theorem sourceProfileLiteralCount_eq
    {Variable : Type} (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (sourceProfiles.map fun profile => profile.literals.length).sum =
      PeriodicCNF.presentationLiteralCount source := by
  have lengths := congrArg (fun clauses =>
    (clauses.map List.length).sum) sourceCorrect
  calc
    (sourceProfiles.map fun profile => profile.literals.length).sum =
        ((sourceProfiles.map ClauseProfile.literals).map List.length).sum := by
      rw [List.map_map]
      rfl
    _ = ((source.clauses.map literalProfiles).map List.length).sum := lengths
    _ = PeriodicCNF.presentationLiteralCount source := by
      have profileLength :
          List.length ∘
              (literalProfiles : PeriodicClause Variable →
                List LiteralProfile) =
            List.length := by
        funext clause
        simp [literalProfiles]
      unfold PeriodicCNF.presentationLiteralCount
      rw [List.map_map, profileLength]
      simp

/-- The unary marker count is exactly the number of distinct variables in
the occurrence-split formula. -/
theorem variableCount_eq_formula
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    FormulaShape.variableCount (shape sourceProfiles) =
      (PeriodicCNF.variableOccurrences
        (PeriodicThreeSATThree.formula source)).dedup.length := by
  rw [variableCount_shape,
    sourceProfileLiteralCount_eq source sourceProfiles sourceCorrect,
    PeriodicThreeSATThree.formula_variableOccurrences_dedup_length]

/-- The same finite shape simultaneously gives the exact clause profiles and
the exact distinct-variable count of occurrence splitting. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceProfiles : List ClauseProfile)
    (sourceCorrect : sourceProfiles.map ClauseProfile.literals =
      source.clauses.map literalProfiles) :
    (FormulaShape.clauseProfiles (shape sourceProfiles)).map
        ClauseProfile.literals =
        (PeriodicThreeSATThree.formula source).clauses.map literalProfiles ∧
      FormulaShape.variableCount (shape sourceProfiles) =
        (PeriodicCNF.variableOccurrences
          (PeriodicThreeSATThree.formula source)).dedup.length := by
  constructor
  · rw [clauseProfiles_shape]
    exact ClauseProfileOccurrenceSplit.profiles_literals_eq_formula
      sourceProfiles source sourceCorrect
  · exact variableCount_eq_formula source sourceProfiles sourceCorrect

end ClauseProfileOccurrenceShape
end PeriodicCNF
end LeanTrominoes
