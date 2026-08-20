/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFinalExactOneSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData
import LeanTrominoes.PeriodicOneInThreeExactVariableCount
import LeanTrominoes.PeriodicOneInThreeNoUnitsExactVariableCount
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationProfileVariableCount

/-! # Exact semantics of final exact-one formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFinalExactOne

open UnaryProgramClauseProfile
open ClauseProfileOccurrenceSplit

/-- Name each nested derived instance so synthesis does not exhaust its depth
while elaborating the three-stage output type. -/
local instance oneInThreeVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeVariable Variable) := inferInstance

local instance oneInThreeNoUnitVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable Variable) := inferInstance

local instance polarityNormalizedVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (PolarityNormalizedVariable Variable) := inferInstance

/-- Summing the per-source-clause fresh count is the same as summing the
three successive reductions' fresh counts over their respective exact
profile streams. -/
theorem sum_clauseFreshVariableCount (source : List ClauseProfile) :
    (source.map clauseFreshVariableCount).sum =
      (source.map figureNineFreshVariableCount).sum +
        ((source.flatMap ClauseProfileFigureNine.oneInThreeProfiles).map
          noUnitFreshVariableCount).sum +
        ((ClauseProfileFigureNine.profiles source).map
          polarityFreshVariableCount).sum := by
  induction source with
  | nil => rfl
  | cons profile source induction =>
      unfold ClauseProfileFigureNine.profiles at induction ⊢
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.map_append, List.sum_append]
      rw [induction]
      unfold clauseFreshVariableCount
      omega

/-- An exact input shape becomes the exact clause-and-variable shape after
Figure 9, unit elimination, and polarity normalization. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceShape : List FormulaShape.Token)
    (sourceClausesCorrect :
      (FormulaShape.clauseProfiles sourceShape).map
          ClauseProfile.literals =
        source.clauses.map literalProfiles)
    (sourceVariablesCorrect :
      FormulaShape.variableCount sourceShape =
        source.variableOccurrences.dedup.length) :
    (FormulaShape.clauseProfiles (shape sourceShape)).map
          ClauseProfile.literals =
        (PeriodicOneInThreePolarityNormalization.formula
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula source))).clauses.map
              literalProfiles ∧
      FormulaShape.variableCount (shape sourceShape) =
        (PeriodicCNF.variableOccurrences
          (PeriodicOneInThreePolarityNormalization.formula
            (PeriodicOneInThreeNoUnits.formula
              (PeriodicOneInThree.formula source)))).dedup.length := by
  let sourceProfiles := FormulaShape.clauseProfiles sourceShape
  have figureProfilesCorrect :=
    ClauseProfileFigureNine.oneInThree_profiles_literals_eq_formula
      source sourceProfiles sourceClausesCorrect
  have unitFreeProfilesCorrect :=
    ClauseProfileFigureNine.profiles_literals_eq_formula
      source sourceProfiles sourceClausesCorrect
  have figureCount :=
    PeriodicOneInThree.ExactVariableCount.formula_variableOccurrences_dedup_length_of_profiles
      source sourceProfiles sourceClausesCorrect
  have unitFreeCount :=
    PeriodicOneInThreeNoUnits.ExactVariableCount.formula_variableOccurrences_dedup_length_of_profiles
      (PeriodicOneInThree.formula source)
      (sourceProfiles.flatMap
        ClauseProfileFigureNine.oneInThreeProfiles)
      figureProfilesCorrect
  have normalizedCount :=
    PeriodicOneInThreePolarityNormalization.ExactVariableCount.formula_variableOccurrences_dedup_length_of_profiles
      (PeriodicOneInThreeNoUnits.formula
        (PeriodicOneInThree.formula source))
      (ClauseProfileFigureNine.profiles sourceProfiles)
      unitFreeProfilesCorrect
  constructor
  · rw [clauseProfiles_shape]
    exact ClauseProfileFinalExactOne.profiles_literals_eq_formula
      source sourceProfiles sourceClausesCorrect
  · rw [variableCount_shape, sourceVariablesCorrect]
    change
      source.variableOccurrences.dedup.length +
          (sourceProfiles.map clauseFreshVariableCount).sum = _
    calc
      source.variableOccurrences.dedup.length +
            (sourceProfiles.map clauseFreshVariableCount).sum =
          ((source.variableOccurrences.dedup.length +
              (sourceProfiles.map figureNineFreshVariableCount).sum) +
            ((sourceProfiles.flatMap
                ClauseProfileFigureNine.oneInThreeProfiles).map
              noUnitFreshVariableCount).sum) +
            ((ClauseProfileFigureNine.profiles sourceProfiles).map
              polarityFreshVariableCount).sum := by
        rw [sum_clauseFreshVariableCount]
        omega
      _ =
          (PeriodicCNF.variableOccurrences
              (PeriodicOneInThreeNoUnits.formula
                (PeriodicOneInThree.formula source))).dedup.length +
            ((ClauseProfileFigureNine.profiles sourceProfiles).map
              polarityFreshVariableCount).sum := by
        rw [← figureCount, ← unitFreeCount]
      _ =
          (PeriodicCNF.variableOccurrences
            (PeriodicOneInThreePolarityNormalization.formula
              (PeriodicOneInThreeNoUnits.formula
                (PeriodicOneInThree.formula source)))).dedup.length := by
        exact normalizedCount.symm

end FormulaShapeFinalExactOne
end PeriodicCNF
end LeanTrominoes
