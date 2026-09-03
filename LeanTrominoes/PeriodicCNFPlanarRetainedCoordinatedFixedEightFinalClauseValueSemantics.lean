/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseProfileListSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClausePermutationSemantics
import LeanTrominoes.PositionedPeriodicCNFFinalClauseValueProjection

/-! # Literal values of the retained final Figure 9 clause order -/

set_option maxHeartbeats 800000

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicCNF
open PeriodicCNF.ClauseProfileOccurrenceSplit
open PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering
open PeriodicCNF.UnaryProgramClauseProfile

local instance finalClauseValueVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The actual retained final-clockwise positioned formula has exactly the
literal-value clause stream emitted by the finite directed Figure 9 tables.
The theorem intentionally projects away periodic offsets, which are not used
by terminal-polarity routing. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_clauseLiteralValues_eq_descriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).clauses.map fun clause =>
          clause.literals.map PeriodicLiteral.value) =
      (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
        source).flatMap finalClauseLiteralValueBlock := by
  let descriptors :=
    PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors source
  let sourceProfiles :=
    PeriodicCNF.FormulaShape.clauseProfiles
      (PeriodicCNF.FormulaShapeDirectionOrdering.shape descriptors)
  have sourceCorrect :
      sourceProfiles.map ClauseProfile.literals =
        (retainedFigureNineClearancePositionedFormula
          source).erase.clauses.map literalProfiles := by
    exact
      (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.shape_correct
        source sourceWidth sourceClausesNonempty).1
  have profileCorrect :=
    PeriodicCNF.ClauseProfileFigureNine.profiles_literals_eq_formula
      (retainedFigureNineClearancePositionedFormula source).erase
      sourceProfiles sourceCorrect
  have profileCorrectRaw :
      (PeriodicCNF.ClauseProfileFigureNine.profiles sourceProfiles).map
          ClauseProfile.literals =
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.clauses.map literalProfiles := by
    rw [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
    exact profileCorrect
  have valueCorrect :=
    PeriodicCNF.positioned_reorderedLiteralValues_eq_of_profiles
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (PeriodicCNF.ClauseProfileFigureNine.profiles sourceProfiles)
      profileCorrectRaw
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_clauses_eq_map_reorderList
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty,
    List.map_map]
  change
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).clauses.map fun clause =>
          (reorderList clause.literals).map PeriodicLiteral.value) =
      descriptors.flatMap finalClauseLiteralValueBlock
  rw [source_finalClauseLiteralValues_eq_profiles descriptors]
  calc
    _ =
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.map fun clause =>
            reorderList
              (clause.literals.map PeriodicLiteral.value) := by
      apply List.map_congr_left
      intro clause _clauseMember
      exact (reorderList_map PeriodicLiteral.value clause.literals).symm
    _ = _ := by
      simpa only [sourceProfiles, descriptors] using valueCorrect.symm

end PeriodicOrthocrossing
end LeanTrominoes
