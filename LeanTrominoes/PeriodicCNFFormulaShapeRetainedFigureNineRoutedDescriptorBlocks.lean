/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData

/-! # Routed descriptor blocks of the retained Figure 9 formula -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing

/-- The final positioned fixed-eight formula is exactly its copied-clause
prefix followed by its positioned implication-cycle suffix. -/
theorem finalPositionedFormula_clauses_eq_descriptorBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source).clauses =
      copiedOccurrenceClauses source ++ finalCycleClauses source := by
  unfold
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    PeriodicEightOccurrenceSplit.retainedAngularFanSourceScaledRefinedFormula
    PeriodicEightOccurrenceSplit.retainedAngularFanRefinedFormula
  rw [PositionedPeriodicCNF.scale_clauses]
  unfold PeriodicEightOccurrenceSplitPositioned.formula
  rw [List.map_append]
  apply congrArg₂ List.append
  · unfold copiedOccurrenceClauses copiedOccurrenceClause
    unfold occurrencePortsForFigureSeven sourceScaledForFigureSeven
      routesScaledForFigureSeven finalCoordinatedSource
      finalCoordinatedSourceRoutes
    unfold PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map, List.map_map, List.map_map]
    apply List.map_congr_left
    rintro ⟨clause, clauseIndex⟩ _clauseMember
    rfl
  · rfl

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
