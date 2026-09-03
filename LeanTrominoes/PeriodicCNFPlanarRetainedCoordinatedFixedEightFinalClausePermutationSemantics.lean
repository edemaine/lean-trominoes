/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightBinaryNormalizedClauseRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightComposedRawClauseArity
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrdering
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionListPermutation

/-! # Exact final clause permutation of the retained Figure 9 formula -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

local instance finalClausePermutationVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Globally, the actual second clockwise ordering keeps clause order and
applies exactly `reorderList` to every generated clause's literals. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_clauses_eq_map_reorderList
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).clauses =
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).clauses.map fun clause =>
          { position := clause.position
            literals :=
              PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
                clause.literals } := by
  unfold
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
  exact
    PositionedPeriodicCNF.orderClausesByRouteDirection_clauses_eq_map_of
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
      (by
        intro taggedClause taggedClauseMember
        exact
          retainedOrderedFixedEight_orderClauseByRouteDirection_literals_eq_reorderList
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty taggedClauseMember
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_clauseArity
              source taggedClauseMember))

end PeriodicOrthocrossing
end LeanTrominoes
