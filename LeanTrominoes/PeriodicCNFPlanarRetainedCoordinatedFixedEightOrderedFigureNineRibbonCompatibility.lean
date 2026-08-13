/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineCompleteRouteSeparation

/-!
# Finite compatibility boundary for the ordered retained Figure 9 endpoint

The final normalized route family already supplies graph well-formedness,
the two presentation lengths, and exact periodic endpoints.  Consequently
its complete `IsCompatible` certificate is equivalent to the two genuinely
geometric facts about the unchanged vertex list: distinctness and strict
fundamental-square bounds.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 400000

local instance orderedRibbonCompatibilityVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- For the completed normalized Figure 9 routes, finite graph compatibility
is exactly duplicate-free, fundamental-square-bounded vertex geometry. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isCompatible_iff_vertexGeometry
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    let drawing :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
    drawing.IsCompatible
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.incidenceGraph ↔
      drawing.vertexPositions.Nodup ∧
        ∀ position ∈ drawing.vertexPositions,
          drawing.PositionInFundamentalSquare position := by
  dsimp only
  constructor
  · intro compatible
    exact ⟨compatible.2.2.2.1, compatible.2.2.2.2.1⟩
  · rintro ⟨positionsNodup, positionsInside⟩
    refine
      ⟨PeriodicCNF.incidenceGraph_isWellFormed
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase,
        ?_, ?_, positionsNodup, positionsInside, ?_⟩
    · simpa only [
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing,
        PositionedPeriodicCNF.incidenceDrawing]
        using
          PositionedPeriodicCNF.incidenceVertexPositions_length
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source)
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source)
    · simpa only [
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing,
        PositionedPeriodicCNF.incidenceDrawing]
        using
          PositionedPeriodicCNF.incidenceEdgeRoutes_length
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source)
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty)
    · exact
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_routesMatch
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty

end PeriodicOrthocrossing
end LeanTrominoes
