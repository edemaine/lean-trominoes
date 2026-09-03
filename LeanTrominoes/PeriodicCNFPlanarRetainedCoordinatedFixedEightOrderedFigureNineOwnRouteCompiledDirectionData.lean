/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineFinitePrefixDirectionBlock
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineOwnRouteDirectionData

/-!
# Compiled direction form of retained inherited Figure 9 routes

The actual normalized finite prefix is selected by finite clause-profile,
template-incidence, fan, and slot data.  The remaining inherited source tail
is the original tail direction word repeated by the fixed factor `144`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open Gadget

set_option maxHeartbeats 2000000

local instance ownRouteCompiledDirectionVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Exact finite-block-plus-repeated-tail form of one retained inherited
Figure 9 route. -/
theorem
    retainedOrderedFixedEightFigureNineOwnInheritedRoute_compiledDirectionWord
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clauseIndex literalIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex literalIndex)
    (first second : Cell)
    (rest : List Cell)
    (originalRouteEq :
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex =
        first :: second :: rest) :
    let clearanceSource :=
      retainedFigureNineClearancePositionedFormula source
    let clearancePlacement :=
      retainedFigureNineClearancePlacement source
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        clearanceSource clearancePlacement
    let localRoute :=
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        clearanceSource clearancePlacement clauseIndex literalIndex
    let fanData :=
      PositionedPeriodicCNF.clauseExitFanData
        data.sourceClause data.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source)
    let slot := data.sourceSlot clearanceWidth
    let profile :=
      PeriodicCNF.FormulaShapeOfFormula.clauseProfile
        (PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles
          data.sourceClause.literals)
    ∃ templateIndex :
        Fin
          (PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
            profile).incidences.length,
      unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint localRoute
              (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
                outputPlacement clearancePlacement data.sourceClause
                data.generatedClause fanData slot
                (AxisDirection.unitSubdividePolyline
                  (scalePolyline 2 (first :: second :: rest)))))) =
        PlanarOneInThreeNoUnitsFigureNine.normalizedLocalExtendedDirectionBlock
            ⟨profile, templateIndex, fanData, slot⟩ ++
          repeatDirections 144
            (unitSubdivisionDirections (second :: rest)) ∧
      ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        profile).incidenceAt templateIndex).clauseIndex =
          data.metadata.localClauseIndex ∧
      ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
        profile).incidenceAt templateIndex).literalIndex = literalIndex := by
  dsimp only
  rcases
      retainedOrderedFixedEightFigureNineOwnInheritedFinitePrefix_directionBlock
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data with
    ⟨templateIndex, prefixEq, clauseCoordinate, literalCoordinate⟩
  refine ⟨templateIndex, ?_, clauseCoordinate, literalCoordinate⟩
  rw [
    retainedOrderedFixedEightFigureNineOwnInheritedRoute_directionWord
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data first second rest originalRouteEq,
    prefixEq]

end PeriodicOrthocrossing
end LeanTrominoes
