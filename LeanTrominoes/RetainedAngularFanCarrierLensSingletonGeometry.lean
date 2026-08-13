/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanEqualityLensSingletonGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings

/-!
# Singleton escaped fans in retained carrier lenses

The equality-lens calculation is stated for the canonical signed-axis
placement.  This file transports it through the two route-preserving variable
renamings used by a planar-SAT carrier component.  Thus a singleton source
prefix in any geometrically certified carrier lens can be replaced by its
complete escaped fan while remaining separated from the other route prefix
in the same local clause.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT
open OccurrenceSplitRing

/-- The complete escaped singleton fallback remains separated from the
partner prefix in any certified planar-SAT carrier lens. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_singletonPrefix_escapedCompleteRoute_separated_from_partnerPrefix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (geometry :
      EqualityLink.LensGeometry
        (CarrierNode.position formula.incidenceGraph) link)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (factor : Nat)
    (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        ((drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes
            clauseIndex firstLiteralIndex).length)
    (singletonPrefix :
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).routes
          clauseIndex firstLiteralIndex).dropLast.length = 1) :
    ∃ port : Port, ∃ length : Nat,
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector
            ((drawingPlanarSATCarrierLensIncidenceDrawing
              formula link).routes
                clauseIndex firstLiteralIndex)) =
        some (.compass port, length) ∧
      (EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                ((drawingPlanarSATCarrierLensIncidenceDrawing
                  formula link).routes
                    clauseIndex firstLiteralIndex)).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot)
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              ((drawingPlanarSATCarrierLensIncidenceDrawing
                formula link).routes
                  clauseIndex secondLiteralIndex))).dropLast ∧
        EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                ((drawingPlanarSATCarrierLensIncidenceDrawing
                  formula link).routes
                    clauseIndex firstLiteralIndex)).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot)
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              ((drawingPlanarSATCarrierLensIncidenceDrawing
                formula link).routes
                  clauseIndex secondLiteralIndex))).dropLast) := by
  simpa [drawingPlanarSATCarrierLensIncidenceDrawing,
    EqualityLink.lensDrawing, placedEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename] using
      axisEqualityLensRoutes_singletonPrefix_escapedCompleteRoute_separated_from_partnerPrefix
        (CarrierNode.position formula.incidenceGraph link.first)
        (AxisDirection.between
          (CarrierNode.position formula.incidenceGraph link.first)
          (CarrierNode.position formula.incidenceGraph link.second))
        (AxisDirection.axisSpan
          (CarrierNode.position formula.incidenceGraph link.first)
          (CarrierNode.position formula.incidenceGraph link.second))
        geometry.spanLarge clauseIndex
        firstLiteralIndex secondLiteralIndex
        indicesDifferent secondLiteralIndexLt
        factor factorPositive slot firstLength singletonPrefix

end PeriodicEightOccurrenceSplit
end LeanTrominoes
