/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendClauseNormalizationAt
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # First directions of retained bend-corner routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The first compass direction of one route in the finite corner-equality
table. -/
def bendRouteFirstDirection
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : AxisDirection :=
  AxisDirection.polylineFirstDirection
    (cornerEqualityRoutes firstPort secondPort
      localClauseIndex literalIndex)

/-- Placing and scoping a bend's fixed corner drawing translates every route
but leaves its first compass direction unchanged. -/
theorem bend_routeFirstDirection_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (localClauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (((DrawingPlanarSATClauseSource.bend
            routeBend localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex) =
      bendRouteFirstDirection routeBend.incomingPort routeBend.outgoingPort
        localClauseIndex literalIndex := by
  change AxisDirection.polylineFirstDirection
      ((cornerEqualityRoutes routeBend.incomingPort routeBend.outgoingPort
        localClauseIndex literalIndex).map
          (Cell.add (Cell.scale planarMacroScale
            (routeBend.drawingPoint source.incidenceGraph)))) = _
  change AxisDirection.polylineFirstDirection
      (PeriodicOrthocrossing.translatePolyline
        (Cell.scale planarMacroScale
          (routeBend.drawingPoint source.incidenceGraph))
        (cornerEqualityRoutes routeBend.incomingPort routeBend.outgoingPort
          localClauseIndex literalIndex)) = _
  exact AxisDirection.polylineFirstDirection_translatePolyline _ _

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
