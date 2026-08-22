/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverClauseNormalization
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataData
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # First directions of retained crossover routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Placing and scoping the fixed crossover drawing translates every route
but leaves its first compass direction unchanged. -/
theorem crossover_routeFirstDirection_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (localClauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (((DrawingPlanarSATClauseSource.crossover
            crossing localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex) =
      AxisDirection.polylineFirstDirection
        (crossoverStraightIncidenceDrawing.routes
          localClauseIndex literalIndex) := by
  change AxisDirection.polylineFirstDirection
      ((crossoverStraightIncidenceDrawing.routes
        localClauseIndex literalIndex).map
          (Cell.add (crossingMacroOrigin crossing))) = _
  change AxisDirection.polylineFirstDirection
      (PeriodicOrthocrossing.translatePolyline
        (crossingMacroOrigin crossing)
        (crossoverStraightIncidenceDrawing.routes
          localClauseIndex literalIndex)) = _
  exact AxisDirection.polylineFirstDirection_translatePolyline
    (crossingMacroOrigin crossing)
    (crossoverStraightIncidenceDrawing.routes
      localClauseIndex literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
