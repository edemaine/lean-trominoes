/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRouteDirectionData
import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawingData

/-! # Correctness of the static routed-variable direction table -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- The explicit finite direction table agrees with the route lookup in each
fixed duplicator-arm incidence drawing. -/
theorem duplicatorArm_routeFirstDirection_eq
    (arm : DuplicatorArm)
    (localClauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        ((duplicatorArmStraightIncidenceDrawing arm).routes
          localClauseIndex literalIndex) =
      routedVariableRouteFirstDirection
        arm localClauseIndex literalIndex := by
  cases arm <;>
    rcases localClauseIndex with _ | (_ | localClauseIndex) <;>
      rcases literalIndex with _ | (_ | literalIndex) <;>
        simp [duplicatorArmStraightIncidenceDrawing,
          duplicatorArmFormula, equalityInstance,
          straightIncidenceDrawing, straightIncidenceRoutes,
          straightIncidenceRoute, duplicatorArmEqualityPositions,
          DuplicatorArmVariable.position,
          DuplicatorArm.portPosition,
          duplicatorArmCenterPosition,
          AxisDirection.polylineFirstDirection,
          AxisDirection.between,
          routedVariableRouteFirstDirection]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
