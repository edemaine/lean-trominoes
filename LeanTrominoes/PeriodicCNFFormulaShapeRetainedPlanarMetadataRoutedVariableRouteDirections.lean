/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseNormalizationAt
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRouteDirectionTableSemantics
import LeanTrominoes.OrthogonalPolylineEndpointDirectionTranslation

/-! # First directions of retained routed-variable routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Placing and scoping a fixed duplicator-arm drawing translates every
route but leaves its first compass direction unchanged. -/
theorem routedVariable_routeFirstDirection_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (((DrawingPlanarSATClauseSource.routedVariable
            site armIndex arm link localClauseIndex).incidenceDrawing
              source).routes localClauseIndex literalIndex) =
      routedVariableRouteFirstDirection
        arm localClauseIndex literalIndex := by
  change AxisDirection.polylineFirstDirection
      (((duplicatorArmStraightIncidenceDrawing arm).routes
        localClauseIndex literalIndex).map
          (Cell.add (routedVariableOrigin source site))) = _
  change AxisDirection.polylineFirstDirection
      (PeriodicOrthocrossing.translatePolyline
        (routedVariableOrigin source site)
        ((duplicatorArmStraightIncidenceDrawing arm).routes
          localClauseIndex literalIndex)) = _
  exact AxisDirection.polylineFirstDirection_translatePolyline_static _ _
    |>.trans (duplicatorArm_routeFirstDirection_eq
      arm localClauseIndex literalIndex)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
