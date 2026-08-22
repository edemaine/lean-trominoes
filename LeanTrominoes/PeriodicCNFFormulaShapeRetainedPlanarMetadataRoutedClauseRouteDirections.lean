/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalization
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # First directions of retained routed source-clause routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every route of the direct fixed source-clause star is diagonal, so the
axis-direction lookup returns its total fallback.  The same statement covers
out-of-range route indices. -/
theorem routedClausePort_routeFirstDirection_eq_invalid
    (literals : List (DuplicatorArm × Bool))
    (literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        ((routedClausePortStraightIncidenceDrawing literals).routes
          0 literalIndex) = .invalid := by
  simp [routedClausePortStraightIncidenceDrawing,
    routedClausePortFormula, straightIncidenceDrawing,
    straightIncidenceRoutes]
  cases lookup : literals[literalIndex]? with
  | none =>
      simp [AxisDirection.polylineFirstDirection]
  | some literal =>
      rcases literal with ⟨arm, value⟩
      cases arm <;>
        simp [straightIncidenceRoute,
          DuplicatorArm.portPosition,
          AxisDirection.polylineFirstDirection,
          AxisDirection.between]

/-- The placed routed source-clause drawing has the same invalid first-axis
fallback as its untranslated fixed star. -/
theorem routedClause_routeFirstDirection_eq_invalid
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (((DrawingPlanarSATClauseSource.routedClause site).incidenceDrawing
          source).routes 0 literalIndex) = .invalid := by
  change AxisDirection.polylineFirstDirection
      (((routedClausePortStraightIncidenceDrawing
        (routedClausePortLiterals source site)).routes
          0 literalIndex).map
            (Cell.add (routedClauseOrigin source site))) = _
  change AxisDirection.polylineFirstDirection
      (PeriodicOrthocrossing.translatePolyline
        (routedClauseOrigin source site)
        ((routedClausePortStraightIncidenceDrawing
          (routedClausePortLiterals source site)).routes
            0 literalIndex)) = _
  rw [AxisDirection.polylineFirstDirection_translatePolyline]
  exact routedClausePort_routeFirstDirection_eq_invalid _ _

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
