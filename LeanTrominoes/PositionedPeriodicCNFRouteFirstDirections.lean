/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # First directions of normalized periodic-CNF routes -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Subtracting a clause's common period translation from every route point
does not change the direction of its first edge. -/
@[simp]
theorem polylineFirstDirection_normalizeIncidenceRoute
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell) :
    AxisDirection.polylineFirstDirection
        (normalizeIncidenceRoute placement clause route) =
      AxisDirection.polylineFirstDirection route := by
  let offset :=
    placement.translation
      (PeriodicCNF.clauseAnchor clause.literals)
  have routeEq :
      normalizeIncidenceRoute placement clause route =
        PeriodicOrthocrossing.translatePolyline
          (Cell.scale (-1) offset) route := by
    unfold normalizeIncidenceRoute
      PeriodicOrthocrossing.translatePolyline
    apply List.map_congr_left
    intro point _pointMember
    change
      Cell.sub point offset =
        Cell.add (Cell.scale (-1) offset) point
    rcases point with ⟨pointX, pointY⟩
    rcases offset with ⟨offsetX, offsetY⟩
    simp [Cell.add, Cell.sub, Cell.scale, sub_eq_add_neg, add_comm]
  rw [routeEq]
  exact
    AxisDirection.polylineFirstDirection_translatePolyline
      (Cell.scale (-1) offset) route

end PositionedPeriodicCNF
end LeanTrominoes
