import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexGeometry
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Coordinate bounds for assembled planar 3DM routes

The source incidence drawing is refined by the standard factor `128` before
local 3DM gadgets are inserted.  This file begins the route-coordinate half
of the global assembly proof: the three central copies of every genuine
source incidence remain in the one-cell halo of the refined fundamental
square.

The proof uses pointwise bounds on the reversed-and-rebased source route.
The `96`, `100`, and `104` lane offsets fit strictly inside the `128` units
of slack created by refining each source grid cell.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Scaling a halo-bounded source point by the standard refinement factor and
adding any of the three standard lane offsets keeps it in the refined halo. -/
theorem standardLanePoint_insideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    {sourcePoint : Cell}
    (sourcePointInside :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes)
        |>.PositionInExpandedSquare sourcePoint)
    (color : WireColor) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare
        (Cell.add
          (standardThreeStrandLayout.laneOffset color)
          (Cell.scale standardThreeStrandLayout.factor sourcePoint)) := by
  simp only [PeriodicGridDrawing.PositionInExpandedSquare]
    at sourcePointInside ⊢
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    source placement presentation.routes presentation.periodPositive]
    at sourcePointInside
  rw [assembledDrawing_gridSize]
  rcases sourcePoint with ⟨sourceX, sourceY⟩
  cases color <;>
    simp [constructedThreeStrandRouting, standardThreeStrandLayout,
      Cell.add, Cell.scale] <;>
    omega

/-- Every point on every refined central incidence lane lies in the open
one-cell halo of the assembled drawing. -/
theorem standardOccurrenceLaneRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceLaneRoute
        presentation standardThreeStrandLayout entry color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  let data := occurrenceSpliceData presentation entry
  change point ∈
    PeriodicOrthocrossing.translatePolyline
      (standardThreeStrandLayout.laneOffset color)
      (scalePolyline standardThreeStrandLayout.factor
        (presentation.variableToClauseRoute data.indexed.1))
    at pointMember
  unfold PeriodicOrthocrossing.translatePolyline
    scalePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨scaledPoint, scaledPointMember, pointEq⟩
  rcases List.mem_map.mp scaledPointMember with
    ⟨sourcePoint, sourcePointMember, scaledPointEq⟩
  subst scaledPoint
  subst point
  apply standardLanePoint_insideExpandedSquare presentation
  exact sourceBounds data.indexed data.indexedMember
    sourcePoint sourcePointMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
