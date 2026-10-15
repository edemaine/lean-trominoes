/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.PeriodicThreeDMVertexNormalizationVerticalBandAffine
import LeanTrominoes.ThreeDM.PeriodicThreeDMVertexNormalizationVerticalBandFigureTwoTemplate
import LeanTrominoes.ThreeDM.PeriodicThreeDMVertexNormalizationVerticalBandCyclicTemplate
import LeanTrominoes.ThreeDM.PeriodicThreeDMVertexNormalizationVerticalBandSplice

/-! # Normalization routes remain strictly inside a fundamental square -/
namespace LeanTrominoes.PeriodicGridDrawing

def PolylineInFundamentalSquare (drawing : PeriodicGridDrawing) (route : List Cell) : Prop :=
  ∀ point∈route,drawing.PositionInFundamentalSquare point

theorem PositionInFundamentalSquare.of_segment_contains {drawing : PeriodicGridDrawing}
    {segment : GridSegment} {point : Cell}
    (start : drawing.PositionInFundamentalSquare segment.start)
    (finish : drawing.PositionInFundamentalSquare segment.finish) (contains : segment.Contains point) :
    drawing.PositionInFundamentalSquare point := by
  have inside := fundamental_of_contains start finish contains
  have upper := (mem_fundamentalPoints_iff drawing point).mp inside
  rcases contains with ⟨horizontal,same,between⟩|⟨vertical,same,between⟩
  · rcases between with between|between <;>
      simp only [PositionInFundamentalSquare,GridSegment.IsHorizontal] at * <;> omega
  · rcases between with between|between <;>
      simp only [PositionInFundamentalSquare,GridSegment.IsVertical] at * <;> omega
end LeanTrominoes.PeriodicGridDrawing
namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Mapping the normalization affine map over a route is scaling followed by
translation by the template center. -/
theorem map_normalizeVertexPosition_eq_translate_scalePolyline_for_finite_square
    (points : List Cell) :
    points.map normalizeVertexPosition =
      translatePolyline center
        (scalePolyline vertexNormalizationScale points) := by
  induction points with
  | nil => rfl
  | cons point rest induction =>
      simp only [List.map_cons, scalePolyline_cons,
        translatePolyline, induction]
      rw [show normalizeVertexPosition point =
          Cell.add center
            (Cell.scale vertexNormalizationScale point) by
        simp [normalizeVertexPosition, Cell.add, add_comm]]

/-- The affine image of one old band point lies in the enlarged band's
interior. -/
theorem normalizeVertexPosition_inFundamentalSquare
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInFundamentalSquare position) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PositionInFundamentalSquare
        (normalizeVertexPosition position) := by
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare]
    at inside ⊢
  rw [vertexNormalizationMagnifiedUnitDrawing_gridSize]
  simp only [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add]
  have gridPositive : 0 < drawing.gridSize :=
    Nat.zero_lt_succ drawing.gridSizePred
  norm_num at inside ⊢
  repeat' constructor <;> omega

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Magnification, affine translation, and ordered unit subdivision preserve
pointwise vertical-band membership for an orthogonal polyline. -/
theorem magnifiedUnitRoute_inFundamentalSquare
    {drawing : PeriodicGridDrawing} {route : List Cell}
    (orthogonal : OrthogonalPolyline route)
    (inside : drawing.PolylineInFundamentalSquare route) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInFundamentalSquare
        (magnifiedUnitRoute route) := by
  intro point pointMember
  have mappedOrthogonal :
      OrthogonalPolyline (route.map normalizeVertexPosition) := by
    rw [map_normalizeVertexPosition_eq_translate_scalePolyline_for_finite_square]
    have scaled :
        OrthogonalPolyline
          (scalePolyline vertexNormalizationScale route) := by
      simpa [vertexNormalizationScale] using
        OrthogonalPolyline.scalePolyline orthogonal
          (factor := 12) (by norm_num)
    exact scaled.translate center
  unfold magnifiedUnitRoute at pointMember
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        mappedOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · rcases List.mem_map.mp originalMember with
      ⟨source, sourceMember, rfl⟩
    exact normalizeVertexPosition_inFundamentalSquare
      (inside source sourceMember)
  · have endpointMembers :=
      gridPolylineSegments_endpoints_mem segmentMember
    rcases List.mem_map.mp endpointMembers.1 with
      ⟨sourceStart, sourceStartMember, startEq⟩
    rcases List.mem_map.mp endpointMembers.2 with
      ⟨sourceFinish, sourceFinishMember, finishEq⟩
    apply
      PeriodicGridDrawing.PositionInFundamentalSquare.of_segment_contains
    · rw [← startEq]
      exact normalizeVertexPosition_inFundamentalSquare
        (inside sourceStart sourceStartMember)
    · rw [← finishEq]
      exact normalizeVertexPosition_inFundamentalSquare
        (inside sourceFinish sourceFinishMember)
    · exact GridSegment.contains_of_interiorContains interior

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The complete affine/unit-refinement stage preserves the open vertical
halo route by route. -/
theorem vertexNormalizationMagnifiedUnitDrawing_routePointsInFundamentalSquare
    {drawing : PeriodicGridDrawing}
    (orthogonal : drawing.IsOrthogonal)
    (inside : drawing.RoutePointsInFundamentalSquare) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.RoutePointsInFundamentalSquare := by
  intro route routeMember point pointMember
  rw [vertexNormalizationMagnifiedUnitDrawing_edgeRoutes] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨sourceRoute, sourceRouteMember, rfl⟩
  have sourceOrthogonal :=
    (PeriodicGridDrawing.isOrthogonal_iff_routes drawing).mp orthogonal
      sourceRoute sourceRouteMember
  exact magnifiedUnitRoute_inFundamentalSquare sourceOrthogonal
    (fun source sourceMember =>
      inside sourceRoute sourceRouteMember source sourceMember)
    point pointMember

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicThreeDM

/-- Every point within radius three of the affine image of an old band point
lies in the enlarged open vertical halo. -/
theorem withinThree_normalizeVertexPosition_inFundamentalSquare
    {drawing : PeriodicGridDrawing} {position point : Cell}
    (positionInside :
      drawing.PositionInFundamentalSquare position)
    (near :
      WithinCoordinateRadius 3
        (normalizeVertexPosition position) point) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PositionInFundamentalSquare point := by
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare]
    at positionInside ⊢
  rw [vertexNormalizationMagnifiedUnitDrawing_gridSize]
  simp only [WithinCoordinateRadius] at near
  have horizontalAbsolute :
      |point.1 - (normalizeVertexPosition position).1| ≤ (3 : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast near.1
  have horizontalBounds := abs_le.mp horizontalAbsolute
  have verticalAbsolute :
      |point.2 - (normalizeVertexPosition position).2| ≤ (3 : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast near.2
  have verticalBounds := abs_le.mp verticalAbsolute
  simp only [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add]
    at verticalBounds horizontalBounds
  have gridPositive : 0 < drawing.gridSize :=
    Nat.zero_lt_succ drawing.gridSizePred
  norm_num at positionInside verticalBounds horizontalBounds ⊢
  repeat' constructor <;> omega

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- The finite Figure 2 route tables lie in the radius-three box around the
local center. -/
private theorem figureTwoRoute_withinCoordinateRadius
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    ∀ point ∈ route omitted port,
      WithinCoordinateRadius 3 center point := by
  cases omitted <;> cases port <;> decide +kernel

/-- An anchored Figure 2 route at an old band point lies in the enlarged
open vertical halo. -/
theorem normalizationTemplateAt_route_inFundamentalSquare
    {drawing : PeriodicGridDrawing} {position : Cell}
    (positionInside :
      drawing.PositionInFundamentalSquare position)
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInFundamentalSquare
        (normalizationTemplateAt position (route omitted port)) := by
  intro point pointMember
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact withinThree_normalizeVertexPosition_inFundamentalSquare
    positionInside
    ((figureTwoRoute_withinCoordinateRadius
      omitted port localPoint localMember).translate
        (Cell.scale vertexNormalizationScale position))

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Every selected finite cyclic route table lies in the radius-three box
around the local center. -/
private theorem cyclicRoute_withinCoordinateRadius
    (active : Bool) (oldPort : CanonicalVertexPort) :
    ∀ point ∈ (rotationRoundPortAndRoute active oldPort).2,
      WithinCoordinateRadius 3 center point := by
  cases active <;> cases oldPort <;> decide +kernel

/-- An anchored selected cyclic-round route at an old band point lies in the
enlarged open vertical halo. -/
theorem normalizationTemplateAt_rotationRoundRoute_inFundamentalSquare
    {drawing : PeriodicGridDrawing} {position : Cell}
    (positionInside :
      drawing.PositionInFundamentalSquare position)
    (active : Bool) (oldPort : CanonicalVertexPort) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInFundamentalSquare
        (normalizationTemplateAt position
          (rotationRoundPortAndRoute active oldPort).2) := by
  intro point pointMember
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact withinThree_normalizeVertexPosition_inFundamentalSquare
    positionInside
    ((cyclicRoute_withinCoordinateRadius
      active oldPort localPoint localMember).translate
        (Cell.scale vertexNormalizationScale position))

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Splicing two band-contained local templates around the trimmed affine
image of a band-contained orthogonal route preserves the enlarged halo. -/
theorem normalizeRouteWithTemplates_inFundamentalSquare
    {drawing : PeriodicGridDrawing}
    {sourcePosition targetPosition : Cell}
    {sourceTemplate targetTemplate oldRoute : List Cell}
    (orthogonal : OrthogonalPolyline oldRoute)
    (oldInside : drawing.PolylineInFundamentalSquare oldRoute)
    (sourceInside :
      (vertexNormalizationMagnifiedUnitDrawing drawing)
        |>.PolylineInFundamentalSquare
          (normalizationTemplateAt sourcePosition sourceTemplate))
    (targetInside :
      (vertexNormalizationMagnifiedUnitDrawing drawing)
        |>.PolylineInFundamentalSquare
          (normalizationTemplateAt targetPosition targetTemplate)) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInFundamentalSquare
        (normalizeRouteWithTemplates
          sourcePosition targetPosition
          sourceTemplate targetTemplate oldRoute) := by
  intro point pointMember
  unfold normalizeRouteWithTemplates at pointMember
  rcases mem_joinAtEndpoint pointMember with
    sourceMember | remainingMember
  · exact sourceInside point sourceMember
  · rcases mem_joinAtEndpoint remainingMember with
      trimmedMember | targetReverseMember
    · have magnifiedMember : point ∈ magnifiedUnitRoute oldRoute := by
        simp only [trimmedMagnifiedRoute] at trimmedMember
        exact List.mem_of_mem_drop
          (List.mem_of_mem_take trimmedMember)
      exact magnifiedUnitRoute_inFundamentalSquare
        orthogonal oldInside point magnifiedMember
    · exact targetInside point
        (List.mem_reverse.mp targetReverseMember)

end PeriodicThreeDM
end LeanTrominoes
