/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATEqualityLensCarrierInterface

/-!
# Bounding boxes for equality lenses

The canonical equality lens stays between its two endpoints and uses only
the three normal offsets `-2`, `0`, and `1`.  This file packages the exact
closed rectangle after arbitrary signed-axis placement and exposes it for
positioned equality links.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- Lower corner of the exact axis-oriented equality-lens corridor. -/
def AxisDirection.equalityLensRectangleLower
    (origin : Cell) (direction : AxisDirection) (span : Int) : Cell :=
  match direction with
  | .east => (origin.1, origin.2 - 2)
  | .north => (origin.1 - 1, origin.2)
  | .west => (origin.1 - span, origin.2 - 1)
  | .south => (origin.1 - 2, origin.2 - span)
  | .invalid => (origin.1, origin.2 - 2)

/-- Upper corner of the exact axis-oriented equality-lens corridor. -/
def AxisDirection.equalityLensRectangleUpper
    (origin : Cell) (direction : AxisDirection) (span : Int) : Cell :=
  match direction with
  | .east => (origin.1 + span, origin.2 + 1)
  | .north => (origin.1 + 2, origin.2 + span)
  | .west => (origin.1, origin.2 + 2)
  | .south => (origin.1 + 1, origin.2)
  | .invalid => (origin.1 + span, origin.2 + 1)

/-- Every point of the canonical horizontal lens stays in its exact narrow
rectangle. -/
theorem horizontalEqualityLensDrawing_routePoints_bounded
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing span).RoutePointsSatisfy
      (InClosedGridRectangle (0, -2) (span, 1)) := by
  intro incidenceIndex point pointMember
  fin_cases incidenceIndex
  all_goals
    simp only [horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensRoutes,
      equalityInstance,
      EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      List.zipIdx_cons, List.zipIdx_nil] at pointMember
  all_goals
    simp_all [horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute]
  case «0» =>
    rcases pointMember with rfl | rfl <;>
      simp [InClosedGridRectangle] <;> omega
  case «1» =>
    rcases pointMember with rfl | rfl | rfl | rfl <;>
      simp [InClosedGridRectangle] <;> omega
  case «2» =>
    rcases pointMember with rfl | rfl | rfl | rfl <;>
      simp [InClosedGridRectangle] <;> omega
  case «3» =>
    rcases pointMember with rfl | rfl <;>
      simp [InClosedGridRectangle] <;> omega

/-- Signed-axis placement transports the canonical narrow rectangle to the
corresponding physical carrier corridor. -/
theorem axisEqualityLensDrawing_routePoints_bounded
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (axisEqualityLensDrawing
      origin direction span).RoutePointsSatisfy
        (InClosedGridRectangle
          (AxisDirection.equalityLensRectangleLower
            origin direction span)
          (AxisDirection.equalityLensRectangleUpper
            origin direction span)) := by
  have canonical :=
    horizontalEqualityLensDrawing_routePoints_bounded
      span spanLarge
  have oriented :
      ((horizontalEqualityLensDrawing span).orient
        direction).RoutePointsSatisfy
          (InClosedGridRectangle
            (AxisDirection.equalityLensRectangleLower
              (0, 0) direction span)
            (AxisDirection.equalityLensRectangleUpper
              (0, 0) direction span)) :=
    canonical.mapPoints direction.orientPoint
      (fun point bounded => by
        rcases point with ⟨pointX, pointY⟩
        cases direction <;>
          simp [InClosedGridRectangle,
            AxisDirection.equalityLensRectangleLower,
            AxisDirection.equalityLensRectangleUpper,
            AxisDirection.orientPoint] at bounded ⊢ <;>
          omega)
  change
    (((horizontalEqualityLensDrawing span).orient direction).translate
      origin).RoutePointsSatisfy _
  exact
    oriented.translate origin
      (fun point bounded => by
        rcases origin with ⟨originX, originY⟩
        rcases point with ⟨pointX, pointY⟩
        cases direction <;>
          simp [InClosedGridRectangle,
            AxisDirection.equalityLensRectangleLower,
            AxisDirection.equalityLensRectangleUpper,
            Cell.add] at bounded ⊢ <;>
          omega)

/-- Logical endpoint renaming preserves the physical corridor bound. -/
theorem placedEqualityLensDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (placedEqualityLensDrawing
      first second origin direction span).RoutePointsSatisfy
        (InClosedGridRectangle
          (AxisDirection.equalityLensRectangleLower
            origin direction span)
          (AxisDirection.equalityLensRectangleUpper
            origin direction span)) := by
  unfold placedEqualityLensDrawing
  exact
    (axisEqualityLensDrawing_routePoints_bounded
      origin direction span spanLarge).rename _ _

namespace EqualityLink

/-- Lower corner of the physical corridor occupied by a positioned link. -/
def lensRectangleLower
    {Variable : Type*}
    (position : Variable → Cell) (link : EqualityLink Variable) : Cell :=
  let direction := carrierDirection position link
  AxisDirection.equalityLensRectangleLower
    (position link.first) direction (carrierSpan position link)

/-- Upper corner of the physical corridor occupied by a positioned link. -/
def lensRectangleUpper
    {Variable : Type*}
    (position : Variable → Cell) (link : EqualityLink Variable) : Cell :=
  let direction := carrierDirection position link
  AxisDirection.equalityLensRectangleUpper
    (position link.first) direction (carrierSpan position link)

/-- A geometrically certified positioned link stays inside its exact
physical carrier corridor. -/
theorem lensDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    {position : Variable → Cell} {link : EqualityLink Variable}
    (geometry : LensGeometry position link) :
    (lensDrawing position link).RoutePointsSatisfy
      (InClosedGridRectangle
        (lensRectangleLower position link)
        (lensRectangleUpper position link)) := by
  unfold lensDrawing lensRectangleLower lensRectangleUpper
  exact
    placedEqualityLensDrawing_routePoints_bounded
      link.first link.second
      (position link.first)
      (carrierDirection position link)
      (carrierSpan position link)
      geometry.spanLarge

end EqualityLink
end PlanarThreeSAT
end LeanTrominoes
