import LeanTrominoes.PeriodicGridDrawing
import LeanTrominoes.GadgetPorts

/-!
# Finite local incidence drawings

The planar 3DM reduction replaces each source vertex by a fixed finite
incidence gadget.  This file provides the small geometric certificate used
for those local replacements.

Unlike `PeriodicGridDrawing.IsPlanar`, the segment-intersection test below is
not restricted to integer witness points.  For collinear horizontal or
vertical segments it compares their open coordinate intervals directly.
Consequently a pair of coincident unit segments is rejected, which is
important before a local drawing is scaled and inserted into a larger grid.
-/

namespace LeanTrominoes

namespace GridSegment

/-- Two open one-dimensional intervals overlap.  Endpoints may be given in
either order. -/
def OpenIntervalsOverlap (firstStart firstFinish
    secondStart secondFinish : Int) : Prop :=
  min firstStart firstFinish < max secondStart secondFinish ∧
    min secondStart secondFinish < max firstStart firstFinish

instance (firstStart firstFinish secondStart secondFinish : Int) :
    Decidable
      (OpenIntervalsOverlap firstStart firstFinish
        secondStart secondFinish) := by
  unfold OpenIntervalsOverlap
  infer_instance

/-- The relative interiors of two axis-aligned segments meet in the
continuous plane. -/
def InteriorsMeet (first second : GridSegment) : Prop :=
  (first.IsHorizontal ∧ second.IsHorizontal ∧
      first.start.2 = second.start.2 ∧
      OpenIntervalsOverlap first.start.1 first.finish.1
        second.start.1 second.finish.1) ∨
    (first.IsVertical ∧ second.IsVertical ∧
      first.start.1 = second.start.1 ∧
      OpenIntervalsOverlap first.start.2 first.finish.2
        second.start.2 second.finish.2) ∨
    (first.IsHorizontal ∧ second.IsVertical ∧
      StrictlyBetween first.start.1 first.finish.1 second.start.1 ∧
      StrictlyBetween second.start.2 second.finish.2 first.start.2) ∨
    (first.IsVertical ∧ second.IsHorizontal ∧
      StrictlyBetween second.start.1 second.finish.1 first.start.1 ∧
      StrictlyBetween first.start.2 first.finish.2 second.start.2)

instance (first second : GridSegment) :
    Decidable (InteriorsMeet first second) := by
  unfold InteriorsMeet
  infer_instance

end GridSegment

/-- A finite bipartite incidence drawing.  Every triple has one incident
element of each color, and `route` draws that colored incidence. -/
structure LocalIncidenceDrawing
    (Triple Element : Type*) where
  triplePosition : Triple → Cell
  elementPosition : Element → Cell
  reference : Triple → Gadget.WireColor → Element
  route : Triple → Gadget.WireColor → List Cell

namespace LocalIncidenceDrawing

open Gadget

/-- Apply one coordinate transformation to all vertices and route points. -/
def mapPoints {Triple Element : Type*}
    (transform : Cell → Cell)
    (drawing : LocalIncidenceDrawing Triple Element) :
    LocalIncidenceDrawing Triple Element where
  triplePosition triple := transform (drawing.triplePosition triple)
  elementPosition element := transform (drawing.elementPosition element)
  reference := drawing.reference
  route triple color := (drawing.route triple color).map transform

@[simp]
theorem mapPoints_reference {Triple Element : Type*}
    (transform : Cell → Cell)
    (drawing : LocalIncidenceDrawing Triple Element)
    (triple : Triple) (color : Gadget.WireColor) :
    (drawing.mapPoints transform).reference triple color =
      drawing.reference triple color := by
  rfl

/-- A colored incidence names one route in the local drawing. -/
abbrev RouteKey (Triple : Type*) := Triple × WireColor

/-- Source position of a colored incidence route. -/
def sourcePosition {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (key : RouteKey Triple) : Cell :=
  drawing.triplePosition key.1

/-- Target position of a colored incidence route. -/
def targetPosition {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (key : RouteKey Triple) : Cell :=
  drawing.elementPosition (drawing.reference key.1 key.2)

/-- The polyline stored for a route key. -/
def routeAt {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (key : RouteKey Triple) : List Cell :=
  drawing.route key.1 key.2

/-- Every colored route starts and ends at its advertised bipartite
vertices. -/
def RoutesMatch {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element) : Prop :=
  ∀ key,
    (drawing.routeAt key).head? = some (drawing.sourcePosition key) ∧
      (drawing.routeAt key).getLast? = some (drawing.targetPosition key)

instance {Triple Element : Type*} [Fintype Triple]
    (drawing : LocalIncidenceDrawing Triple Element) :
    Decidable drawing.RoutesMatch := by
  unfold RoutesMatch
  infer_instance

/-- Every segment of every colored route is horizontal or vertical. -/
def IsOrthogonal {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element) : Prop :=
  ∀ key, ∀ segment ∈ gridPolylineSegments (drawing.routeAt key),
    segment.IsAxisAligned

instance {Triple Element : Type*} [Fintype Triple]
    (drawing : LocalIncidenceDrawing Triple Element) :
    Decidable drawing.IsOrthogonal := by
  unfold IsOrthogonal
  infer_instance

/-- One polyline has no repeated point, no point in the interior of one of
its segments, and no overlap or crossing between distinct segment
interiors. -/
def RouteIsSimple (route : List Cell) : Prop :=
  route.Nodup ∧
    (∀ point ∈ route, ∀ segment ∈ gridPolylineSegments route,
      ¬segment.InteriorContains point) ∧
    ∀ first ∈ (gridPolylineSegments route).zipIdx,
      ∀ second ∈ (gridPolylineSegments route).zipIdx,
        first.2 ≠ second.2 →
          ¬GridSegment.InteriorsMeet first.1 second.1

instance (route : List Cell) : Decidable (RouteIsSimple route) := by
  unfold RouteIsSimple
  infer_instance

/-- Two different incidence routes have disjoint relative interiors, and no
listed point of the first lies in a segment interior of the second. -/
def RoutesAvoidEachOther {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (first second : RouteKey Triple) : Prop :=
  (∀ firstSegment ∈
        gridPolylineSegments (drawing.routeAt first),
      ∀ secondSegment ∈
          gridPolylineSegments (drawing.routeAt second),
        ¬GridSegment.InteriorsMeet firstSegment secondSegment) ∧
    ∀ point ∈ drawing.routeAt first,
      ∀ secondSegment ∈
          gridPolylineSegments (drawing.routeAt second),
        ¬secondSegment.InteriorContains point

instance {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (first second : RouteKey Triple) :
    Decidable (drawing.RoutesAvoidEachOther first second) := by
  unfold RoutesAvoidEachOther
  infer_instance

/-- A point shared by two different route polylines must be an endpoint of
both routes. -/
def RoutesMeetOnlyAtEndpoints {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (first second : RouteKey Triple) : Prop :=
  ∀ point,
    point ∈ drawing.routeAt first →
      point ∈ drawing.routeAt second →
        (point = drawing.sourcePosition first ∨
          point = drawing.targetPosition first) ∧
        (point = drawing.sourcePosition second ∨
          point = drawing.targetPosition second)

instance {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (first second : RouteKey Triple) :
    Decidable (drawing.RoutesMeetOnlyAtEndpoints first second) := by
  unfold RoutesMeetOnlyAtEndpoints
  infer_instance

/-- No triple or element vertex lies in a route interior. -/
def VerticesAvoidRouteInteriors
    {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element) : Prop :=
  (∀ triple key segment,
      segment ∈ gridPolylineSegments (drawing.routeAt key) →
        ¬segment.InteriorContains (drawing.triplePosition triple)) ∧
    ∀ element key segment,
      segment ∈ gridPolylineSegments (drawing.routeAt key) →
        ¬segment.InteriorContains (drawing.elementPosition element)

instance {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element]
    [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element) :
    Decidable drawing.VerticesAvoidRouteInteriors := by
  unfold VerticesAvoidRouteInteriors
  infer_instance

/-- Distinct graph vertices occupy distinct points, including across the two
parts of the bipartition. -/
def VertexPositionsDistinct
    {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element) : Prop :=
  Function.Injective drawing.triplePosition ∧
    Function.Injective drawing.elementPosition ∧
    ∀ triple element,
      drawing.triplePosition triple ≠ drawing.elementPosition element

instance {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element]
    [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element) :
    Decidable drawing.VertexPositionsDistinct := by
  unfold VertexPositionsDistinct Function.Injective
  infer_instance

/-- Exact finite nonintersection certificate for a local gadget drawing. -/
def IsPlanar {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element) : Prop :=
  (∀ key, RouteIsSimple (drawing.routeAt key)) ∧
    (∀ first second,
      first ≠ second →
        drawing.RoutesAvoidEachOther first second ∧
          drawing.RoutesMeetOnlyAtEndpoints first second) ∧
    drawing.VerticesAvoidRouteInteriors ∧
    drawing.VertexPositionsDistinct

instance {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element]
    [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element) :
    Decidable drawing.IsPlanar := by
  unfold IsPlanar
  infer_instance

/-- A complete local geometric certificate. -/
def IsValid {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element) : Prop :=
  drawing.RoutesMatch ∧ drawing.IsOrthogonal ∧ drawing.IsPlanar

instance {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element]
    [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element) :
    Decidable drawing.IsValid := by
  unfold IsValid
  infer_instance

end LocalIncidenceDrawing

end LeanTrominoes
