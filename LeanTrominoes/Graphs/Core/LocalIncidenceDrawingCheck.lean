/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Core.LocalIncidenceDrawing
import LeanTrominoes.Computation.Encoding.Finite.FiniteBoolCheck

namespace LeanTrominoes.LocalIncidenceDrawing

open Gadget

/-- A simple-polyline check with Boolean loops over its concrete segments. -/
def routeIsSimpleCheck (route : List Cell) : Bool :=
  let segments := gridPolylineSegments route
  decide route.Nodup &&
    route.all (fun point => segments.all (fun segment =>
      !decide (segment.InteriorContains point))) &&
    segments.zipIdx.all (fun first => segments.zipIdx.all (fun second =>
      decide (first.2 = second.2) ||
        !decide (GridSegment.InteriorsMeet first.1 second.1)))

@[simp]
theorem routeIsSimpleCheck_eq_true (route : List Cell) :
    routeIsSimpleCheck route = true ↔ RouteIsSimple route := by
  simp [routeIsSimpleCheck, RouteIsSimple, List.all_eq_true,
    Bool.and_eq_true, Bool.or_eq_true, or_iff_not_imp_left, and_assoc]

/-- Boolean loops for the continuous nonintersection conditions. -/
def routesAvoidEachOtherCheck (first second : List Cell) : Bool :=
  let firstSegments := gridPolylineSegments first
  let secondSegments := gridPolylineSegments second
  firstSegments.all (fun a => secondSegments.all (fun b =>
    !decide (GridSegment.InteriorsMeet a b))) &&
    first.all (fun point => secondSegments.all (fun segment =>
      !decide (segment.InteriorContains point)))

@[simp]
theorem routesAvoidEachOtherCheck_eq_true {Triple Element : Type*}
    (drawing : LocalIncidenceDrawing Triple Element)
    (first second : RouteKey Triple) :
    routesAvoidEachOtherCheck (drawing.routeAt first) (drawing.routeAt second) = true ↔
      drawing.RoutesAvoidEachOther first second := by
  simp [routesAvoidEachOtherCheck, RoutesAvoidEachOther, List.all_eq_true,
    Bool.and_eq_true]

/-- A reflected validity check.  Its proof below relates every Boolean loop
back to the original endpoint, orthogonality, and planarity predicates. -/
def isValidCheck {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element] [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element) : Bool :=
  (finiteAll fun key : RouteKey Triple =>
    decide ((drawing.routeAt key).head? = some (drawing.sourcePosition key) ∧
      (drawing.routeAt key).getLast? = some (drawing.targetPosition key))) &&
  (finiteAll fun key : RouteKey Triple =>
    (gridPolylineSegments (drawing.routeAt key)).all fun segment =>
      decide segment.IsAxisAligned) &&
  (finiteAll fun key : RouteKey Triple => routeIsSimpleCheck (drawing.routeAt key)) &&
  (finiteAll fun first : RouteKey Triple => finiteAll fun second : RouteKey Triple =>
    decide (first = second) ||
      (routesAvoidEachOtherCheck (drawing.routeAt first) (drawing.routeAt second) &&
        (drawing.routeAt first).all fun point =>
          decide (point ∈ drawing.routeAt second →
            (point = drawing.sourcePosition first ∨ point = drawing.targetPosition first) ∧
            (point = drawing.sourcePosition second ∨ point = drawing.targetPosition second)))) &&
  (finiteAll fun triple : Triple => finiteAll fun key : RouteKey Triple =>
    (gridPolylineSegments (drawing.routeAt key)).all fun segment =>
      !decide (segment.InteriorContains (drawing.triplePosition triple))) &&
  (finiteAll fun element : Element => finiteAll fun key : RouteKey Triple =>
    (gridPolylineSegments (drawing.routeAt key)).all fun segment =>
      !decide (segment.InteriorContains (drawing.elementPosition element))) &&
  (finiteAll fun first : Triple => finiteAll fun second : Triple =>
    decide (drawing.triplePosition first = drawing.triplePosition second → first = second)) &&
  (finiteAll fun first : Element => finiteAll fun second : Element =>
    decide (drawing.elementPosition first = drawing.elementPosition second → first = second)) &&
  (finiteAll fun triple : Triple => finiteAll fun element : Element =>
    decide (drawing.triplePosition triple ≠ drawing.elementPosition element))

@[simp]
theorem isValidCheck_eq_true {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element] [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element) :
    drawing.isValidCheck = true ↔ drawing.IsValid := by
  simp [isValidCheck, IsValid, RoutesMatch, IsOrthogonal, IsPlanar,
    VerticesAvoidRouteInteriors, VertexPositionsDistinct, Function.Injective,
    RoutesMeetOnlyAtEndpoints, List.all_eq_true, Bool.and_eq_true,
    Bool.or_eq_true, or_iff_not_imp_left, and_assoc]

/-- A closed Boolean certificate proves validity in Lean's kernel. -/
theorem isValid_of_check {Triple Element : Type*}
    [DecidableEq Triple] [DecidableEq Element] [Fintype Triple] [Fintype Element]
    (drawing : LocalIncidenceDrawing Triple Element)
    (checked : drawing.isValidCheck = true) : drawing.IsValid :=
  (isValidCheck_eq_true drawing).mp checked

end LeanTrominoes.LocalIncidenceDrawing
