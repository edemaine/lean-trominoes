/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.FiniteBoolCheck

namespace LeanTrominoes

/-- Boolean implication for a decidable guard. -/
def guardedCheck (guard : Prop) [Decidable guard] (checked : Bool) : Bool :=
  !decide guard || checked

@[simp]
theorem guardedCheck_eq_true (guard : Prop) [Decidable guard] (checked : Bool) :
    guardedCheck guard checked = true ↔ (guard → checked = true) := by
  simp [guardedCheck, Bool.or_eq_true, or_iff_not_imp_left]

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Boolean loops for separation that permits shared polyline endpoints. -/
def routesAvoidEachOtherCheck (first second : List Cell) : Bool :=
  let firstSegments := gridPolylineSegments first
  let secondSegments := gridPolylineSegments second
  firstSegments.all (fun a => secondSegments.all (fun b =>
    !decide (GridSegment.InteriorsMeet a b))) &&
    first.all (fun point => secondSegments.all (fun segment =>
      !decide (segment.InteriorContains point))) &&
    second.all (fun point => firstSegments.all (fun segment =>
      !decide (segment.InteriorContains point))) &&
    first.all (fun a => second.all (fun b =>
      guardedCheck (a = b)
        (decide (RoutePointIsEndpoint first a) && decide (RoutePointIsEndpoint second b))))

@[simp]
theorem routesAvoidEachOtherCheck_eq_true (first second : List Cell) :
    routesAvoidEachOtherCheck first second = true ↔ RoutesAvoidEachOther first second := by
  simp only [routesAvoidEachOtherCheck, RoutesAvoidEachOther,
    SegmentInteriorsDisjoint, RoutePointsAvoidInteriors, RoutesMeetOnlyAtEndpoints,
    List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, guardedCheck_eq_true, List.forall_mem_iff_get, and_assoc]

/-- Check continuous route separation with nondependent Boolean list loops. -/
def routesStrictlyAvoidEachOtherCheck (first second : List Cell) : Bool :=
  let firstSegments := gridPolylineSegments first
  let secondSegments := gridPolylineSegments second
  firstSegments.all (fun a => secondSegments.all (fun b =>
    !decide (GridSegment.InteriorsMeet a b))) &&
    first.all (fun point => secondSegments.all (fun segment =>
      !decide (segment.InteriorContains point))) &&
    second.all (fun point => firstSegments.all (fun segment =>
      !decide (segment.InteriorContains point))) &&
    first.all (fun a => second.all (fun b => decide (a ≠ b)))

@[simp]
theorem routesStrictlyAvoidEachOtherCheck_eq_true (first second : List Cell) :
    routesStrictlyAvoidEachOtherCheck first second = true ↔
      RoutesStrictlyAvoidEachOther first second := by
  simp [routesStrictlyAvoidEachOtherCheck, RoutesStrictlyAvoidEachOther,
    List.all_eq_true, Bool.and_eq_true, and_assoc]

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
end LeanTrominoes
