/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingRibbonScalingSeparation
import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionRibbon

/-!
# Affine unit refinement of periodic grid drawings

Vertex normalization magnifies an entire periodic drawing, subdivides its
orthogonal routes into unit steps, and finally applies one common integral
translation.  This module packages the separation facts for that common
operation.  In particular, ribbon readiness and orthogonality supply the
complete lifted-route separation needed by ordered unit subdivision.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- In an orthogonal planar drawing, the relative interior of one lifted
segment avoids both endpoints of every distinct lifted segment occurrence. -/
theorem segmentEndpointsAvoidInteriors_of_isPlanar_of_isOrthogonal
    {drawing : PeriodicGridDrawing}
    (planar : drawing.IsPlanar)
    (orthogonal : drawing.IsOrthogonal) :
    drawing.SegmentEndpointsAvoidInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate point different interior
  have avoids := planar.1 first firstMember second secondMember
    firstTranslate secondTranslate point different interior
  have secondAligned :
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)).IsAxisAligned :=
    (GridSegment.isAxisAligned_translate _ _).mpr
      (orthogonal second secondMember)
  constructor
  · intro pointEqual
    apply avoids
    rw [pointEqual]
    exact GridSegment.contains_start_of_axisAligned secondAligned
  · intro pointEqual
    apply avoids
    rw [pointEqual]
    exact GridSegment.contains_finish_of_axisAligned secondAligned

/-- A ribbon-ready orthogonal family of nondegenerate routes has complete
pairwise separation in the periodic lift, even before unit subdivision. -/
theorem relativeLiftedRoutesAvoidEachOther_of_isRibbonReady_of_isOrthogonal
    {drawing : PeriodicGridDrawing}
    (ribbonReady : drawing.IsRibbonReady)
    (orthogonal : drawing.IsOrthogonal)
    (lengths :
      ∀ route ∈ drawing.edgeRoutes,
        2 ≤ route.length) :
    drawing.RelativeLiftedRoutesAvoidEachOther := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  have avoids :=
    routeOccurrences_avoidEachOther_of_segmentEndpointsAvoid
      ribbonReady.1
      (segmentEndpointsAvoidInteriors_of_isPlanar_of_isOrthogonal
        ribbonReady.1.1 orthogonal)
      ribbonReady.2
      firstMember secondMember
      (lengths first.1 (List.fst_mem_of_mem_zipIdx firstMember))
      (lengths second.1 (List.fst_mem_of_mem_zipIdx secondMember))
      (0, 0) relativeTranslate occurrencesDifferent
  have zeroTranslate :
      first.1.map
          (Cell.add (drawing.periodTranslation (0, 0))) =
        first.1 := by
    induction first.1 with
    | nil => rfl
    | cons point points induction =>
        simp only [List.map_cons]
        rw [induction]
        congr 1
        apply Prod.ext <;>
          simp [periodTranslation, Cell.add, Cell.scale]
  rwa [zeroTranslate] at avoids

/-- Absolute-shift form of complete lifted-route separation. -/
theorem liftedRoutesAvoidEachOther_of_isRibbonReady_of_isOrthogonal
    {drawing : PeriodicGridDrawing}
    (ribbonReady : drawing.IsRibbonReady)
    (orthogonal : drawing.IsOrthogonal)
    (lengths :
      ∀ route ∈ drawing.edgeRoutes,
        2 ≤ route.length) :
    drawing.LiftedRoutesAvoidEachOther :=
  (liftedRoutesAvoidEachOther_iff_relative drawing).mpr
    (relativeLiftedRoutesAvoidEachOther_of_isRibbonReady_of_isOrthogonal
      ribbonReady orthogonal lengths)

/-- Translate every stored vertex and route point by one common integral
offset, without changing the periodic lattice. -/
def translateCoordinates (offset : Cell)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := drawing.gridSizePred
  vertexPositions := drawing.vertexPositions.map (Cell.add offset)
  edgeRoutes := drawing.edgeRoutes.map fun route =>
    route.map (Cell.add offset)

@[simp]
theorem translateCoordinates_gridSize
    (offset : Cell) (drawing : PeriodicGridDrawing) :
    (drawing.translateCoordinates offset).gridSize = drawing.gridSize :=
  rfl

@[simp]
theorem translateCoordinates_periodTranslation
    (offset : Cell) (drawing : PeriodicGridDrawing) (translate : Cell) :
    (drawing.translateCoordinates offset).periodTranslation translate =
      drawing.periodTranslation translate :=
  rfl

@[simp]
theorem translateCoordinates_edgeRoutes
    (offset : Cell) (drawing : PeriodicGridDrawing) :
    (drawing.translateCoordinates offset).edgeRoutes =
      drawing.edgeRoutes.map fun route => route.map (Cell.add offset) :=
  rfl

namespace IndexedRoutePoint

/-- Common coordinate translation preserves every syntactic point key. -/
def translate (offset : Cell) (indexed : IndexedRoutePoint) :
    IndexedRoutePoint where
  routeIndex := indexed.routeIndex
  pointIndex := indexed.pointIndex
  routeLength := indexed.routeLength
  point := Cell.add offset indexed.point

end IndexedRoutePoint

/-- Indexed route points of a common coordinate translation retain their
route and point indices. -/
theorem indexedRoutePoints_translateCoordinates
    (offset : Cell) (drawing : PeriodicGridDrawing) :
    (drawing.translateCoordinates offset).indexedRoutePoints =
      drawing.indexedRoutePoints.map
        (IndexedRoutePoint.translate offset) := by
  unfold indexedRoutePoints translateCoordinates
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨route, routeIndex⟩ taggedRouteMember
  simp [List.zipIdx_map, List.map_map,
    IndexedRoutePoint.translate, Function.comp_def]

/-- A common integral translation preserves endpoint-only contacts of all
lifted listed route-point occurrences. -/
theorem routePointsMeetOnlyAtEndpoints_translateCoordinates
    (offset : Cell) (drawing : PeriodicGridDrawing)
    (contacts : drawing.RoutePointsMeetOnlyAtEndpoints) :
    (drawing.translateCoordinates offset)
      |>.RoutePointsMeetOnlyAtEndpoints := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate different equal
  rw [indexedRoutePoints_translateCoordinates] at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨originalFirst, originalFirstMember, rfl⟩
  rcases List.mem_map.mp secondMember with
    ⟨originalSecond, originalSecondMember, rfl⟩
  have originalDifferent :
      RoutePointOccurrenceKey originalFirst firstTranslate ≠
        RoutePointOccurrenceKey originalSecond secondTranslate := by
    simpa [RoutePointOccurrenceKey,
      IndexedRoutePoint.translate] using different
  have originalEqual :
      Cell.add originalFirst.point
          (drawing.periodTranslation firstTranslate) =
        Cell.add originalSecond.point
          (drawing.periodTranslation secondTranslate) := by
    change
      Cell.add (Cell.add offset originalFirst.point)
          (drawing.periodTranslation firstTranslate) =
        Cell.add (Cell.add offset originalSecond.point)
          (drawing.periodTranslation secondTranslate) at equal
    simp only [Cell.add, Prod.mk.injEq] at equal ⊢
    rcases equal with ⟨horizontalEqual, verticalEqual⟩
    constructor <;> omega
  have result := contacts originalFirst originalFirstMember
    originalSecond originalSecondMember firstTranslate secondTranslate
    originalDifferent originalEqual
  simpa [IndexedRoutePoint.translate,
    IndexedRoutePoint.IsEndpoint] using result

/-- Magnify by a positive integral factor, subdivide every route into unit
steps, and apply one common coordinate translation. -/
def affineUnitRefine (factor : Nat) (offset : Cell)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing :=
  ((drawing.scale factor).unitSubdivide).translateCoordinates offset

/-- The affine unit-refinement stage preserves endpoint-only route contacts.
The simplicity premise is exactly what ordered subdivision needs to avoid
creating duplicate syntactic occurrences along a route. -/
theorem routePointsMeetOnlyAtEndpoints_affineUnitRefine
    {factor : Nat} (positive : 0 < factor)
    (offset : Cell) (drawing : PeriodicGridDrawing)
    (ribbonReady : drawing.IsRibbonReady)
    (orthogonal : drawing.IsOrthogonal)
    (lengths :
      ∀ route ∈ drawing.edgeRoutes,
        2 ≤ route.length)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    (drawing.affineUnitRefine factor offset)
      |>.RoutePointsMeetOnlyAtEndpoints := by
  let scaled := drawing.scale factor
  have sourceSeparated : drawing.LiftedRoutesAvoidEachOther :=
    liftedRoutesAvoidEachOther_of_isRibbonReady_of_isOrthogonal
      ribbonReady orthogonal lengths
  have scaledSeparated : scaled.LiftedRoutesAvoidEachOther :=
    liftedRoutesAvoidEachOther_scale positive drawing sourceSeparated
  have scaledOrthogonal : scaled.IsOrthogonal :=
    isOrthogonal_scale positive drawing orthogonal
  have scaledNonempty :
      ∀ route ∈ scaled.edgeRoutes, route ≠ [] := by
    intro route routeMember
    have routeMember' :
        route ∈ drawing.edgeRoutes.map (scalePolyline factor) := by
      simpa [scaled, PeriodicGridDrawing.scale] using routeMember
    rcases List.mem_map.mp routeMember' with
      ⟨source, sourceMember, rfl⟩
    have sourceLength := lengths source sourceMember
    have sourceNonempty : source ≠ [] := by
      intro sourceEmpty
      simp [sourceEmpty] at sourceLength
    simpa [scalePolyline] using sourceNonempty
  have scaledSimple :
      ∀ route ∈ scaled.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route :=
    routesSimple_scale positive drawing simple
  unfold affineUnitRefine
  apply routePointsMeetOnlyAtEndpoints_translateCoordinates
  exact routePointsMeetOnlyAtEndpoints_unitSubdivide scaled
    scaledSeparated scaledOrthogonal scaledNonempty scaledSimple

end PeriodicGridDrawing
end LeanTrominoes
