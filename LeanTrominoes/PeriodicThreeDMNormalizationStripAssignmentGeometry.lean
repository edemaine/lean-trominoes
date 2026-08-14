/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentGeometry
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterization

/-!
# Collision freedom for normalized 3DM strip assignments

The rectangular strip raster remembers the geometric vertical coordinate
instead of reducing it modulo the period.  Equality of strip locations
therefore implies equality of the corresponding square-torus locations.
The existing geometric occurrence-separation certificate consequently also
proves that the strip assignment list has no duplicate locations.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Forgetting the cell types emitted by the strip route rasterizer leaves
exactly the strip-rasterized internal route points. -/
theorem stripRouteInteriorAssignmentLocations
    (period : Nat) (color : WireColor) :
    ∀ route,
      (stripRouteInteriorAssignments period color route).map Prod.fst =
        (routeInteriorPoints route).map (stripRasterLocation period)
  | [] => by simp [stripRouteInteriorAssignments, routeInteriorPoints]
  | [_] => by simp [stripRouteInteriorAssignments, routeInteriorPoints]
  | [_, _] => by simp [stripRouteInteriorAssignments, routeInteriorPoints]
  | before :: current :: after :: rest => by
      simp only [stripRouteInteriorAssignments, List.map_cons,
        routeInteriorPoints, List.tail_cons, List.dropLast_cons_cons]
      rw [stripRouteInteriorAssignmentLocations period color
        (current :: after :: rest)]
      rfl

/-- Locations used as keys by the rectangular strip assignment list. -/
def PlanarPresentation.finalStripAssignmentLocations
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List Cell :=
  presentation.finalStripCellAssignments.map Prod.fst

/-- No two normalized vertex or route-interior assignments occupy the same
location in the rectangular strip. -/
def PlanarPresentation.FinalStripAssignmentsCollisionFree
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : Prop :=
  presentation.finalStripAssignmentLocations.Nodup

/-- Strip assignment locations are the final geometric assignment points
mapped into the rectangular raster. -/
theorem PlanarPresentation.finalStripAssignmentLocations_eq_map
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalStripAssignmentLocations =
      presentation.finalGeometricAssignmentPoints.map
        (stripRasterLocation presentation.finalNormalizationPeriod) := by
  unfold PlanarPresentation.finalStripAssignmentLocations
    PlanarPresentation.finalStripCellAssignments
    PlanarPresentation.finalStripVertexAssignments
    PlanarPresentation.finalStripRouteAssignments
    PlanarPresentation.finalGeometricAssignmentPoints
  rw [presentation.finalNormalizedVertexPositions_eq_map]
  simp only [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro edge edgeMember
  exact stripRouteInteriorAssignmentLocations _ _ _

/-- Equal strip locations are also equal after reduction to the square
torus. -/
theorem rasterLocation_eq_of_stripRasterLocation_eq
    {period : Nat} {first second : Cell}
    (equal : stripRasterLocation period first =
      stripRasterLocation period second) :
    rasterLocation period first = rasterLocation period second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [stripRasterLocation, Prod.mk.injEq] at equal
  simp only [rasterLocation, Prod.mk.injEq]
  constructor
  · exact equal.1
  · have verticalEqual : firstY = secondY := by omega
    rw [verticalEqual]

/-- Duplicate freedom after square-torus rasterization implies duplicate
freedom after the more informative strip rasterization. -/
theorem stripRasterLocations_nodup_of_rasterLocations_nodup
    {period : Nat} {points : List Cell}
    (nodup : (points.map (rasterLocation period)).Nodup) :
    (points.map (stripRasterLocation period)).Nodup := by
  have pointsNodup : points.Nodup := nodup.of_map
  have rasterInjective :=
    (List.nodup_map_iff_inj_on pointsNodup).mp nodup
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    exact rasterInjective first firstMember second secondMember
      (rasterLocation_eq_of_stripRasterLocation_eq equal)
  · exact pointsNodup

/-- The existing square-torus assignment collision certificate also
certifies the rectangular strip assignment list. -/
theorem PlanarPresentation.finalStripAssignmentsCollisionFree_of_finalAssignmentsCollisionFree
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (collisionFree : presentation.FinalAssignmentsCollisionFree) :
    presentation.FinalStripAssignmentsCollisionFree := by
  unfold PlanarPresentation.FinalStripAssignmentsCollisionFree
  rw [presentation.finalStripAssignmentLocations_eq_map]
  unfold PlanarPresentation.FinalAssignmentsCollisionFree at collisionFree
  rw [presentation.finalAssignmentLocations_eq_map] at collisionFree
  exact stripRasterLocations_nodup_of_rasterLocations_nodup collisionFree

end PeriodicThreeDM

namespace PeriodicGridDrawing

open PeriodicThreeDM

/-- Occurrence separation for the square torus also makes the more
informative rectangular strip locations duplicate-free. -/
theorem assignmentPointStripRasterLocations_nodup
    {drawing : PeriodicGridDrawing}
    (separated : drawing.AssignmentPointOccurrencesSeparated) :
    ((drawing.indexedAssignmentPoints.map Prod.snd).map
      (stripRasterLocation drawing.gridSize)).Nodup := by
  have keysNodup := drawing.indexedAssignmentPointKeys_nodup
  have occurrencesNodup : drawing.indexedAssignmentPoints.Nodup :=
    keysNodup.of_map Prod.fst
  have keyInjective :=
    (List.nodup_map_iff_inj_on occurrencesNodup).mp keysNodup
  rw [List.map_map]
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    by_contra different
    have keysDifferent : first.1 ≠ second.1 := by
      intro keysEqual
      exact different
        (keyInjective first firstMember second secondMember keysEqual)
    exact separated first firstMember second secondMember keysDifferent
      (rasterLocation_eq_of_stripRasterLocation_eq equal)
  · exact occurrencesNodup

end PeriodicGridDrawing

namespace PeriodicThreeDM

/-- The final normalized drawing's occurrence-separation certificate proves
collision freedom for its rectangular strip assignments. -/
theorem ContinuousPlanarPresentation.finalStripAssignmentsCollisionFree_of_occurrencesSeparated
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (separated : presentation.finalNormalizedGridDrawing
      |>.AssignmentPointOccurrencesSeparated) :
    presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree := by
  unfold PlanarPresentation.FinalStripAssignmentsCollisionFree
  rw [presentation.toPlanarPresentation.finalStripAssignmentLocations_eq_map]
  have pointList :=
    presentation.toPlanarPresentation.finalNormalizedGridDrawing
      |>.indexedAssignmentPoints_map_point
  have pointListFinal :
      (presentation.toPlanarPresentation.finalNormalizedGridDrawing
          |>.indexedAssignmentPoints.map Prod.snd) =
        presentation.toPlanarPresentation.finalGeometricAssignmentPoints := by
    calc
      _ =
          presentation.toPlanarPresentation.finalNormalizedGridDrawing.vertexPositions ++
            presentation.toPlanarPresentation.finalNormalizedGridDrawing.edgeRoutes.flatMap
              fun route => route.tail.dropLast := pointList
      _ =
          presentation.toPlanarPresentation.finalNormalizedVertexPositions ++
            (problem.contractedEdges.map
              presentation.toPlanarPresentation.finalNormalizationRoute).flatMap
                fun route => route.tail.dropLast := by
        rw [presentation.toPlanarPresentation.finalNormalizedGridDrawing_edgeRoutes_eq_map]
        rfl
      _ = presentation.toPlanarPresentation.finalGeometricAssignmentPoints := by
        unfold PlanarPresentation.finalGeometricAssignmentPoints
        simp only [List.flatMap_map, routeInteriorPoints]
  rw [← pointListFinal]
  simpa only [presentation.toPlanarPresentation.finalNormalizedGridDrawing_gridSize]
    using PeriodicGridDrawing.assignmentPointStripRasterLocations_nodup separated

/-- Endpoint-only route contacts imply collision freedom for the final
rectangular strip assignment list. -/
theorem ContinuousPlanarPresentation.finalStripAssignmentsCollisionFree_of_endpointContacts
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (endpointContacts :
      presentation.toPlanarPresentation.finalNormalizedGridDrawing
        |>.RoutePointsMeetOnlyAtEndpoints) :
    presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree := by
  apply presentation.finalStripAssignmentsCollisionFree_of_occurrencesSeparated
  exact
    PeriodicGridDrawing.assignmentPointOccurrencesSeparated_of_incident_endpointContacts
      problem.contractedGraph
      presentation.toPlanarPresentation.finalNormalizedGridDrawing
      presentation.toPlanarPresentation.finalNormalizedGridDrawing_isCompatible
      (contractedGraph_everyVertexIncident problem
        presentation.problemWellFormed degree)
      endpointContacts

end PeriodicThreeDM
end LeanTrominoes
