/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicThreeDMContractionContinuousPlanarity

/-!
# Route separation under reversal

Reversing a polyline changes only its traversal order.  This file records
that the finite continuous-separation predicate used by embedded CNF
incidence drawings is invariant under reversing both routes.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Reversing a route swaps its two advertised endpoints and therefore
preserves the endpoint predicate. -/
@[simp]
theorem routePointIsEndpoint_reverse_iff
    (route : List Cell) (point : Cell) :
    RoutePointIsEndpoint route.reverse point ↔
      RoutePointIsEndpoint route point := by
  simp [RoutePointIsEndpoint, or_comm]

/-- Reversing both traversal orders preserves complete continuous route
separation. -/
theorem routesAvoidEachOther_reverse
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second) :
    RoutesAvoidEachOther first.reverse second.reverse := by
  unfold RoutesAvoidEachOther at avoid ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex
    let firstSegment :=
      (gridPolylineSegments first.reverse).get firstIndex
    let secondSegment :=
      (gridPolylineSegments second.reverse).get secondIndex
    have firstMember :
        firstSegment ∈
          gridPolylineSegments first.reverse :=
      List.get_mem _ _
    have secondMember :
        secondSegment ∈
          gridPolylineSegments second.reverse :=
      List.get_mem _ _
    have firstMapped :
        firstSegment ∈
          (gridPolylineSegments first).reverse.map
            GridSegment.reverse := by
      rw [← gridPolylineSegments_reverse]
      exact firstMember
    have secondMapped :
        secondSegment ∈
          (gridPolylineSegments second).reverse.map
            GridSegment.reverse := by
      rw [← gridPolylineSegments_reverse]
      exact secondMember
    rcases List.mem_map.mp firstMapped with
      ⟨firstOriginal, firstOriginalMember, firstEqual⟩
    rcases List.mem_map.mp secondMapped with
      ⟨secondOriginal, secondOriginalMember, secondEqual⟩
    have firstOriginalMember' :
        firstOriginal ∈ gridPolylineSegments first := by
      simpa using firstOriginalMember
    have secondOriginalMember' :
        secondOriginal ∈ gridPolylineSegments second := by
      simpa using secondOriginalMember
    rcases List.mem_iff_get.mp firstOriginalMember' with
      ⟨firstOriginalIndex, firstOriginalEqual⟩
    rcases List.mem_iff_get.mp secondOriginalMember' with
      ⟨secondOriginalIndex, secondOriginalEqual⟩
    intro meet
    apply avoid.1 firstOriginalIndex secondOriginalIndex
    rw [firstOriginalEqual, secondOriginalEqual]
    have meet' : GridSegment.InteriorsMeet firstSegment secondSegment := by
      simpa [firstSegment, secondSegment] using meet
    rw [← firstEqual, ← secondEqual] at meet'
    simpa using meet'
  · intro firstPointIndex secondSegmentIndex
    have firstPointMember :
        first.reverse.get firstPointIndex ∈ first :=
      List.mem_reverse.mp (List.get_mem _ _)
    let secondSegment :=
      (gridPolylineSegments second.reverse).get secondSegmentIndex
    have secondSegmentMember :
        secondSegment ∈
          gridPolylineSegments second.reverse :=
      List.get_mem _ _
    have secondMapped :
        secondSegment ∈
          (gridPolylineSegments second).reverse.map
            GridSegment.reverse := by
      rw [← gridPolylineSegments_reverse]
      exact secondSegmentMember
    rcases List.mem_map.mp secondMapped with
      ⟨secondOriginal, secondOriginalMember, secondEqual⟩
    have secondOriginalMember' :
        secondOriginal ∈ gridPolylineSegments second := by
      simpa using secondOriginalMember
    rcases List.mem_iff_get.mp firstPointMember with
      ⟨firstOriginalIndex, firstPointEqual⟩
    rcases List.mem_iff_get.mp secondOriginalMember' with
      ⟨secondOriginalIndex, secondOriginalEqual⟩
    intro contains
    apply avoid.2.1 firstOriginalIndex secondOriginalIndex
    rw [secondOriginalEqual, firstPointEqual]
    have contains' :
        secondSegment.InteriorContains
          (first.reverse.get firstPointIndex) := by
      simpa [secondSegment] using contains
    rw [← secondEqual] at contains'
    simpa using contains'
  · intro secondPointIndex firstSegmentIndex
    have secondPointMember :
        second.reverse.get secondPointIndex ∈ second :=
      List.mem_reverse.mp (List.get_mem _ _)
    let firstSegment :=
      (gridPolylineSegments first.reverse).get firstSegmentIndex
    have firstSegmentMember :
        firstSegment ∈
          gridPolylineSegments first.reverse :=
      List.get_mem _ _
    have firstMapped :
        firstSegment ∈
          (gridPolylineSegments first).reverse.map
            GridSegment.reverse := by
      rw [← gridPolylineSegments_reverse]
      exact firstSegmentMember
    rcases List.mem_map.mp firstMapped with
      ⟨firstOriginal, firstOriginalMember, firstEqual⟩
    have firstOriginalMember' :
        firstOriginal ∈ gridPolylineSegments first := by
      simpa using firstOriginalMember
    rcases List.mem_iff_get.mp secondPointMember with
      ⟨secondOriginalIndex, secondPointEqual⟩
    rcases List.mem_iff_get.mp firstOriginalMember' with
      ⟨firstOriginalIndex, firstOriginalEqual⟩
    intro contains
    apply avoid.2.2.1 secondOriginalIndex firstOriginalIndex
    rw [firstOriginalEqual, secondPointEqual]
    have contains' :
        firstSegment.InteriorContains
          (second.reverse.get secondPointIndex) := by
      simpa [firstSegment] using contains
    rw [← firstEqual] at contains'
    simpa using contains'
  · intro firstPointIndex secondPointIndex equal
    have firstPointMember :
        first.reverse.get firstPointIndex ∈ first :=
      List.mem_reverse.mp (List.get_mem _ _)
    have secondPointMember :
        second.reverse.get secondPointIndex ∈ second :=
      List.mem_reverse.mp (List.get_mem _ _)
    rcases List.mem_iff_get.mp firstPointMember with
      ⟨firstOriginalIndex, firstPointEqual⟩
    rcases List.mem_iff_get.mp secondPointMember with
      ⟨secondOriginalIndex, secondPointEqual⟩
    have originalEqual :
        first.get firstOriginalIndex =
          second.get secondOriginalIndex := by
      calc
        first.get firstOriginalIndex =
            first.reverse.get firstPointIndex :=
          firstPointEqual
        _ = second.reverse.get secondPointIndex := equal
        _ = second.get secondOriginalIndex :=
          secondPointEqual.symm
    have endpoints :=
      avoid.2.2.2 firstOriginalIndex secondOriginalIndex originalEqual
    constructor
    · rw [← firstPointEqual]
      exact (routePointIsEndpoint_reverse_iff _ _).2 endpoints.1
    · rw [← secondPointEqual]
      exact (routePointIsEndpoint_reverse_iff _ _).2 endpoints.2

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
