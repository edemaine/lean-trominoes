/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionSimplicity
import LeanTrominoes.ListZipIdxFstMembership

/-! # Separating a simple route from its final segment

Deleting the last two points of a simple route leaves a leading prefix that
is strictly separated from the discarded final segment.  This is the precise
contact-free form needed when a replacement route is allowed to retain the
old penultimate point as its joining gate.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The leading prefix of a simple route strictly avoids its final segment.
The penultimate point is removed from the prefix, so even the segment's
source endpoint is excluded. -/
theorem routeIsSimple_dropLast_dropLast_strictlyAvoids_finalSegment
    {route : List Cell} {entrance finalPoint : Cell}
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (entranceLookup : route.dropLast.getLast? = some entrance)
    (finalLookup : route.getLast? = some finalPoint) :
    RoutesStrictlyAvoidEachOther
      route.dropLast.dropLast [entrance, finalPoint] := by
  have droppedSimple :
      LocalIncidenceDrawing.RouteIsSimple route.dropLast := by
    have reversed := simple.reverse.tail.reverse
    rw [← List.dropLast_reverse (l := route.reverse)] at reversed
    simpa using reversed
  have entranceClear :=
    routeIsSimple_dropLast_avoids_final_point
      droppedSimple entranceLookup
  have finalClear :=
    routeIsSimple_dropLast_avoids_final_point
      simple finalLookup
  have finalNotInLeading :
      ∀ point ∈ route.dropLast.dropLast,
        point ≠ finalPoint := by
    intro point pointMember
    exact finalClear.1 point
      (List.mem_of_mem_dropLast pointMember)
  have entranceMember : entrance ∈ route := by
    exact List.mem_of_mem_dropLast
      (List.mem_of_mem_getLast? entranceLookup)
  have finalMember : finalPoint ∈ route :=
    List.mem_of_mem_getLast? finalLookup
  have terminalSegmentMember :
      (⟨entrance, finalPoint⟩ : GridSegment) ∈
        gridPolylineSegments route := by
    have droppedNonempty : route.dropLast ≠ [] := by
      intro droppedEmpty
      rw [droppedEmpty] at entranceLookup
      simp at entranceLookup
    have routeEq : route.dropLast ++ [finalPoint] = route :=
      List.dropLast_append_getLast? finalPoint finalLookup
    have entranceLastD :
        route.dropLast.getLastD (0, 0) = entrance := by
      rw [List.getLastD_eq_getLast?, entranceLookup]
      rfl
    rw [← routeEq,
      gridPolylineSegments_append_singleton_of_ne_nil
        route.dropLast (0, 0) finalPoint droppedNonempty,
      List.mem_append]
    right
    simp only [List.mem_singleton]
    rw [entranceLastD]
  unfold RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    have firstOriginal : firstSegment ∈ gridPolylineSegments route :=
      gridPolylineSegments_dropLast_subset route
        (gridPolylineSegments_dropLast_subset route.dropLast firstMember)
    have secondEq :
        secondSegment = (⟨entrance, finalPoint⟩ : GridSegment) := by
      simpa [gridPolylineSegments] using secondMember
    subst secondSegment
    rcases exists_mem_zipIdx_fst
        (gridPolylineSegments route) 0 firstOriginal with
      ⟨firstIndex, firstTaggedMember⟩
    rcases exists_mem_zipIdx_fst
        (gridPolylineSegments route) 0 terminalSegmentMember with
      ⟨terminalIndex, terminalTaggedMember⟩
    have indicesNe : firstIndex ≠ terminalIndex := by
      intro indicesEq
      have firstLookup :=
        (List.mem_zipIdx_iff_getElem?).mp firstTaggedMember
      have terminalLookup :=
        (List.mem_zipIdx_iff_getElem?).mp terminalTaggedMember
      have segmentEq :
          firstSegment = (⟨entrance, finalPoint⟩ : GridSegment) := by
        rw [indicesEq, terminalLookup] at firstLookup
        exact Option.some.inj firstLookup.symm
      have endpoints := gridPolylineSegments_endpoints_mem firstMember
      exact finalNotInLeading firstSegment.finish endpoints.2
        (by simpa [segmentEq])
    exact simple.2.2
      (firstSegment, firstIndex) firstTaggedMember
      ((⟨entrance, finalPoint⟩ : GridSegment), terminalIndex)
      terminalTaggedMember indicesNe
  · intro point pointMember segment segmentMember
    have pointOriginal : point ∈ route :=
      List.mem_of_mem_dropLast
        (List.mem_of_mem_dropLast pointMember)
    have segmentEq :
        segment = (⟨entrance, finalPoint⟩ : GridSegment) := by
      simpa [gridPolylineSegments] using segmentMember
    subst segment
    exact simple.2.1 point pointOriginal
      (⟨entrance, finalPoint⟩ : GridSegment)
      terminalSegmentMember
  · intro point pointMember segment segmentMember
    have segmentOriginal : segment ∈ gridPolylineSegments route :=
      gridPolylineSegments_dropLast_subset route
        (gridPolylineSegments_dropLast_subset route.dropLast segmentMember)
    simp at pointMember
    rcases pointMember with pointEq | pointEq
    · subst point
      exact simple.2.1 entrance entranceMember segment segmentOriginal
    · subst point
      exact simple.2.1 finalPoint finalMember segment segmentOriginal
  · intro firstPoint firstMember secondPoint secondMember
    simp at secondMember
    rcases secondMember with pointEq | pointEq
    · subst secondPoint
      exact entranceClear.1 firstPoint firstMember
    · subst secondPoint
      exact finalNotInLeading firstPoint firstMember

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
end LeanTrominoes
