/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionSimplicity

/-!
# Simplicity of endpoint joins

Two simple routes remain simple after an endpoint join when their continuous
geometry avoids and their advertised boundary is their only common listed
point.  This is the route-level counterpart of the existing compositional
separation lemmas.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace LocalIncidenceDrawing

/-- Joining two simple, continuously separated routes at their only common
listed point preserves geometric simplicity. -/
theorem RouteIsSimple.joinAtEndpoint_of_only_common
    {first second : List Cell}
    {boundary : Cell}
    (firstSimple : RouteIsSimple first)
    (secondSimple : RouteIsSimple second)
    (avoid :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        first second)
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary)
    (onlyCommon :
      ∀ point, point ∈ first → point ∈ second →
        point = boundary) :
    RouteIsSimple (LeanTrominoes.joinAtEndpoint first second) := by
  have firstSecondTailDisjoint :
      List.Disjoint first second.tail := by
    rw [List.disjoint_left]
    intro point firstMember secondTailMember
    have pointEq :=
      onlyCommon point firstMember
        (List.mem_of_mem_tail secondTailMember)
    cases second with
    | nil => simp at secondHead
    | cons secondFirst secondRest =>
        have secondFirstEq : secondFirst = boundary := by
          simpa using secondHead
        subst secondFirst
        have boundaryFresh : boundary ∉ secondRest :=
          (List.nodup_cons.mp secondSimple.1).1
        exact boundaryFresh (by simpa [pointEq] using secondTailMember)
  have joinedNodup :
      (LeanTrominoes.joinAtEndpoint first second).Nodup := by
    unfold LeanTrominoes.joinAtEndpoint
    exact firstSimple.1.append secondSimple.1.tail
      firstSecondTailDisjoint
  have joinedSegments :
      gridPolylineSegments
          (LeanTrominoes.joinAtEndpoint first second) =
        gridPolylineSegments first ++
          gridPolylineSegments second :=
    gridPolylineSegments_joinAtEndpoint firstLast secondHead
  refine ⟨joinedNodup, ?_, ?_⟩
  · intro point pointMember segment segmentMember
    rw [joinedSegments, List.mem_append] at segmentMember
    rcases mem_joinAtEndpoint pointMember with
      firstPointMember | secondPointMember
    · rcases segmentMember with firstSegmentMember | secondSegmentMember
      · exact firstSimple.2.1 point firstPointMember
          segment firstSegmentMember
      · exact avoid.firstPointsAvoid_of_mem
          point firstPointMember segment secondSegmentMember
    · rcases segmentMember with firstSegmentMember | secondSegmentMember
      · exact avoid.secondPointsAvoid_of_mem
          point secondPointMember segment firstSegmentMember
      · exact secondSimple.2.1 point secondPointMember
          segment secondSegmentMember
  · intro firstIndexed firstIndexedMember
      secondIndexed secondIndexedMember indicesDifferent
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff] at firstIndexedMember secondIndexedMember
    let firstIndex :
        Fin (gridPolylineSegments
          (LeanTrominoes.joinAtEndpoint first second)).length :=
      ⟨firstIndexed.2, firstIndexedMember.1⟩
    let secondIndex :
        Fin (gridPolylineSegments
          (LeanTrominoes.joinAtEndpoint first second)).length :=
      ⟨secondIndexed.2, secondIndexedMember.1⟩
    have firstPlain :
        firstIndexed.1 ∈
          gridPolylineSegments
            (LeanTrominoes.joinAtEndpoint first second) := by
      rw [← firstIndexedMember.2]
      exact List.get_mem _ firstIndex
    have secondPlain :
        secondIndexed.1 ∈
          gridPolylineSegments
            (LeanTrominoes.joinAtEndpoint first second) := by
      rw [← secondIndexedMember.2]
      exact List.get_mem _ secondIndex
    have joinedSegmentsNodup :
        (gridPolylineSegments
          (LeanTrominoes.joinAtEndpoint first second)).Nodup :=
      gridPolylineSegments_nodup_of_points_nodup joinedNodup
    have segmentsDifferent :
        firstIndexed.1 ≠ secondIndexed.1 := by
      intro segmentsEqual
      have indexedEqual : firstIndex = secondIndex :=
        (List.nodup_iff_injective_get.mp joinedSegmentsNodup)
          (firstIndexedMember.2.trans
            (segmentsEqual.trans secondIndexedMember.2.symm))
      exact indicesDifferent (congrArg Fin.val indexedEqual)
    rw [joinedSegments, List.mem_append] at firstPlain secondPlain
    rcases firstPlain with firstInFirst | firstInSecond <;>
      rcases secondPlain with secondInFirst | secondInSecond
    · exact firstSimple.segmentInteriorsAvoid_of_mem
        firstInFirst secondInFirst segmentsDifferent
    · exact avoid.segmentsAvoid_of_mem
        firstIndexed.1 firstInFirst
        secondIndexed.1 secondInSecond
    · intro meet
      exact avoid.segmentsAvoid_of_mem
        secondIndexed.1 secondInFirst
        firstIndexed.1 firstInSecond
        ((GridSegment.interiorsMeet_comm _ _).mpr meet)
    · exact secondSimple.segmentInteriorsAvoid_of_mem
        firstInSecond secondInSecond segmentsDifferent

end LocalIncidenceDrawing
end LeanTrominoes
