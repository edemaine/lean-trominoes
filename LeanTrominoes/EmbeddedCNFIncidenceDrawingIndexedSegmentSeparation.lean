/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicGridDrawingScaling

/-!
# Flat indexed-segment separation in finite incidence drawings

The finite planarity certificate is phrased using `Fin` indices.  Periodic
route normalization instead produces membership witnesses in flat
`zipIdx` lists.  This module bridges those interfaces while preserving both
the incidence and within-route segment indices.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Complete route avoidance keeps the relative interior of a selected
first segment away from both endpoints of a selected second segment.  This
statement remains meaningful when the second segment is diagonal. -/
theorem RoutesAvoidEachOther.taggedSegments_endpointsAvoidInterior
    {firstRoute secondRoute : List Cell}
    (avoid : RoutesAvoidEachOther firstRoute secondRoute)
    {firstSegment secondSegment : GridSegment × Nat}
    (firstMember :
      firstSegment ∈ (gridPolylineSegments firstRoute).zipIdx)
    (secondMember :
      secondSegment ∈ (gridPolylineSegments secondRoute).zipIdx)
    {point : Cell}
    (firstContains : firstSegment.1.InteriorContains point) :
    point ≠ secondSegment.1.start ∧
      point ≠ secondSegment.1.finish := by
  have firstIndexLt :
      firstSegment.2 < (gridPolylineSegments firstRoute).length :=
    List.snd_lt_of_mem_zipIdx firstMember
  let firstIndex : Fin (gridPolylineSegments firstRoute).length :=
    ⟨firstSegment.2, firstIndexLt⟩
  have firstAt :
      (gridPolylineSegments firstRoute).get firstIndex =
        firstSegment.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp firstMember)).2
  have endpoints :=
    gridPolylineSegments_endpoints_mem
      (List.fst_mem_of_mem_zipIdx secondMember)
  constructor
  · intro pointEq
    have startMember : point ∈ secondRoute := by
      rw [pointEq]
      exact endpoints.1
    rcases List.mem_iff_get.mp startMember with
      ⟨pointIndex, pointAt⟩
    exact
      (avoid.2.2.1 pointIndex firstIndex)
        (by
          simpa only [pointAt, firstAt] using firstContains)
  · intro pointEq
    have finishMember : point ∈ secondRoute := by
      rw [pointEq]
      exact endpoints.2
    rcases List.mem_iff_get.mp finishMember with
      ⟨pointIndex, pointAt⟩
    exact
      (avoid.2.2.1 pointIndex firstIndex)
        (by
          simpa only [pointAt, firstAt] using firstContains)

/-- Two distinct flat segment occurrences in a finite planar incidence
drawing have disjoint continuous interiors. -/
theorem taggedSegments_interiorsDisjoint
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {firstIncidence secondIncidence :
      EmbeddedCNFIncidence Variable × Nat}
    (firstIncidenceMember :
      firstIncidence ∈ drawing.incidences.zipIdx)
    (secondIncidenceMember :
      secondIncidence ∈ drawing.incidences.zipIdx)
    {firstSegment secondSegment : GridSegment × Nat}
    (firstSegmentMember :
      firstSegment ∈
        (gridPolylineSegments
          (drawing.routeAt firstIncidence.1)).zipIdx)
    (secondSegmentMember :
      secondSegment ∈
        (gridPolylineSegments
          (drawing.routeAt secondIncidence.1)).zipIdx)
    (different :
      firstIncidence.2 ≠ secondIncidence.2 ∨
        firstSegment.2 ≠ secondSegment.2) :
    ¬GridSegment.InteriorsMeet
      firstSegment.1 secondSegment.1 := by
  have firstIncidenceIndexLt :
      firstIncidence.2 < drawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx firstIncidenceMember
  have secondIncidenceIndexLt :
      secondIncidence.2 < drawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx secondIncidenceMember
  let firstIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨firstIncidence.2, firstIncidenceIndexLt⟩
  let secondIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨secondIncidence.2, secondIncidenceIndexLt⟩
  have firstIncidenceAt :
      drawing.incidenceAt firstIncidenceIndex =
        firstIncidence.1 := by
    exact
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstIncidenceMember)).2
  have secondIncidenceAt :
      drawing.incidenceAt secondIncidenceIndex =
        secondIncidence.1 := by
    exact
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondIncidenceMember)).2
  by_cases incidenceIndexEq :
      firstIncidence.2 = secondIncidence.2
  · have finiteIncidenceIndexEq :
        firstIncidenceIndex = secondIncidenceIndex :=
      Fin.ext incidenceIndexEq
    have incidenceEq :
        firstIncidence.1 = secondIncidence.1 := by
      rw [← firstIncidenceAt, ← secondIncidenceAt,
        finiteIncidenceIndexEq]
    have segmentIndexNe :
        firstSegment.2 ≠ secondSegment.2 := by
      rcases different with incidenceIndexNe | segmentIndexNe
      · exact False.elim (incidenceIndexNe incidenceIndexEq)
      · exact segmentIndexNe
    have simple := planar.1 firstIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (drawing.routeAt
          (drawing.incidenceAt firstIncidenceIndex))
      at simple
    rw [firstIncidenceAt] at simple
    apply simple.2.2
      firstSegment firstSegmentMember
      secondSegment
    · simpa only [incidenceEq] using secondSegmentMember
    · exact segmentIndexNe
  · have finiteIncidenceIndexNe :
        firstIncidenceIndex ≠ secondIncidenceIndex := by
      intro equal
      exact incidenceIndexEq (congrArg Fin.val equal)
    have separated :=
      planar.2.1
        firstIncidenceIndex secondIncidenceIndex
        finiteIncidenceIndexNe
    change
      RoutesAvoidEachOther
        (drawing.routeAt
          (drawing.incidenceAt firstIncidenceIndex))
        (drawing.routeAt
          (drawing.incidenceAt secondIncidenceIndex))
      at separated
    rw [firstIncidenceAt, secondIncidenceAt] at separated
    have firstSegmentIndexLt :
        firstSegment.2 <
          (gridPolylineSegments
            (drawing.routeAt firstIncidence.1)).length :=
      List.snd_lt_of_mem_zipIdx firstSegmentMember
    have secondSegmentIndexLt :
        secondSegment.2 <
          (gridPolylineSegments
            (drawing.routeAt secondIncidence.1)).length :=
      List.snd_lt_of_mem_zipIdx secondSegmentMember
    let firstSegmentIndex :
        Fin
          (gridPolylineSegments
            (drawing.routeAt firstIncidence.1)).length :=
      ⟨firstSegment.2, firstSegmentIndexLt⟩
    let secondSegmentIndex :
        Fin
          (gridPolylineSegments
            (drawing.routeAt secondIncidence.1)).length :=
      ⟨secondSegment.2, secondSegmentIndexLt⟩
    have firstSegmentAt :
        (gridPolylineSegments
          (drawing.routeAt firstIncidence.1)).get
            firstSegmentIndex =
          firstSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstSegmentMember)).2
    have secondSegmentAt :
        (gridPolylineSegments
          (drawing.routeAt secondIncidence.1)).get
            secondSegmentIndex =
          secondSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondSegmentMember)).2
    simpa only [firstSegmentAt, secondSegmentAt] using
      separated.1 firstSegmentIndex secondSegmentIndex

/-- For two distinct flat segment occurrences in a finite planar incidence
drawing, the relative interior of the first cannot meet the closed extent
of the second. -/
theorem taggedSegments_avoidsInterior
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {firstIncidence secondIncidence :
      EmbeddedCNFIncidence Variable × Nat}
    (firstIncidenceMember :
      firstIncidence ∈ drawing.incidences.zipIdx)
    (secondIncidenceMember :
      secondIncidence ∈ drawing.incidences.zipIdx)
    {firstSegment secondSegment : GridSegment × Nat}
    (firstSegmentMember :
      firstSegment ∈
        (gridPolylineSegments
          (drawing.routeAt firstIncidence.1)).zipIdx)
    (secondSegmentMember :
      secondSegment ∈
        (gridPolylineSegments
          (drawing.routeAt secondIncidence.1)).zipIdx)
    (different :
      firstIncidence.2 ≠ secondIncidence.2 ∨
        firstSegment.2 ≠ secondSegment.2)
    {point : Cell}
    (firstContains :
      firstSegment.1.InteriorContains point) :
    ¬secondSegment.1.Contains point := by
  have firstIncidenceIndexLt :
      firstIncidence.2 < drawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx firstIncidenceMember
  have secondIncidenceIndexLt :
      secondIncidence.2 < drawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx secondIncidenceMember
  let firstIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨firstIncidence.2, firstIncidenceIndexLt⟩
  let secondIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨secondIncidence.2, secondIncidenceIndexLt⟩
  have firstIncidenceAt :
      drawing.incidenceAt firstIncidenceIndex =
        firstIncidence.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp
        firstIncidenceMember)).2
  have secondIncidenceAt :
      drawing.incidenceAt secondIncidenceIndex =
        secondIncidence.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp
        secondIncidenceMember)).2
  by_cases incidenceIndexEq :
      firstIncidence.2 = secondIncidence.2
  · have finiteIncidenceIndexEq :
        firstIncidenceIndex = secondIncidenceIndex :=
      Fin.ext incidenceIndexEq
    have incidenceEq :
        firstIncidence.1 = secondIncidence.1 := by
      rw [← firstIncidenceAt, ← secondIncidenceAt,
        finiteIncidenceIndexEq]
    have segmentIndexNe :
        firstSegment.2 ≠ secondSegment.2 := by
      rcases different with incidenceIndexNe | segmentIndexNe
      · exact False.elim (incidenceIndexNe incidenceIndexEq)
      · exact segmentIndexNe
    have simple := planar.1 firstIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (drawing.routeAt
          (drawing.incidenceAt firstIncidenceIndex))
      at simple
    rw [firstIncidenceAt] at simple
    intro secondContains
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          secondContains with
      secondInterior | secondEndpoint
    · exact
        (simple.2.2
          firstSegment firstSegmentMember
          secondSegment
          (by simpa only [incidenceEq] using secondSegmentMember)
          segmentIndexNe)
          (GridSegment.interiorsMeet_of_interiorContains
            firstContains secondInterior)
    · have endpointMember :
          point ∈ drawing.routeAt firstIncidence.1 := by
        have endpoints :=
          gridPolylineSegments_endpoints_mem
            (List.fst_mem_of_mem_zipIdx
              (by simpa only [incidenceEq] using
                secondSegmentMember))
        rw [← incidenceEq] at endpoints
        rcases secondEndpoint with atStart | atFinish
        · exact atStart.symm ▸ endpoints.1
        · exact atFinish.symm ▸ endpoints.2
      exact
        (simple.2.1 point endpointMember firstSegment.1
          (List.fst_mem_of_mem_zipIdx firstSegmentMember))
          firstContains
  · have finiteIncidenceIndexNe :
        firstIncidenceIndex ≠ secondIncidenceIndex := by
      intro equal
      exact incidenceIndexEq (congrArg Fin.val equal)
    have separated :=
      planar.2.1
        firstIncidenceIndex secondIncidenceIndex
        finiteIncidenceIndexNe
    change
      RoutesAvoidEachOther
        (drawing.routeAt
          (drawing.incidenceAt firstIncidenceIndex))
        (drawing.routeAt
          (drawing.incidenceAt secondIncidenceIndex))
      at separated
    rw [firstIncidenceAt, secondIncidenceAt] at separated
    have firstSegmentIndexLt :
        firstSegment.2 <
          (gridPolylineSegments
            (drawing.routeAt firstIncidence.1)).length :=
      List.snd_lt_of_mem_zipIdx firstSegmentMember
    have secondSegmentIndexLt :
        secondSegment.2 <
          (gridPolylineSegments
            (drawing.routeAt secondIncidence.1)).length :=
      List.snd_lt_of_mem_zipIdx secondSegmentMember
    let firstSegmentIndex :
        Fin
          (gridPolylineSegments
            (drawing.routeAt firstIncidence.1)).length :=
      ⟨firstSegment.2, firstSegmentIndexLt⟩
    let secondSegmentIndex :
        Fin
          (gridPolylineSegments
            (drawing.routeAt secondIncidence.1)).length :=
      ⟨secondSegment.2, secondSegmentIndexLt⟩
    have firstSegmentAt :
        (gridPolylineSegments
          (drawing.routeAt firstIncidence.1)).get
            firstSegmentIndex =
          firstSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstSegmentMember)).2
    have secondSegmentAt :
        (gridPolylineSegments
          (drawing.routeAt secondIncidence.1)).get
            secondSegmentIndex =
          secondSegment.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondSegmentMember)).2
    intro secondContains
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          secondContains with
      secondInterior | secondEndpoint
    · exact
        (separated.1 firstSegmentIndex secondSegmentIndex)
          (by
            simpa only [firstSegmentAt, secondSegmentAt] using
              GridSegment.interiorsMeet_of_interiorContains
                firstContains secondInterior)
    · have endpointMember :
          point ∈ drawing.routeAt secondIncidence.1 := by
        have endpoints :=
          gridPolylineSegments_endpoints_mem
            (List.fst_mem_of_mem_zipIdx secondSegmentMember)
        rcases secondEndpoint with atStart | atFinish
        · exact atStart.symm ▸ endpoints.1
        · exact atFinish.symm ▸ endpoints.2
      rcases List.mem_iff_getElem.mp endpointMember with
        ⟨pointIndex, pointIndexLt, pointAt⟩
      let finitePointIndex :
          Fin (drawing.routeAt secondIncidence.1).length :=
        ⟨pointIndex, pointIndexLt⟩
      have finitePointAt :
          (drawing.routeAt secondIncidence.1).get
              finitePointIndex =
            point := by
        change
          (drawing.routeAt secondIncidence.1)[pointIndex] =
            point
        exact pointAt
      exact
        (separated.2.2.1 finitePointIndex firstSegmentIndex)
          (by
            simpa only [finitePointAt,
              firstSegmentAt] using firstContains)

/-- For two distinct flat segment occurrences in a finite planar incidence
drawing, the relative interior of the first avoids both endpoints of the
second, including endpoints of diagonal segments. -/
theorem taggedSegments_endpointsAvoidInterior
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (planar : drawing.IsPlanar)
    {firstIncidence secondIncidence :
      EmbeddedCNFIncidence Variable × Nat}
    (firstIncidenceMember :
      firstIncidence ∈ drawing.incidences.zipIdx)
    (secondIncidenceMember :
      secondIncidence ∈ drawing.incidences.zipIdx)
    {firstSegment secondSegment : GridSegment × Nat}
    (firstSegmentMember :
      firstSegment ∈
        (gridPolylineSegments
          (drawing.routeAt firstIncidence.1)).zipIdx)
    (secondSegmentMember :
      secondSegment ∈
        (gridPolylineSegments
          (drawing.routeAt secondIncidence.1)).zipIdx)
    (different :
      firstIncidence.2 ≠ secondIncidence.2 ∨
        firstSegment.2 ≠ secondSegment.2)
    {point : Cell}
    (firstContains :
      firstSegment.1.InteriorContains point) :
    point ≠ secondSegment.1.start ∧
      point ≠ secondSegment.1.finish := by
  have firstIncidenceIndexLt :
      firstIncidence.2 < drawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx firstIncidenceMember
  have secondIncidenceIndexLt :
      secondIncidence.2 < drawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx secondIncidenceMember
  let firstIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨firstIncidence.2, firstIncidenceIndexLt⟩
  let secondIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨secondIncidence.2, secondIncidenceIndexLt⟩
  have firstIncidenceAt :
      drawing.incidenceAt firstIncidenceIndex =
        firstIncidence.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp
        firstIncidenceMember)).2
  have secondIncidenceAt :
      drawing.incidenceAt secondIncidenceIndex =
        secondIncidence.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp
        secondIncidenceMember)).2
  by_cases incidenceIndexEq :
      firstIncidence.2 = secondIncidence.2
  · have finiteIncidenceIndexEq :
        firstIncidenceIndex = secondIncidenceIndex :=
      Fin.ext incidenceIndexEq
    have incidenceEq :
        firstIncidence.1 = secondIncidence.1 := by
      rw [← firstIncidenceAt, ← secondIncidenceAt,
        finiteIncidenceIndexEq]
    have segmentIndexNe :
        firstSegment.2 ≠ secondSegment.2 := by
      rcases different with incidenceIndexNe | segmentIndexNe
      · exact False.elim (incidenceIndexNe incidenceIndexEq)
      · exact segmentIndexNe
    have simple := planar.1 firstIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (drawing.routeAt
          (drawing.incidenceAt firstIncidenceIndex))
      at simple
    rw [firstIncidenceAt] at simple
    have secondSegmentMember' :
        secondSegment.1 ∈
          gridPolylineSegments
            (drawing.routeAt firstIncidence.1) :=
      List.fst_mem_of_mem_zipIdx
        (by simpa only [incidenceEq] using secondSegmentMember)
    have endpoints :=
      gridPolylineSegments_endpoints_mem secondSegmentMember'
    have firstSegmentMember' :
        firstSegment.1 ∈
          gridPolylineSegments
            (drawing.routeAt firstIncidence.1) :=
      List.fst_mem_of_mem_zipIdx firstSegmentMember
    constructor
    · intro pointEq
      subst point
      exact
        (simple.2.1 secondSegment.1.start endpoints.1
          firstSegment.1 firstSegmentMember') firstContains
    · intro pointEq
      subst point
      exact
        (simple.2.1 secondSegment.1.finish endpoints.2
          firstSegment.1 firstSegmentMember') firstContains
  · have finiteIncidenceIndexNe :
        firstIncidenceIndex ≠ secondIncidenceIndex := by
      intro equal
      exact incidenceIndexEq (congrArg Fin.val equal)
    have separated :=
      planar.2.1
        firstIncidenceIndex secondIncidenceIndex
        finiteIncidenceIndexNe
    change
      RoutesAvoidEachOther
        (drawing.routeAt
          (drawing.incidenceAt firstIncidenceIndex))
        (drawing.routeAt
          (drawing.incidenceAt secondIncidenceIndex))
      at separated
    rw [firstIncidenceAt, secondIncidenceAt] at separated
    exact
      separated.taggedSegments_endpointsAvoidInterior
        firstSegmentMember secondSegmentMember firstContains

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
