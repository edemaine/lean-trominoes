import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity

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

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
