import LeanTrominoes.EmbeddedCNFIncidenceDrawingIndexedRoutePointSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATFinitePlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointOccurrences

/-!
# Route-point contacts at a common retained-drawing translate

When two final route-point occurrences undo to the same translate of the
finite retained drawing, finite route simplicity and endpoint-only contact
settle the interaction completely.  Equal points on one physical route
would violate duplicate-freeness unless the final occurrences were equal;
equal points on different physical routes must be outer endpoints of both.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Distinct final point occurrences represented at the same physical
finite-drawing shift can coincide only as outer endpoints of both routes. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_samePhysicalShift_routePointsAreEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (different :
      PeriodicGridDrawing.RoutePointOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.RoutePointOccurrenceKey
          secondIndexed secondShift)
    (samePhysicalShift :
      first.segmentWitness.physicalShift =
        second.segmentWitness.physicalShift)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  let finiteDrawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have physicalKeyNe :
      first.physicalKey ≠ second.physicalKey := by
    intro physicalKeyEq
    exact different
      ((FinalGaugedRoutePointOccurrenceWitness.physicalKey_eq_iff_routePointOccurrenceKey_eq
        first second).mp physicalKeyEq)
  have liftedPhysicalPointEq :
      Cell.add first.physicalPoint
          (placement.translation first.segmentWitness.physicalShift) =
        Cell.add second.physicalPoint
          (placement.translation second.segmentWitness.physicalShift) :=
    first.pointEq.symm.trans (equal.trans second.pointEq)
  have physicalPointEq :
      first.physicalPoint = second.physicalPoint := by
    apply
      Cell.add_left_injective
        (placement.translation second.segmentWitness.physicalShift)
    simpa [samePhysicalShift, Cell.add, add_comm] using
      liftedPhysicalPointEq
  have finiteDifferent :
      first.segmentWitness.physicalIncidenceIndex ≠
          second.segmentWitness.physicalIncidenceIndex ∨
        firstIndexed.pointIndex ≠ secondIndexed.pointIndex := by
    by_cases incidenceIndexNe :
        first.segmentWitness.physicalIncidenceIndex ≠
          second.segmentWitness.physicalIncidenceIndex
    · exact Or.inl incidenceIndexNe
    · right
      intro pointIndexEq
      apply physicalKeyNe
      apply Prod.ext
      · exact not_ne_iff.mp incidenceIndexNe
      · apply Prod.ext
        · exact pointIndexEq
        · exact samePhysicalShift
  have finitePlanar :
      finiteDrawing.IsPlanar :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
      formula wellFormed degree isLocal clausesNonempty
  by_cases incidenceIndexEq :
      first.segmentWitness.physicalIncidenceIndex =
        second.segmentWitness.physicalIncidenceIndex
  · have pointIndexNe :
        firstIndexed.pointIndex ≠ secondIndexed.pointIndex := by
      rcases finiteDifferent with incidenceIndexNe | pointIndexNe
      · exact False.elim (incidenceIndexNe incidenceIndexEq)
      · exact pointIndexNe
    have firstIncidenceLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        first.segmentWitness.physicalIncidenceMember
    have secondIncidenceLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        second.segmentWitness.physicalIncidenceMember
    have physicalIncidenceEq :
        metadataPhysicalIncidence
            first.segmentWitness.routeWitness.metadata
            first.segmentWitness.routeWitness.metadataIndex
            first.segmentWitness.routeWitness.literal
            first.segmentWitness.taggedLiteral.2 =
          metadataPhysicalIncidence
            second.segmentWitness.routeWitness.metadata
            second.segmentWitness.routeWitness.metadataIndex
            second.segmentWitness.routeWitness.literal
            second.segmentWitness.taggedLiteral.2 := by
      rw [incidenceIndexEq] at firstIncidenceLookup
      exact Option.some.inj
        (firstIncidenceLookup.symm.trans secondIncidenceLookup)
    have incidenceIndexLt :
        first.segmentWitness.physicalIncidenceIndex <
          finiteDrawing.incidences.length :=
      List.snd_lt_of_mem_zipIdx
        first.segmentWitness.physicalIncidenceMember
    let incidenceIndex : Fin finiteDrawing.incidences.length :=
      ⟨first.segmentWitness.physicalIncidenceIndex,
        incidenceIndexLt⟩
    have incidenceAt :
        finiteDrawing.incidenceAt incidenceIndex =
          metadataPhysicalIncidence
            first.segmentWitness.routeWitness.metadata
            first.segmentWitness.routeWitness.metadataIndex
            first.segmentWitness.routeWitness.literal
            first.segmentWitness.taggedLiteral.2 := by
      exact
        (List.getElem?_eq_some_iff.mp firstIncidenceLookup).2
    have simple := finitePlanar.1 incidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt incidenceIndex))
      at simple
    rw [incidenceAt] at simple
    have firstPointLookup :=
      (List.mem_zipIdx_iff_getElem?).mp first.physicalPointMember
    have secondPointLookup :=
      (List.mem_zipIdx_iff_getElem?).mp second.physicalPointMember
    have firstPointLookup' :
        (finiteDrawing.routeAt
          (metadataPhysicalIncidence
            first.segmentWitness.routeWitness.metadata
            first.segmentWitness.routeWitness.metadataIndex
            first.segmentWitness.routeWitness.literal
            first.segmentWitness.taggedLiteral.2))[
              firstIndexed.pointIndex]? =
          some second.physicalPoint :=
      firstPointLookup.trans (congrArg some physicalPointEq)
    have secondPointLookup' :
        (finiteDrawing.routeAt
          (metadataPhysicalIncidence
            first.segmentWitness.routeWitness.metadata
            first.segmentWitness.routeWitness.metadataIndex
            first.segmentWitness.routeWitness.literal
            first.segmentWitness.taggedLiteral.2))[
              secondIndexed.pointIndex]? =
          some second.physicalPoint := by
      simpa only [physicalIncidenceEq] using secondPointLookup
    exact False.elim
      (pointIndexNe
        (List.Nodup.index_eq_of_getElem?_eq_some
          simple.1 firstPointLookup' secondPointLookup'))
  · have firstIncidenceIndexLt :
        first.segmentWitness.physicalIncidenceIndex <
          finiteDrawing.incidences.length :=
      List.snd_lt_of_mem_zipIdx
        first.segmentWitness.physicalIncidenceMember
    have secondIncidenceIndexLt :
        second.segmentWitness.physicalIncidenceIndex <
          finiteDrawing.incidences.length :=
      List.snd_lt_of_mem_zipIdx
        second.segmentWitness.physicalIncidenceMember
    let firstIncidenceIndex : Fin finiteDrawing.incidences.length :=
      ⟨first.segmentWitness.physicalIncidenceIndex,
        firstIncidenceIndexLt⟩
    let secondIncidenceIndex : Fin finiteDrawing.incidences.length :=
      ⟨second.segmentWitness.physicalIncidenceIndex,
        secondIncidenceIndexLt⟩
    have firstIncidenceAt :
        finiteDrawing.incidenceAt firstIncidenceIndex =
          metadataPhysicalIncidence
            first.segmentWitness.routeWitness.metadata
            first.segmentWitness.routeWitness.metadataIndex
            first.segmentWitness.routeWitness.literal
            first.segmentWitness.taggedLiteral.2 := by
      exact
        (List.getElem?_eq_some_iff.mp
          ((List.mem_zipIdx_iff_getElem?).mp
            first.segmentWitness.physicalIncidenceMember)).2
    have secondIncidenceAt :
        finiteDrawing.incidenceAt secondIncidenceIndex =
          metadataPhysicalIncidence
            second.segmentWitness.routeWitness.metadata
            second.segmentWitness.routeWitness.metadataIndex
            second.segmentWitness.routeWitness.literal
            second.segmentWitness.taggedLiteral.2 := by
      exact
        (List.getElem?_eq_some_iff.mp
          ((List.mem_zipIdx_iff_getElem?).mp
            second.segmentWitness.physicalIncidenceMember)).2
    have finiteIncidenceIndexNe :
        firstIncidenceIndex ≠ secondIncidenceIndex := by
      intro indexEq
      exact incidenceIndexEq (congrArg Fin.val indexEq)
    have separated :=
      finitePlanar.2.1
        firstIncidenceIndex secondIncidenceIndex
        finiteIncidenceIndexNe
    change
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt firstIncidenceIndex))
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt secondIncidenceIndex))
      at separated
    rw [firstIncidenceAt, secondIncidenceAt] at separated
    have firstPointIndexLt :
        firstIndexed.pointIndex <
          (finiteDrawing.routeAt
            (metadataPhysicalIncidence
              first.segmentWitness.routeWitness.metadata
              first.segmentWitness.routeWitness.metadataIndex
              first.segmentWitness.routeWitness.literal
              first.segmentWitness.taggedLiteral.2)).length :=
      List.snd_lt_of_mem_zipIdx first.physicalPointMember
    have secondPointIndexLt :
        secondIndexed.pointIndex <
          (finiteDrawing.routeAt
            (metadataPhysicalIncidence
              second.segmentWitness.routeWitness.metadata
              second.segmentWitness.routeWitness.metadataIndex
              second.segmentWitness.routeWitness.literal
              second.segmentWitness.taggedLiteral.2)).length :=
      List.snd_lt_of_mem_zipIdx second.physicalPointMember
    let firstPointIndex :
        Fin
          (finiteDrawing.routeAt
            (metadataPhysicalIncidence
              first.segmentWitness.routeWitness.metadata
              first.segmentWitness.routeWitness.metadataIndex
              first.segmentWitness.routeWitness.literal
              first.segmentWitness.taggedLiteral.2)).length :=
      ⟨firstIndexed.pointIndex, firstPointIndexLt⟩
    let secondPointIndex :
        Fin
          (finiteDrawing.routeAt
            (metadataPhysicalIncidence
              second.segmentWitness.routeWitness.metadata
              second.segmentWitness.routeWitness.metadataIndex
              second.segmentWitness.routeWitness.literal
              second.segmentWitness.taggedLiteral.2)).length :=
      ⟨secondIndexed.pointIndex, secondPointIndexLt⟩
    have firstPointAt :
        (finiteDrawing.routeAt
          (metadataPhysicalIncidence
            first.segmentWitness.routeWitness.metadata
            first.segmentWitness.routeWitness.metadataIndex
            first.segmentWitness.routeWitness.literal
            first.segmentWitness.taggedLiteral.2)).get
              firstPointIndex =
          first.physicalPoint :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          first.physicalPointMember)).2
    have secondPointAt :
        (finiteDrawing.routeAt
          (metadataPhysicalIncidence
            second.segmentWitness.routeWitness.metadata
            second.segmentWitness.routeWitness.metadataIndex
            second.segmentWitness.routeWitness.literal
            second.segmentWitness.taggedLiteral.2)).get
              secondPointIndex =
          second.physicalPoint :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          second.physicalPointMember)).2
    have physicalEndpoints :=
      separated.2.2.2 firstPointIndex secondPointIndex
        (by simpa only [firstPointAt, secondPointAt] using physicalPointEq)
    have physicalEndpoints' :
        EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
            (finiteDrawing.routeAt
              (metadataPhysicalIncidence
                first.segmentWitness.routeWitness.metadata
                first.segmentWitness.routeWitness.metadataIndex
                first.segmentWitness.routeWitness.literal
                first.segmentWitness.taggedLiteral.2))
            first.physicalPoint ∧
          EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
            (finiteDrawing.routeAt
              (metadataPhysicalIncidence
                second.segmentWitness.routeWitness.metadata
                second.segmentWitness.routeWitness.metadataIndex
                second.segmentWitness.routeWitness.literal
                second.segmentWitness.taggedLiteral.2))
            second.physicalPoint := by
      simpa only [firstPointAt, secondPointAt] using physicalEndpoints
    have firstSimple := finitePlanar.1 firstIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt firstIncidenceIndex))
      at firstSimple
    rw [firstIncidenceAt] at firstSimple
    have secondSimple := finitePlanar.1 secondIncidenceIndex
    change
      LocalIncidenceDrawing.RouteIsSimple
        (finiteDrawing.routeAt
          (finiteDrawing.incidenceAt secondIncidenceIndex))
      at secondSimple
    rw [secondIncidenceAt] at secondSimple
    have firstPhysicalEndpoint :
        first.physicalIndexedPoint.IsEndpoint := by
      have indexedEndpoint :=
        EmbeddedCNFIncidenceDrawing.indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
          firstSimple.1 first.physicalPointMember physicalEndpoints'.1
      simpa only [
        FinalGaugedRoutePointOccurrenceWitness.physicalIndexedPoint,
        IndexedRoutePoint.IsEndpoint] using indexedEndpoint
    have secondPhysicalEndpoint :
        second.physicalIndexedPoint.IsEndpoint := by
      have indexedEndpoint :=
        EmbeddedCNFIncidenceDrawing.indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
          secondSimple.1 second.physicalPointMember physicalEndpoints'.2
      simpa only [
        FinalGaugedRoutePointOccurrenceWitness.physicalIndexedPoint,
        IndexedRoutePoint.IsEndpoint] using indexedEndpoint
    exact
      ⟨(first.physicalIndexedPoint_isEndpoint_iff).mp
          firstPhysicalEndpoint,
        (second.physicalIndexedPoint_isEndpoint_iff).mp
          secondPhysicalEndpoint⟩

end PeriodicOrthocrossing
end LeanTrominoes
