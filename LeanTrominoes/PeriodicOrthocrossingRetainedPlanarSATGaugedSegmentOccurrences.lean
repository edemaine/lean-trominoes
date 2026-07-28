import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences

/-!
# Physical representatives of gauged retained segment occurrences

The route-occurrence correspondence is refined here to individual indexed
segments.  Every segment occurrence in the final periodic quotient is the
same translated segment as one segment of the corresponding genuine route
in the finite retained drawing, at the same within-route index.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Translating every point of a polyline translates every one of its
segments. -/
private theorem gridPolylineSegments_translatePolyline_occurrence
    (offset : Cell) (points : List Cell) :
    gridPolylineSegments (translatePolyline offset points) =
      (gridPolylineSegments points).map
        (GridSegment.translate offset) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [translatePolyline, gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      simp only [translatePolyline, List.map_cons,
        gridPolylineSegments]
      change
        GridSegment.mk (Cell.add offset first) (Cell.add offset second) ::
            gridPolylineSegments
              (translatePolyline offset (second :: rest)) =
          GridSegment.translate offset (GridSegment.mk first second) ::
            (gridPolylineSegments (second :: rest)).map
              (GridSegment.translate offset)
      rw [tailInduction second]
      rfl

/-- An equality between translated routes matches their segments at every
shared syntactic segment index. -/
private theorem exists_segment_of_translatePolyline_eq
    {source target : List Cell}
    {sourceOffset targetOffset : Cell}
    {segment : GridSegment}
    {segmentIndex : Nat}
    (segmentMember :
      (segment, segmentIndex) ∈
        (gridPolylineSegments source).zipIdx)
    (routeEq :
      translatePolyline sourceOffset source =
        translatePolyline targetOffset target) :
    ∃ targetSegment : GridSegment,
      (targetSegment, segmentIndex) ∈
          (gridPolylineSegments target).zipIdx ∧
        segment.translate sourceOffset =
          targetSegment.translate targetOffset := by
  have translatedMember :
      (segment.translate sourceOffset, segmentIndex) ∈
        (gridPolylineSegments
          (translatePolyline sourceOffset source)).zipIdx := by
    rw [gridPolylineSegments_translatePolyline_occurrence,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(segment, segmentIndex), segmentMember, rfl⟩
  rw [routeEq,
    gridPolylineSegments_translatePolyline_occurrence,
    List.zipIdx_map] at translatedMember
  rcases List.mem_map.mp translatedMember with
    ⟨taggedTarget, taggedTargetMember, taggedTargetEq⟩
  rcases taggedTarget with ⟨targetSegment, targetIndex⟩
  have indexEq :
      targetIndex = segmentIndex :=
    congrArg Prod.snd taggedTargetEq
  have segmentEq :
      targetSegment.translate targetOffset =
        segment.translate sourceOffset :=
    congrArg Prod.fst taggedTargetEq
  refine ⟨targetSegment, ?_, segmentEq.symm⟩
  simpa only [indexEq] using taggedTargetMember

/-- A final indexed segment together with its final route coordinates and
its segment representative in the finite retained drawing. -/
structure FinalGaugedSegmentOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment)
    (shift : Cell) where
  finalRoute : List Cell
  finalRouteMember :
    (finalRoute, indexed.routeIndex) ∈
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).edgeRoutes.zipIdx
  taggedClause :
    PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  taggedClauseMember :
    taggedClause ∈
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.zipIdx
  taggedLiteral :
    PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  taggedLiteralMember :
    taggedLiteral ∈ taggedClause.1.literals.zipIdx
  finalRouteEq :
    finalRoute =
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2
  routeWitness :
    FinalGaugedRouteOccurrenceWitness
      formula taggedClause.2 taggedLiteral.2 shift
  physicalSegment : GridSegment
  physicalSegmentMember :
    (physicalSegment, indexed.segmentIndex) ∈
      (gridPolylineSegments
        ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          (metadataPhysicalIncidence
            routeWitness.metadata routeWitness.metadataIndex
            routeWitness.literal taggedLiteral.2))).zipIdx
  segmentEq :
    indexed.segment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation shift) =
      physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (Cell.sub shift
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula routeWitness.metadata).literals)))

/-- Every genuine indexed segment occurrence in the final quotient is an
anchor-adjusted translate of a same-indexed segment in one genuine finite
retained incidence route. -/
theorem
    exists_retainedPhysicalSegment_of_finalSegmentOccurrence
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
    (indexed : IndexedGridSegment)
    (indexedMember :
      indexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (shift : Cell) :
    Nonempty
      (FinalGaugedSegmentOccurrenceWitness
        formula indexed shift) := by
  unfold PeriodicGridDrawing.indexedSegments at indexedMember
  rcases List.mem_flatMap.mp indexedMember with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedSegment, taggedSegmentMember, indexedEq⟩
  subst indexed
  have routeMember :
      taggedRoute.1 ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes :=
    List.fst_mem_of_mem_zipIdx taggedRouteMember
  rcases exists_incidenceRoute_coordinates
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      (by
        simpa only [
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
          using routeMember) with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, finalRouteEq⟩
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula wellFormed degree isLocal clausesNonempty
        taggedClause taggedClauseMember
        taggedLiteral taggedLiteralMember shift with
    ⟨routeWitness⟩
  have routeOccurrenceEq :
      translatePolyline
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).translation shift)
          taggedRoute.1 =
        metadataPhysicalRouteOccurrence
          formula routeWitness.metadata routeWitness.metadataIndex
          routeWitness.literal taggedLiteral.2 shift := by
    rw [finalRouteEq]
    exact routeWitness.routeEq
  rcases exists_segment_of_translatePolyline_eq
      taggedSegmentMember routeOccurrenceEq with
    ⟨physicalSegment, physicalSegmentMember, segmentEq⟩
  refine ⟨{
    finalRoute := taggedRoute.1
    finalRouteMember := ?_
    taggedClause := taggedClause
    taggedClauseMember := taggedClauseMember
    taggedLiteral := taggedLiteral
    taggedLiteralMember := taggedLiteralMember
    finalRouteEq := finalRouteEq
    routeWitness := routeWitness
    physicalSegment := physicalSegment
    physicalSegmentMember := ?_
    segmentEq := ?_
  }⟩
  · simpa only using taggedRouteMember
  · simpa [metadataPhysicalRouteOccurrence] using
      physicalSegmentMember
  · simpa [metadataPhysicalRouteOccurrence] using segmentEq

end PeriodicOrthocrossing
end LeanTrominoes
