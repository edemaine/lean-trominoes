import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup

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

/-- Metadata-rich incidences of the final deduplicated periodic source.
Keeping this enumeration opaque avoids repeatedly normalizing the entire
retained formula while elaborating dependent segment witnesses. -/
def finalGaugedIncidences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List
      (CNFIncidence
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  PeriodicCNF.incidencesWithMetadata
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase

/-- Metadata coordinates of one route tagged in the flat final route list. -/
structure FinalGaugedRouteCoordinates
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedRoute : List Cell × Nat) where
  finalIncidence :
    CNFIncidence
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  finalIncidenceMember :
    finalIncidence ∈ (finalGaugedIncidences formula).zipIdx
  finalIncidenceIndexEq :
    finalIncidence.2 = taggedRoute.2
  taggedClause :
    PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  taggedClauseMember :
    taggedClause ∈
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.zipIdx
  taggedClauseIndexEq :
    taggedClause.2 = finalIncidence.1.clauseIndex
  taggedLiteral :
    PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  taggedLiteralMember :
    taggedLiteral ∈ taggedClause.1.literals.zipIdx
  finalRouteEq :
    taggedRoute.1 =
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2

/-- Recover metadata-rich clause and literal coordinates without unfolding
the flattened incidence source in every downstream segment proof. -/
theorem exists_finalGaugedRouteCoordinates
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedRoute : List Cell × Nat)
    (taggedRouteMember :
      taggedRoute ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx) :
    Nonempty (FinalGaugedRouteCoordinates formula taggedRoute) := by
  rcases
      PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
        taggedRoute
        (by
          simpa only [
            retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
            using taggedRouteMember) with
    ⟨taggedIncidence, taggedIncidenceMember,
      positionedClause, literal,
      positionedClauseMember, literalMember,
      finalRouteEq, finalIncidenceIndexEq⟩
  let taggedClause :
      PositionedPeriodicClause
          (WrappedPeriodicPlanarSATVariable Variable) × Nat :=
    (positionedClause, taggedIncidence.1.clauseIndex)
  let taggedLiteral :
      PeriodicLiteral
          (WrappedPeriodicPlanarSATVariable Variable) × Nat :=
    (literal, taggedIncidence.1.literalIndex)
  refine ⟨{
    finalIncidence := taggedIncidence
    finalIncidenceMember := ?_
    finalIncidenceIndexEq := finalIncidenceIndexEq
    taggedClause := taggedClause
    taggedClauseMember := ?_
    taggedClauseIndexEq := rfl
    taggedLiteral := taggedLiteral
    taggedLiteralMember := ?_
    finalRouteEq := ?_
  }⟩
  · simpa only [finalGaugedIncidences] using
      taggedIncidenceMember
  · simpa only [taggedClause] using
      positionedClauseMember
  · simpa only [taggedClause, taggedLiteral] using
      literalMember
  · simpa only [taggedClause, taggedLiteral] using
      finalRouteEq

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
  finalIncidence :
    CNFIncidence
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  finalIncidenceMember :
    finalIncidence ∈
      (finalGaugedIncidences formula).zipIdx
  finalIncidenceIndexEq :
    finalIncidence.2 = indexed.routeIndex
  taggedClause :
    PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) × Nat
  taggedClauseMember :
    taggedClause ∈
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.zipIdx
  taggedClauseIndexEq :
    taggedClause.2 = finalIncidence.1.clauseIndex
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
  rcases exists_finalGaugedRouteCoordinates
      formula taggedRoute taggedRouteMember with
    ⟨coordinates⟩
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula wellFormed degree isLocal clausesNonempty
        coordinates.taggedClause
        coordinates.taggedClauseMember
        coordinates.taggedLiteral
        coordinates.taggedLiteralMember shift with
    ⟨routeWitness⟩
  have routeOccurrenceEq :
      translatePolyline
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).translation shift)
          taggedRoute.1 =
        metadataPhysicalRouteOccurrence
          formula routeWitness.metadata routeWitness.metadataIndex
          routeWitness.literal coordinates.taggedLiteral.2 shift := by
    rw [coordinates.finalRouteEq]
    exact routeWitness.routeEq
  rcases exists_segment_of_translatePolyline_eq
      taggedSegmentMember routeOccurrenceEq with
    ⟨physicalSegment, physicalSegmentMember, segmentEq⟩
  refine ⟨{
    finalRoute := taggedRoute.1
    finalRouteMember := ?_
    finalIncidence := coordinates.finalIncidence
    finalIncidenceMember := coordinates.finalIncidenceMember
    finalIncidenceIndexEq := coordinates.finalIncidenceIndexEq
    taggedClause := coordinates.taggedClause
    taggedClauseMember := coordinates.taggedClauseMember
    taggedClauseIndexEq := coordinates.taggedClauseIndexEq
    taggedLiteral := coordinates.taggedLiteral
    taggedLiteralMember := coordinates.taggedLiteralMember
    finalRouteEq := coordinates.finalRouteEq
    routeWitness := routeWitness
    physicalSegment := physicalSegment
    physicalSegmentMember := ?_
    segmentEq := ?_
  }⟩
  · simpa only using taggedRouteMember
  · simpa [metadataPhysicalRouteOccurrence] using
      physicalSegmentMember
  · simpa [metadataPhysicalRouteOccurrence] using segmentEq

/-- The occurrence key of the corresponding segment in the translated
finite retained drawing.  Clause-anchor normalization changes only the
translation component of the final periodic occurrence key. -/
def FinalGaugedSegmentOccurrenceWitness.physicalKey
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    Nat × Nat × Cell :=
  (witness.finalIncidence.2, indexed.segmentIndex,
    Cell.sub shift
      (PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause
          formula witness.routeWitness.metadata).literals))

/-- Equal final flat-incidence indices select the same retained physical
clause metadata, even though route normalization has changed the clause and
literal presentation coordinates. -/
private theorem metadata_eq_of_finalIncidenceIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (indexEq :
      first.finalIncidence.2 = second.finalIncidence.2) :
    first.routeWitness.metadata = second.routeWitness.metadata := by
  have firstIncidenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.finalIncidenceMember
  have secondIncidenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.finalIncidenceMember
  have incidenceValueEq :
      first.finalIncidence.1 = second.finalIncidence.1 := by
    rw [indexEq] at firstIncidenceLookup
    exact Option.some.inj
      (firstIncidenceLookup.symm.trans secondIncidenceLookup)
  have clauseIndexEq :
      first.taggedClause.2 = second.taggedClause.2 := by
    exact first.taggedClauseIndexEq.trans
      ((congrArg
        (fun incidence :
          CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
            incidence.clauseIndex)
        incidenceValueEq).trans second.taggedClauseIndexEq.symm)
  have firstClauseLookup :=
    first.routeWitness.finalClauseLookup
  have secondClauseLookup :=
    second.routeWitness.finalClauseLookup
  have finalClauseEq :
      first.routeWitness.finalClause =
        second.routeWitness.finalClause := by
    exact Option.some.inj
      (firstClauseLookup.symm.trans
        ((congrArg
          (fun clauseIndex =>
            (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).clauses[clauseIndex]?)
          clauseIndexEq).trans secondClauseLookup))
  have metadataIndexEq :
      first.routeWitness.metadataIndex =
        second.routeWitness.metadataIndex := by
    rw [first.routeWitness.representativeIndexEq,
      second.routeWitness.representativeIndexEq,
      finalClauseEq]
  have firstMetadataLookup :=
    first.routeWitness.metadataLookup
  have secondMetadataLookup :=
    second.routeWitness.metadataLookup
  rw [metadataIndexEq] at firstMetadataLookup
  exact Option.some.inj
    (firstMetadataLookup.symm.trans secondMetadataLookup)

/-- The anchor-adjusted physical occurrence key preserves and reflects the
identity of a final periodic segment occurrence. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.physicalKey_eq_iff_segmentOccurrenceKey_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift) :
    first.physicalKey = second.physicalKey ↔
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift =
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift := by
  constructor
  · intro physicalKeyEq
    have incidenceIndexEq :
        first.finalIncidence.2 = second.finalIncidence.2 :=
      congrArg Prod.fst physicalKeyEq
    have segmentIndexEq :
        firstIndexed.segmentIndex =
          secondIndexed.segmentIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.2.1)
        physicalKeyEq
    have adjustedShiftEq :
        Cell.sub firstShift
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula first.routeWitness.metadata).literals) =
          Cell.sub secondShift
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula second.routeWitness.metadata).literals) :=
      congrArg (fun key : Nat × Nat × Cell => key.2.2)
        physicalKeyEq
    have metadataEq :=
      metadata_eq_of_finalIncidenceIndex_eq
        first second incidenceIndexEq
    have shiftEq : firstShift = secondShift := by
      apply Cell.sub_right_injective
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula first.routeWitness.metadata).literals)
      simpa only [metadataEq] using adjustedShiftEq
    have routeIndexEq :
        firstIndexed.routeIndex = secondIndexed.routeIndex :=
      first.finalIncidenceIndexEq.symm.trans
        (incidenceIndexEq.trans second.finalIncidenceIndexEq)
    simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
      Prod.mk.injEq]
    exact ⟨routeIndexEq, segmentIndexEq, shiftEq⟩
  · intro occurrenceKeyEq
    have routeIndexEq :
        firstIndexed.routeIndex = secondIndexed.routeIndex :=
      congrArg Prod.fst occurrenceKeyEq
    have segmentIndexEq :
        firstIndexed.segmentIndex =
          secondIndexed.segmentIndex :=
      congrArg (fun key : Nat × Nat × Cell => key.2.1)
        occurrenceKeyEq
    have shiftEq : firstShift = secondShift :=
      congrArg (fun key : Nat × Nat × Cell => key.2.2)
        occurrenceKeyEq
    have incidenceIndexEq :
        first.finalIncidence.2 = second.finalIncidence.2 :=
      first.finalIncidenceIndexEq.trans
        (routeIndexEq.trans second.finalIncidenceIndexEq.symm)
    have metadataEq :=
      metadata_eq_of_finalIncidenceIndex_eq
        first second incidenceIndexEq
    have adjustedShiftEq :
        Cell.sub firstShift
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula first.routeWitness.metadata).literals) =
          Cell.sub secondShift
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula second.routeWitness.metadata).literals) := by
      rw [metadataEq, shiftEq]
    simp only [FinalGaugedSegmentOccurrenceWitness.physicalKey,
      Prod.mk.injEq]
    exact ⟨incidenceIndexEq, segmentIndexEq, adjustedShiftEq⟩

end PeriodicOrthocrossing
end LeanTrominoes
