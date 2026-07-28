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
  taggedLiteralIndexEq :
    taggedLiteral.2 = finalIncidence.1.literalIndex
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
    taggedLiteralIndexEq := rfl
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
  taggedLiteralIndexEq :
    taggedLiteral.2 = finalIncidence.1.literalIndex
  finalRouteEq :
    finalRoute =
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula taggedClause.2 taggedLiteral.2
  routeWitness :
    FinalGaugedRouteOccurrenceWitness
      formula taggedClause.2 taggedLiteral.2 shift
  physicalIncidenceIndex : Nat
  physicalIncidenceMember :
    (metadataPhysicalIncidence
        routeWitness.metadata routeWitness.metadataIndex
        routeWitness.literal taggedLiteral.2,
      physicalIncidenceIndex) ∈
      (retainedDrawingPlanarSATLocalIncidenceDrawing
        formula).incidences.zipIdx
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
  rcases List.mem_iff_getElem.mp routeWitness.incidenceMember with
    ⟨physicalIncidenceIndex, physicalIncidenceIndexLt,
      physicalIncidenceEq⟩
  have physicalIncidenceMember :
      (metadataPhysicalIncidence
          routeWitness.metadata routeWitness.metadataIndex
          routeWitness.literal coordinates.taggedLiteral.2,
        physicalIncidenceIndex) ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).incidences.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨physicalIncidenceIndexLt, physicalIncidenceEq⟩
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
    taggedLiteralIndexEq := coordinates.taggedLiteralIndexEq
    finalRouteEq := coordinates.finalRouteEq
    routeWitness := routeWitness
    physicalIncidenceIndex := physicalIncidenceIndex
    physicalIncidenceMember := physicalIncidenceMember
    physicalSegment := physicalSegment
    physicalSegmentMember := ?_
    segmentEq := ?_
  }⟩
  · simpa only using taggedRouteMember
  · simpa [metadataPhysicalRouteOccurrence] using
      physicalSegmentMember
  · simpa [metadataPhysicalRouteOccurrence] using segmentEq

/-- The finite retained drawing translate represented by a final periodic
segment occurrence after undoing clause-anchor normalization. -/
def FinalGaugedSegmentOccurrenceWitness.physicalShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    Cell :=
  Cell.sub shift
    (PeriodicCNF.clauseAnchor
      (metadataGaugedPositionedClause
        formula witness.routeWitness.metadata).literals)

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
  (witness.physicalIncidenceIndex, indexed.segmentIndex,
    witness.physicalShift)

/-- Equal final flat indices select the same metadata-rich final
incidence. -/
private theorem finalIncidence_eq_of_index_eq
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
    first.finalIncidence.1 = second.finalIncidence.1 := by
  have firstIncidenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.finalIncidenceMember
  have secondIncidenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.finalIncidenceMember
  rw [indexEq] at firstIncidenceLookup
  exact Option.some.inj
    (firstIncidenceLookup.symm.trans secondIncidenceLookup)

/-- Equal final flat-incidence indices select the same representative
physical metadata index. -/
private theorem metadataIndex_eq_of_finalIncidenceIndex_eq
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
    first.routeWitness.metadataIndex =
      second.routeWitness.metadataIndex := by
  have incidenceValueEq :=
    finalIncidence_eq_of_index_eq first second indexEq
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
  rw [first.routeWitness.representativeIndexEq,
    second.routeWitness.representativeIndexEq,
    finalClauseEq]

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
  have metadataIndexEq :=
    metadataIndex_eq_of_finalIncidenceIndex_eq
      first second indexEq
  have firstMetadataLookup :=
    first.routeWitness.metadataLookup
  have secondMetadataLookup :=
    second.routeWitness.metadataLookup
  rw [metadataIndexEq] at firstMetadataLookup
  exact Option.some.inj
    (firstMetadataLookup.symm.trans secondMetadataLookup)

/-- Equal final flat-incidence indices select the same metadata-rich
incidence in the retained finite drawing. -/
private theorem physicalIncidence_eq_of_finalIncidenceIndex_eq
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
    metadataPhysicalIncidence
        first.routeWitness.metadata
        first.routeWitness.metadataIndex
        first.routeWitness.literal first.taggedLiteral.2 =
      metadataPhysicalIncidence
        second.routeWitness.metadata
        second.routeWitness.metadataIndex
        second.routeWitness.literal second.taggedLiteral.2 := by
  have finalIncidenceEq :=
    finalIncidence_eq_of_index_eq first second indexEq
  have metadataIndexEq :=
    metadataIndex_eq_of_finalIncidenceIndex_eq
      first second indexEq
  have metadataEq :=
    metadata_eq_of_finalIncidenceIndex_eq
      first second indexEq
  have literalIndexEq :
      first.taggedLiteral.2 = second.taggedLiteral.2 :=
    first.taggedLiteralIndexEq.trans
      ((congrArg CNFIncidence.literalIndex finalIncidenceEq).trans
        second.taggedLiteralIndexEq.symm)
  have firstLiteralLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.routeWitness.literalMember
  have secondLiteralLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.routeWitness.literalMember
  have literalLookupEq :
      first.routeWitness.metadata.clause.literals[
          first.taggedLiteral.2]? =
        second.routeWitness.metadata.clause.literals[
          second.taggedLiteral.2]? := by
    calc
      first.routeWitness.metadata.clause.literals[
            first.taggedLiteral.2]? =
          second.routeWitness.metadata.clause.literals[
            first.taggedLiteral.2]? :=
        congrArg
          (fun metadata :
            DrawingPlanarSATClauseMetadata Variable =>
              metadata.clause.literals[first.taggedLiteral.2]?)
          metadataEq
      _ =
          second.routeWitness.metadata.clause.literals[
            second.taggedLiteral.2]? :=
        congrArg
          (fun literalIndex =>
            second.routeWitness.metadata.clause.literals[
              literalIndex]?)
          literalIndexEq
  have literalEq :
      first.routeWitness.literal =
        second.routeWitness.literal := by
    exact Option.some.inj
      (firstLiteralLookup.symm.trans
        (literalLookupEq.trans secondLiteralLookup))
  simp only [metadataPhysicalIncidence, EmbeddedCNFIncidence.mk.injEq]
  exact ⟨congrArg DrawingPlanarSATClauseMetadata.clause metadataEq,
    metadataIndexEq, literalEq, literalIndexEq⟩

/-- Equal final flat-incidence indices select the same flat incidence index
in the retained finite drawing. -/
private theorem physicalIncidenceIndex_eq_of_finalIncidenceIndex_eq
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
    first.physicalIncidenceIndex =
      second.physicalIncidenceIndex := by
  have physicalIncidenceEq :=
    physicalIncidence_eq_of_finalIncidenceIndex_eq
      first second indexEq
  have firstLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.physicalIncidenceMember
  have secondLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.physicalIncidenceMember
  have firstLookup' :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).incidences[
          first.physicalIncidenceIndex]? =
        some
          (metadataPhysicalIncidence
            second.routeWitness.metadata
            second.routeWitness.metadataIndex
            second.routeWitness.literal second.taggedLiteral.2) :=
    firstLookup.trans (congrArg some physicalIncidenceEq)
  exact List.Nodup.index_eq_of_getElem?_eq_some
    (embeddedCNFIncidences_nodup
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).formula)
    firstLookup' secondLookup

/-- Equal retained finite incidence indices recover equal final flat
incidence indices. -/
private theorem finalIncidenceIndex_eq_of_physicalIncidenceIndex_eq
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
    (physicalIndexEq :
      first.physicalIncidenceIndex =
        second.physicalIncidenceIndex) :
    first.finalIncidence.2 = second.finalIncidence.2 := by
  have firstPhysicalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.physicalIncidenceMember
  have secondPhysicalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.physicalIncidenceMember
  have physicalIncidenceEq :
      metadataPhysicalIncidence
          first.routeWitness.metadata
          first.routeWitness.metadataIndex
          first.routeWitness.literal first.taggedLiteral.2 =
        metadataPhysicalIncidence
          second.routeWitness.metadata
          second.routeWitness.metadataIndex
          second.routeWitness.literal second.taggedLiteral.2 := by
    rw [physicalIndexEq] at firstPhysicalLookup
    exact Option.some.inj
      (firstPhysicalLookup.symm.trans secondPhysicalLookup)
  have metadataIndexEq :
      first.routeWitness.metadataIndex =
        second.routeWitness.metadataIndex := by
    exact congrArg EmbeddedCNFIncidence.clauseIndex
      physicalIncidenceEq
  have firstMetadataLookup :=
    first.routeWitness.metadataLookup
  have secondMetadataLookup :=
    second.routeWitness.metadataLookup
  have metadataEq :
      first.routeWitness.metadata =
        second.routeWitness.metadata := by
    rw [metadataIndexEq] at firstMetadataLookup
    exact Option.some.inj
      (firstMetadataLookup.symm.trans secondMetadataLookup)
  have finalLiteralsEq :
      first.routeWitness.finalClause.literals =
        second.routeWitness.finalClause.literals :=
    first.routeWitness.normalizedLiteralsEq.symm.trans
      ((congrArg
        (metadataGaugedNormalizedClause formula)
        metadataEq).trans
        second.routeWitness.normalizedLiteralsEq)
  let source :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  have firstFinalClauseMember :
      first.routeWitness.finalClause ∈
        source.deduplicateByLiterals.clauses := by
    apply List.mem_iff_getElem?.mpr
    exact
      ⟨first.taggedClause.2,
        by
          simpa only [source,
            retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
            using first.routeWitness.finalClauseLookup⟩
  have secondFinalClauseMember :
      second.routeWitness.finalClause ∈
        source.deduplicateByLiterals.clauses := by
    apply List.mem_iff_getElem?.mpr
    exact
      ⟨second.taggedClause.2,
        by
          simpa only [source,
            retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
            using second.routeWitness.finalClauseLookup⟩
  have firstRepresentative :=
    PositionedPeriodicCNF.eq_representative_of_mem_deduplicateByLiterals
      source first.routeWitness.finalClause firstFinalClauseMember
  have secondRepresentative :=
    PositionedPeriodicCNF.eq_representative_of_mem_deduplicateByLiterals
      source second.routeWitness.finalClause secondFinalClauseMember
  have finalClauseEq :
      first.routeWitness.finalClause =
        second.routeWitness.finalClause := by
    calc
      first.routeWitness.finalClause =
          ⟨source.representativeClausePosition
              first.routeWitness.finalClause.literals,
            first.routeWitness.finalClause.literals⟩ :=
        firstRepresentative
      _ =
          ⟨source.representativeClausePosition
              second.routeWitness.finalClause.literals,
            second.routeWitness.finalClause.literals⟩ := by
        rw [finalLiteralsEq]
      _ = second.routeWitness.finalClause :=
        secondRepresentative.symm
  have firstFinalClauseLookup :
      source.deduplicateByLiterals.clauses[
          first.taggedClause.2]? =
        some second.routeWitness.finalClause := by
    simpa only [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using
        first.routeWitness.finalClauseLookup.trans
          (congrArg some finalClauseEq)
  have secondFinalClauseLookup :
      source.deduplicateByLiterals.clauses[
          second.taggedClause.2]? =
        some second.routeWitness.finalClause := by
    simpa only [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using second.routeWitness.finalClauseLookup
  have clauseIndexEq :
      first.taggedClause.2 = second.taggedClause.2 :=
    List.Nodup.index_eq_of_getElem?_eq_some
      (PositionedPeriodicCNF.deduplicateByLiterals_clauses_nodup
        source)
      firstFinalClauseLookup secondFinalClauseLookup
  have taggedLiteralIndexEq :
      first.taggedLiteral.2 = second.taggedLiteral.2 :=
    congrArg EmbeddedCNFIncidence.literalIndex
      physicalIncidenceEq
  have finalClauseCoordinateEq :
      first.finalIncidence.1.clauseIndex =
        second.finalIncidence.1.clauseIndex :=
    first.taggedClauseIndexEq.symm.trans
      (clauseIndexEq.trans second.taggedClauseIndexEq)
  have finalLiteralCoordinateEq :
      first.finalIncidence.1.literalIndex =
        second.finalIncidence.1.literalIndex :=
    first.taggedLiteralIndexEq.symm.trans
      (taggedLiteralIndexEq.trans
        second.taggedLiteralIndexEq)
  have finalIncidenceEq :
      first.finalIncidence.1 = second.finalIncidence.1 := by
    apply PeriodicCNF.incidence_eq_of_indices_eq
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
    · exact List.fst_mem_of_mem_zipIdx
        first.finalIncidenceMember
    · exact List.fst_mem_of_mem_zipIdx
        second.finalIncidenceMember
    · exact finalClauseCoordinateEq
    · exact finalLiteralCoordinateEq
  have firstFinalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.finalIncidenceMember
  have secondFinalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.finalIncidenceMember
  have firstFinalLookup' :
      (finalGaugedIncidences formula)[first.finalIncidence.2]? =
        some second.finalIncidence.1 :=
    firstFinalLookup.trans (congrArg some finalIncidenceEq)
  exact List.Nodup.index_eq_of_getElem?_eq_some
    (by
      simpa only [finalGaugedIncidences] using
        PeriodicCNF.incidencesWithMetadata_nodup
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase)
    firstFinalLookup' secondFinalLookup

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
    have physicalIncidenceIndexEq :
        first.physicalIncidenceIndex =
          second.physicalIncidenceIndex :=
      congrArg Prod.fst physicalKeyEq
    have incidenceIndexEq :
        first.finalIncidence.2 = second.finalIncidence.2 :=
      finalIncidenceIndex_eq_of_physicalIncidenceIndex_eq
        first second physicalIncidenceIndexEq
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
    have physicalIncidenceIndexEq :
        first.physicalIncidenceIndex =
          second.physicalIncidenceIndex :=
      physicalIncidenceIndex_eq_of_finalIncidenceIndex_eq
        first second incidenceIndexEq
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
    exact
      ⟨physicalIncidenceIndexEq,
        segmentIndexEq, adjustedShiftEq⟩

end PeriodicOrthocrossing
end LeanTrominoes
