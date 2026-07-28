import LeanTrominoes.PeriodicGridDrawingMixedContinuousBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierRouteBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSegmentOccurrences

/-!
# Fundamental-square bounds for final noncarrier segments

Every final indexed segment has a physical representative in one retained
finite route.  If that route belongs to a noncarrier component, clause-anchor
normalization is coordinatewise remainder.  This file transfers the resulting
half-open fundamental-square bound from the physical route endpoints to the
final indexed segment.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Cancelling a common periodic occurrence shift leaves exactly the
clause-anchor normalization of the physical point. -/
private theorem point_eq_anchorNormalized_of_translated_eq
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    {point physical shift anchor : Cell}
    (translatedEq :
      Cell.add (placement.translation shift) point =
        Cell.add
          (placement.translation (Cell.sub shift anchor))
          physical) :
    point =
      Cell.sub physical (placement.translation anchor) := by
  rcases point with ⟨pointX, pointY⟩
  rcases physical with ⟨physicalX, physicalY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  rcases anchor with ⟨anchorX, anchorY⟩
  simp only [PeriodicVariablePlacement.translation, Cell.scale,
    Cell.add, Cell.sub, Prod.mk.injEq] at translatedEq ⊢
  constructor
  · nlinarith [translatedEq.1]
  · nlinarith [translatedEq.2]

/-- A final segment represented by noncarrier retained metadata has both
endpoints in the half-open fundamental square. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.endpointsInHalfOpenFundamentalSquare_of_not_carrier
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
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness
        formula indexed shift)
    (notCarrier :
      ¬∃ link,
        witness.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link) :
    let drawing :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula
    drawing.PositionInHalfOpenFundamentalSquare
        indexed.segment.start ∧
      drawing.PositionInHalfOpenFundamentalSquare
        indexed.segment.finish := by
  let metadata := witness.routeWitness.metadata
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let anchor :=
    PeriodicCNF.clauseAnchor
      (metadataGaugedPositionedClause formula metadata).literals
  have metadataIndexLt :
      witness.routeWitness.metadataIndex <
        (retainedDrawingPlanarSATClauseMetadata formula).length :=
    (List.getElem?_eq_some_iff.mp
      witness.routeWitness.metadataLookup).1
  have metadataMember :
      metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula := by
    have metadataAt :
        (retainedDrawingPlanarSATClauseMetadata formula)[
            witness.routeWitness.metadataIndex] =
          metadata :=
      (List.getElem?_eq_some_iff.mp
        witness.routeWitness.metadataLookup).2
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have valid : metadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula metadataMember
  have metadataClauseMember :
      metadata.clause ∈
        retainedDrawingPlanarSATFormula formula := by
    rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    exact List.mem_map.mpr
      ⟨metadata, metadataMember, rfl⟩
  have nonempty : metadata.clause.literals ≠ [] :=
    clausesNonempty metadata.clause metadataClauseMember
  rcases
      metadata.source.component.exists_macrocellCenter_of_not_carrier
        formula (by simpa only [metadata] using notCarrier) with
    ⟨center, centerEq⟩
  have physicalEndpoints :=
    gridPolylineSegments_endpoints_mem
      (List.fst_mem_of_mem_zipIdx
        witness.physicalSegmentMember)
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          (metadataPhysicalIncidence
            metadata witness.routeWitness.metadataIndex
            witness.routeWitness.literal witness.taggedLiteral.2) =
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex
          witness.taggedLiteral.2 := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.routeWitness.metadataLookup, metadata]
  have physicalStartMember :
      witness.physicalSegment.start ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex
          witness.taggedLiteral.2 := by
    rw [← localRouteEq]
    exact physicalEndpoints.1
  have physicalFinishMember :
      witness.physicalSegment.finish ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex
          witness.taggedLiteral.2 := by
    rw [← localRouteEq]
    exact physicalEndpoints.2
  have physicalStartBounds :=
    metadata_normalizedRoutePoint_inFundamental_of_noncarrier
      wellFormed degree isLocal metadata valid center centerEq
      nonempty witness.routeWitness.literalMember
      physicalStartMember
  have physicalFinishBounds :=
    metadata_normalizedRoutePoint_inFundamental_of_noncarrier
      wellFormed degree isLocal metadata valid center centerEq
      nonempty witness.routeWitness.literalMember
      physicalFinishMember
  have startTranslatedEq :=
    congrArg GridSegment.start witness.segmentEq
  have finishTranslatedEq :=
    congrArg GridSegment.finish witness.segmentEq
  change
    Cell.add (placement.translation shift)
        indexed.segment.start =
      Cell.add
        (placement.translation (Cell.sub shift anchor))
        witness.physicalSegment.start at startTranslatedEq
  change
    Cell.add (placement.translation shift)
        indexed.segment.finish =
      Cell.add
        (placement.translation (Cell.sub shift anchor))
        witness.physicalSegment.finish at finishTranslatedEq
  have startEq :
      indexed.segment.start =
        Cell.sub witness.physicalSegment.start
          (placement.translation anchor) :=
    point_eq_anchorNormalized_of_translated_eq
      placement startTranslatedEq
  have finishEq :
      indexed.segment.finish =
        Cell.sub witness.physicalSegment.finish
          (placement.translation anchor) :=
    point_eq_anchorNormalized_of_translated_eq
      placement finishTranslatedEq
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  have periodPositive : 0 < placement.period := by
    simpa [placement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have gridSizeEq : drawing.gridSize = placement.period := by
    simpa [drawing, placement,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
      using
        PositionedPeriodicCNF.incidenceDrawing_gridSize
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          periodPositive
  dsimp only at physicalStartBounds physicalFinishBounds
  dsimp only [drawing]
  constructor
  · unfold PeriodicGridDrawing.PositionInHalfOpenFundamentalSquare
    rw [startEq, gridSizeEq]
    simpa [metadata, placement, anchor,
      metadataGaugedPositionedClause] using
      physicalStartBounds
  · unfold PeriodicGridDrawing.PositionInHalfOpenFundamentalSquare
    rw [finishEq, gridSizeEq]
    simpa [metadata, placement, anchor,
      metadataGaugedPositionedClause] using
      physicalFinishBounds

end PeriodicOrthocrossing
end LeanTrominoes
