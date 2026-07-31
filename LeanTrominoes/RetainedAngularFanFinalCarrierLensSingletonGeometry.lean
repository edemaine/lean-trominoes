import LeanTrominoes.RetainedAngularFanCarrierLensSingletonGeometry
import LeanTrominoes.RetainedFinalFlatNormalizedRoutes

/-!
# Singleton escaped fans in final carrier occurrences

A final zero-shift route is represented by a retained finite component after
subtracting its clause anchor.  For a carrier source, that physical
translation is equivalently absorbed into the carrier link itself.  The
final route is therefore literally a route in an anchor-normalized equality
lens, so the carrier singleton certificate applies without separately
transporting every escaped-fan construction through translation.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT
open OccurrenceSplitRing

namespace PeriodicOrthocrossing

/-- Every genuine literal selected from carrier metadata is one of the two
literal positions in its local equality clause. -/
theorem
    FinalGaugedRouteOccurrenceWitness.literalIndex_lt_two_of_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.metadata.source =
        .carrier link localClauseIndex) :
    literalIndex < 2 := by
  have valid := witness.metadata_retainedValid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid
  rw [sourceEq] at valid
  have clauseLength :=
    drawingPlanarSATCarrierFormulaAt_clause_literals_length
      link (List.fst_mem_of_mem_zipIdx valid.2)
  have indexLt :=
    List.snd_lt_of_mem_zipIdx witness.literalMember
  rw [clauseLength] at indexLt
  exact indexLt

/-- Every segment of a physical final occurrence represented by carrier
metadata remains axis-aligned after its anchor-normalizing translation. -/
theorem
    FinalGaugedRouteOccurrenceWitness.routeSegments_axisAligned_of_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.metadata.source =
        .carrier link localClauseIndex)
    (segment : GridSegment)
    (segmentMember :
      segment ∈
        gridPolylineSegments
          (finalGaugedRouteOccurrence
            formula clauseIndex literalIndex (0, 0))) :
    segment.IsAxisAligned := by
  have valid := witness.metadata_retainedValid
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have orthogonal :
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).IsOrthogonal :=
    (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
      wellFormed degree isLocal valid'.1).2.1
  have clauseMember :
      (witness.metadata.clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal valid'.1]
    exact valid'.2
  rw [witness.routeEq] at segmentMember
  unfold metadataPhysicalRouteOccurrence translatePolyline
    at segmentMember
  rw [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
    at segmentMember
  rcases List.mem_map.mp segmentMember with
    ⟨physicalSegment, physicalSegmentMember, segmentEq⟩
  subst segment
  apply
    (GridSegment.isAxisAligned_translate _ _).mpr
  apply
    (drawingPlanarSATCarrierLensIncidenceDrawing formula link)
      |>.embeddedSegment_isAxisAligned_of_members
        orthogonal clauseMember witness.literalMember
  simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.metadataLookup, sourceEq,
    DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using
      physicalSegmentMember

/-- The carrier link underlying a zero-shift final route after absorbing the
witness's physical anchor-normalization shift. -/
def FinalGaugedRouteOccurrenceWitness.anchorNormalizedCarrierLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (link : EqualityLink CarrierNode) :
    EqualityLink CarrierNode :=
  carrierLinkPeriodTranslate formula.incidenceGraph link
    witness.physicalShift

/-- At external shift zero, a bare final occurrence witness has physical
shift equal to the negated finite clause anchor. -/
theorem
    FinalGaugedRouteOccurrenceWitness.physicalShift_eq_neg_anchor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0)) :
    witness.physicalShift =
      Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula witness.metadata).literals) := by
  unfold FinalGaugedRouteOccurrenceWitness.physicalShift
  rcases
      PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause
          formula witness.metadata).literals with
    ⟨anchorX, anchorY⟩
  simp [Cell.sub, Cell.neg]

/-- A retained carrier occurrence's anchor-normalized link belongs to the
raw retained carrier window. -/
theorem
    FinalGaugedRouteOccurrenceWitness.anchorNormalizedCarrierLink_mem_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.metadata.source =
        .carrier link localClauseIndex) :
    witness.anchorNormalizedCarrierLink link ∈
      retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph := by
  have nonempty :
      witness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := witness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have anchorNormalized :=
    witness.metadata.carrier_anchorNormalize_mem_raw
      wellFormed degree isLocal
      witness.metadata_retainedValid
      nonempty link localClauseIndex sourceEq
  simpa [FinalGaugedRouteOccurrenceWitness.anchorNormalizedCarrierLink,
    witness.physicalShift_eq_neg_anchor] using anchorNormalized

/-- A zero-shift final carrier occurrence is literally the corresponding
route of its anchor-normalized retained equality lens. -/
theorem
    FinalGaugedRouteOccurrenceWitness.route_eq_anchorNormalizedCarrierLink
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.metadata.source =
        .carrier link localClauseIndex) :
    finalGaugedRouteOccurrence
        formula clauseIndex literalIndex (0, 0) =
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula
        (witness.anchorNormalizedCarrierLink link)).routes
          localClauseIndex literalIndex := by
  rw [witness.routeEq]
  unfold metadataPhysicalRouteOccurrence
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).routeAt
            (metadataPhysicalIncidence
              witness.metadata witness.metadataIndex
              witness.literal literalIndex) =
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes
            localClauseIndex literalIndex := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.metadataLookup, sourceEq,
      DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex]
  rw [localRouteEq]
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  simpa [FinalGaugedRouteOccurrenceWitness.anchorNormalizedCarrierLink,
    FinalGaugedRouteOccurrenceWitness.physicalShift] using
    (drawingPlanarSATCarrierLensIncidenceDrawing_routes_periodTranslate
      formula link witness.physicalShift
      localClauseIndex literalIndex).symm

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

/-- The complete escaped replacement of a singleton final carrier route
remains separated from the other final route prefix in the same carrier
clause. -/
theorem
    finalGaugedCarrierRoutes_singletonPrefix_escapedCompleteRoute_separated_from_partnerPrefix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex firstLiteralIndex secondLiteralIndex : Nat}
    (firstWitness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex firstLiteralIndex (0, 0))
    (secondWitness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex secondLiteralIndex (0, 0))
    (metadataEq :
      firstWitness.metadata = secondWitness.metadata)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      firstWitness.metadata.source =
        .carrier link localClauseIndex)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (factor : Nat)
    (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        (finalGaugedRouteOccurrence
          formula clauseIndex firstLiteralIndex (0, 0)).length)
    (singletonPrefix :
      (finalGaugedRouteOccurrence
        formula clauseIndex firstLiteralIndex
          (0, 0)).dropLast.length = 1) :
    ∃ port : Port, ∃ length : Nat,
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector
            (finalGaugedRouteOccurrence
              formula clauseIndex firstLiteralIndex (0, 0))) =
        some (.compass port, length) ∧
      (EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                (finalGaugedRouteOccurrence
                  formula clauseIndex firstLiteralIndex
                    (0, 0))).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot)
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              (finalGaugedRouteOccurrence
                formula clauseIndex secondLiteralIndex
                  (0, 0)))).dropLast ∧
        EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                (finalGaugedRouteOccurrence
                  formula clauseIndex firstLiteralIndex
                    (0, 0))).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot)
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              (finalGaugedRouteOccurrence
                formula clauseIndex secondLiteralIndex
                  (0, 0)))).dropLast) := by
  have secondSourceEq :
      secondWitness.metadata.source =
        .carrier link localClauseIndex := by
    exact
      (congrArg DrawingPlanarSATClauseMetadata.source metadataEq).symm.trans
        sourceEq
  have shiftsEq :
      firstWitness.physicalShift =
        secondWitness.physicalShift := by
    unfold FinalGaugedRouteOccurrenceWitness.physicalShift
    rw [metadataEq]
  let normalizedLink :=
    firstWitness.anchorNormalizedCarrierLink link
  have firstRouteEq :
      finalGaugedRouteOccurrence
          formula clauseIndex firstLiteralIndex (0, 0) =
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula normalizedLink).routes
            localClauseIndex firstLiteralIndex := by
    simpa [normalizedLink] using
      firstWitness.route_eq_anchorNormalizedCarrierLink
        link localClauseIndex sourceEq
  have secondRouteEq :
      finalGaugedRouteOccurrence
          formula clauseIndex secondLiteralIndex (0, 0) =
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula normalizedLink).routes
            localClauseIndex secondLiteralIndex := by
    simpa [normalizedLink,
      FinalGaugedRouteOccurrenceWitness.anchorNormalizedCarrierLink,
      ← shiftsEq] using
        secondWitness.route_eq_anchorNormalizedCarrierLink
          link localClauseIndex secondSourceEq
  have normalizedLinkMember :
      normalizedLink ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph := by
    simpa [normalizedLink] using
      firstWitness.anchorNormalizedCarrierLink_mem_raw
        wellFormed degree isLocal link localClauseIndex sourceEq
  have geometry :
      EqualityLink.LensGeometry
        (CarrierNode.position formula.incidenceGraph)
        normalizedLink :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal normalizedLinkMember
  have separated :=
    drawingPlanarSATCarrierLensIncidenceDrawing_singletonPrefix_escapedCompleteRoute_separated_from_partnerPrefix
      formula normalizedLink geometry
      localClauseIndex firstLiteralIndex secondLiteralIndex
      indicesDifferent secondLiteralIndexLt
      factor factorPositive slot
      (by simpa [← firstRouteEq] using firstLength)
      (by simpa [← firstRouteEq] using singletonPrefix)
  rw [← firstRouteEq, ← secondRouteEq] at separated
  exact separated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
