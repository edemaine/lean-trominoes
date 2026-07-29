import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointCarrierNoncarrierReduction

/-!
# Endpoint-only carrier--noncarrier route-point contacts

The raw reduction is instantiated for each noncarrier component family.
The family geometry supplies only the neighboring source-coordinate data;
the endpoint conclusion itself always comes from the same finite
`RoutesAvoidEachOther` certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Carrier and routed-clause route points can coincide only at their outer
route endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier link)
    (site : ClauseRouteSite)
    (secondSourceEq :
      second.segmentWitness.routeWitness.metadata.source =
        .routedClause site)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have siteMember :
      site ∈ drawingClauseRouteSites formula := by
    have sourceMember :=
      second.segmentWitness.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have secondNonempty :
      second.segmentWitness.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember :=
      second.segmentWitness.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have secondCenterEq :
      second.segmentWitness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2) := by
    rw [secondSourceEq]
    rfl
  have secondAnchorEq :
      second.segmentWitness.sourceClauseAnchor = site.2 := by
    simpa only [
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (second.segmentWitness.routeWitness.metadata
        |>.sourceClauseAnchor_eq_liftedVertexTranslate
          wellFormed degree isLocal
          second.segmentWitness.metadata_retainedValid
          secondNonempty (.clause site.1)
          (drawingClauseRouteSite_vertex_mem formula siteMember)
          site.2 secondCenterEq)
  apply
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier_of_balanced_source_coordinate
      formula wellFormed degree isLocal clausesNonempty
      first second link firstComponentEq secondNotCarrier (0, 0)
  · intro adjustment adjustmentNeighbor
    rw [secondSourceEq]
    change
      IsNeighborTranslation
        (Cell.add site.2
          (Cell.add
            (Cell.neg second.segmentWitness.sourceClauseAnchor)
            adjustment))
    have translatedSiteEq :
        Cell.add site.2
            (Cell.add
              (Cell.neg second.segmentWitness.sourceClauseAnchor)
              adjustment) =
          adjustment := by
      rw [secondAnchorEq]
      rcases site.2 with ⟨siteX, siteY⟩
      rcases adjustment with ⟨adjustmentX, adjustmentY⟩
      simp [Cell.add, Cell.neg, Cell.sub]
    rw [translatedSiteEq]
    simpa [Cell.add] using adjustmentNeighbor
  · have relativeSiteNeighbor :=
      first.carrier_liftedVertex_relative_neighbor_of_pointEquality
        formula wellFormed degree isLocal second
        link firstComponentEq secondNotCarrier
        (.clause site.1)
        (drawingClauseRouteSite_vertex_mem formula siteMember)
        site.2 secondCenterEq equal
    have zeroNeighbor :
        IsNeighborTranslation (0, 0) := by
      simp [IsNeighborTranslation]
    have relativeSiteDouble :=
      relativeSiteNeighbor.sub_mem_doubleNeighborTranslations
        zeroNeighbor
    have desiredEq :
        Cell.sub
            (Cell.add
              (Cell.add link.first.translate
                (Cell.neg first.segmentWitness.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            (0, 0) =
          Cell.sub
            (Cell.sub
              (Cell.add link.first.translate
                (Cell.neg first.segmentWitness.sourceClauseAnchor))
              (Cell.add site.2
                (Cell.sub second.segmentWitness.physicalShift firstShift)))
            (0, 0) := by
      rw [second.segmentWitness.physicalShift_eq, secondAnchorEq]
      rcases link.first.translate with ⟨linkX, linkY⟩
      rcases first.segmentWitness.sourceClauseAnchor with
        ⟨firstAnchorX, firstAnchorY⟩
      rcases firstShift with ⟨firstShiftX, firstShiftY⟩
      rcases secondShift with ⟨secondShiftX, secondShiftY⟩
      rcases site.2 with ⟨siteX, siteY⟩
      apply Prod.ext <;>
        simp [Cell.sub, Cell.add, Cell.neg] <;> ring
    rw [desiredEq]
    exact relativeSiteDouble
  · exact equal

/-- Carrier and represented routed-variable-arm route points can coincide
only at their outer route endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (carrierLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier carrierLink)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.segmentWitness.routeWitness.metadata.source =
        .routedVariable site armIndex arm routedLink
          localClauseIndex)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (linkFirstEq :
      routedLink.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula)))
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have sourceMember :=
    second.segmentWitness.source_retainedComponentMember
  rw [secondSourceEq] at sourceMember
  have siteMember :
      site ∈ drawingVariableRouteSites formula :=
    sourceMember.1
  have centerEq :
      second.segmentWitness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2) := by
    rw [secondSourceEq]
    rfl
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  have siteTranslateEq :
      Cell.add occurrence.translate occurrence.edge.offset =
        site.2 :=
    congrArg Prod.snd occurrenceData.2
  have edgeMember :=
    occurrence.taggedEdge_mem formula occurrenceData.1
  have edgeLocal : occurrence.edge.span ≤ 1 :=
    isLocal occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have offsetNeighbor :
      IsNeighborTranslation occurrence.edge.offset :=
    PeriodicEdge.offset_neighbor_of_local
      occurrence.edge edgeLocal
  apply
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier_of_balanced_source_coordinate
      formula wellFormed degree isLocal clausesNonempty
      first second carrierLink firstComponentEq secondNotCarrier
      (Cell.add occurrence.translate
        (Cell.neg second.segmentWitness.sourceClauseAnchor))
  · intro adjustment adjustmentNeighbor
    rw [secondSourceEq]
    refine ⟨occurrence, occurrenceMember, linkFirstEq, ?_⟩
    simpa [Cell.add, add_assoc] using adjustmentNeighbor
  · have relativeSiteNeighbor :=
      first.carrier_liftedVertex_relative_neighbor_of_pointEquality
        formula wellFormed degree isLocal second
        carrierLink firstComponentEq secondNotCarrier
        (.variable site.1)
        (drawingVariableRouteSite_vertex_mem formula siteMember)
        site.2 centerEq equal
    have sumMember :=
      relativeSiteNeighbor.add_mem_doubleNeighborTranslations
        offsetNeighbor
    have desiredEq :
        Cell.sub
            (Cell.add
              (Cell.add carrierLink.first.translate
                (Cell.neg first.segmentWitness.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            (Cell.add occurrence.translate
              (Cell.neg second.segmentWitness.sourceClauseAnchor)) =
          Cell.add
            (Cell.sub
              (Cell.add carrierLink.first.translate
                (Cell.neg first.segmentWitness.sourceClauseAnchor))
              (Cell.add site.2
                (Cell.sub second.segmentWitness.physicalShift firstShift)))
            occurrence.edge.offset := by
      rw [second.segmentWitness.physicalShift_eq,
        ← siteTranslateEq]
      rcases firstShift with ⟨firstShiftX, firstShiftY⟩
      rcases secondShift with ⟨secondShiftX, secondShiftY⟩
      rcases first.segmentWitness.sourceClauseAnchor with
        ⟨firstAnchorX, firstAnchorY⟩
      rcases second.segmentWitness.sourceClauseAnchor with
        ⟨secondAnchorX, secondAnchorY⟩
      rcases occurrence.translate with
        ⟨occurrenceX, occurrenceY⟩
      rcases occurrence.edge.offset with
        ⟨offsetX, offsetY⟩
      apply Prod.ext <;>
        simp [Cell.sub, Cell.add, Cell.neg] <;>
        ring
    rw [desiredEq]
    exact sumMember
  · exact equal

/-- Carrier and route-bend route points can coincide only at their outer
route endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_bend
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier link)
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.segmentWitness.routeWitness.metadata.source =
        .bend routeBend localClauseIndex)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  let graph := formula.incidenceGraph
  let anchorShift :=
    Cell.neg first.segmentWitness.sourceClauseAnchor
  let sourceShift :=
    Cell.sub second.segmentWitness.physicalShift firstShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  have secondNotCarrier :
      ¬∃ secondLink,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have routeBendMember :
      routeBend ∈ (drawingRouteBends graph).dedup := by
    have sourceMember :=
      second.segmentWitness.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have centerEq :
      second.segmentWitness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some (routeBend.drawingPoint graph) := by
    rw [secondSourceEq]
    rfl
  have carrierContains :=
    first.anchorNormalizedCarrier_supportingSegment_contains_translatedMacrocellCenter_of_pointEquality
      formula wellFormed degree isLocal second
      link firstComponentEq secondNotCarrier
      (routeBend.drawingPoint graph) centerEq equal
  have incomingTerminalMember :=
    (drawingRouteBend_terminals_mem_drawingSegmentTerminals
      graph routeBendMember).1
  have incomingIndexedMember :
      routeBend.incomingTerminal.indexed ∈
        (drawing graph).indexedSegments :=
    (drawingSegmentTerminal_indexed_mem
      graph incomingTerminalMember).1
  have incomingAxisAligned :
      routeBend.incomingTerminal.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      routeBend.incomingTerminal.indexed incomingIndexedMember
  let translatedIncoming :=
    routeBend.incomingTerminal.periodTranslate sourceShift
  have targetPointEq :
      translatedIncoming.drawingPoint graph =
        Cell.add (routeBend.drawingPoint graph)
          ((drawing graph).periodTranslation sourceShift) := by
    simp only [translatedIncoming, SegmentTerminal.periodTranslate,
      RouteBend.incomingTerminal, SegmentTerminal.drawingPoint,
      GridSegment.translate]
    rw [periodTranslation_add]
    apply Prod.ext <;>
      simp [RouteBend.drawingPoint, Cell.add] <;>
      omega
  have translatedIncomingContains :
      (translatedIncoming.indexed.segment.translate
        ((drawing graph).periodTranslation
          translatedIncoming.translate)).Contains
        (translatedIncoming.drawingPoint graph) := by
    exact
      SegmentTerminal.segment_contains_drawingPoint_of_axisAligned
        graph translatedIncoming
        (by
          simpa [translatedIncoming,
            SegmentTerminal.periodTranslate] using
            incomingAxisAligned)
  rcases
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨firstLocalClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.segmentWitness.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember :=
      first.segmentWitness.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw graph := by
    simpa only [translatedLink, graph, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (first.segmentWitness.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal
          first.segmentWitness.metadata_retainedValid
          firstNonempty link firstLocalClauseIndex firstSourceEq)
  have carrierIndexedMember :
      translatedLink.first.indexed ∈
        (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph
      (retainedDrawingCompleteCarrierLinkRaw_endpoints_mem
        graph translatedLinkMember).1
  have endpointBounds :
      (drawing graph).SegmentEndpointsInExpandedSquare := by
    intro indexed indexedMember
    have bounds :=
      drawing_indexedSegment_endpoints_inExpandedDrawingSquare
        wellFormed degree isLocal indexedMember
    simpa [PeriodicGridDrawing.PositionInExpandedSquare,
      InExpandedDrawingSquare, drawing_gridSize] using bounds
  apply
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier_of_balanced_source_coordinate
      formula wellFormed degree isLocal clausesNonempty
      first second link firstComponentEq secondNotCarrier
      (Cell.add routeBend.translate
        (Cell.neg second.segmentWitness.sourceClauseAnchor))
  · intro adjustment adjustmentNeighbor
    rw [secondSourceEq]
    change
      IsNeighborTranslation
        (Cell.add routeBend.translate
          (Cell.add
            (Cell.neg second.segmentWitness.sourceClauseAnchor)
            adjustment))
    simpa [Cell.add, add_assoc] using adjustmentNeighbor
  · have relativeClose :
        Cell.sub translatedLink.first.translate
            translatedIncoming.translate ∈
          PeriodicGridDrawing.doubleNeighborTranslations := by
      exact
        PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
          endpointBounds carrierIndexedMember
          (by
            simpa [translatedIncoming,
              SegmentTerminal.periodTranslate] using
              incomingIndexedMember)
          (by
            rw [targetPointEq]
            simpa [graph, anchorShift, sourceShift, translatedLink,
              CarrierNode.supportingSegment] using carrierContains)
          translatedIncomingContains
    have desiredEq :
        Cell.sub
            (Cell.add
              (Cell.add link.first.translate
                (Cell.neg first.segmentWitness.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            (Cell.add routeBend.translate
              (Cell.neg second.segmentWitness.sourceClauseAnchor)) =
          Cell.sub translatedLink.first.translate
            translatedIncoming.translate := by
      have translatedLinkTranslateEq :
          translatedLink.first.translate =
            Cell.add link.first.translate anchorShift := by
        simp [translatedLink, carrierLinkPeriodTranslate_first,
          CarrierNode.translate_periodTranslate]
      rw [translatedLinkTranslateEq]
      simp only [translatedIncoming, SegmentTerminal.periodTranslate]
      simp only [sourceShift]
      rw [second.segmentWitness.physicalShift_eq]
      apply Prod.ext <;>
        simp [RouteBend.incomingTerminal, anchorShift,
          Cell.sub, Cell.add, Cell.neg] <;>
        ring
    rw [desiredEq]
    exact relativeClose
  · exact equal

/-- Carrier and crossover route points can coincide only at their outer
route endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_crossover
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier link)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.segmentWitness.routeWitness.metadata.source =
        .crossover crossing localClauseIndex)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  let graph := formula.incidenceGraph
  let anchorShift :=
    Cell.neg first.segmentWitness.sourceClauseAnchor
  let sourceShift :=
    Cell.sub second.segmentWitness.physicalShift firstShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  let translatedCrossing :=
    crossing.periodTranslate graph sourceShift
  have secondNotCarrier :
      ¬∃ secondLink,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have crossingMember :
      crossing ∈ orientedCrossingHalo graph := by
    have sourceMember :=
      second.segmentWitness.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have retainedCrossingMember :
      crossing ∈ retainedCrossings graph :=
    orientedCrossingHalo_subset_retainedCrossings
      wellFormed degree isLocal crossingMember
  have crossingSound :=
    retainedCrossings_sound graph retainedCrossingMember
  have centerEq :
      second.segmentWitness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some crossing.point := by
    rw [secondSourceEq]
    rfl
  have carrierContains :=
    first.anchorNormalizedCarrier_supportingSegment_contains_translatedMacrocellCenter_of_pointEquality
      formula wellFormed degree isLocal second
      link firstComponentEq secondNotCarrier
      crossing.point centerEq equal
  have firstInteriorContains :
      (translatedCrossing.firstSegment graph).InteriorContains
        translatedCrossing.point := by
    rw [CrossingRecord.firstSegment_periodTranslate]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (crossing.firstSegment graph)
        ((drawing graph).periodTranslation sourceShift)
        crossing.point).mpr crossingSound.2.2.1
  have secondInteriorContains :
      (translatedCrossing.secondSegment graph).InteriorContains
        translatedCrossing.point := by
    rw [CrossingRecord.secondSegment_periodTranslate]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (crossing.secondSegment graph)
        ((drawing graph).periodTranslation sourceShift)
        crossing.point).mpr crossingSound.2.2.2.1
  rcases
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨firstLocalClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.segmentWitness.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember :=
      first.segmentWitness.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have secondNonempty :
      second.segmentWitness.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember :=
      second.segmentWitness.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw graph := by
    simpa only [translatedLink, graph, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (first.segmentWitness.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal
          first.segmentWitness.metadata_retainedValid
          firstNonempty link firstLocalClauseIndex firstSourceEq)
  have carrierIndexedMember :
      translatedLink.first.indexed ∈
        (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph
      (retainedDrawingCompleteCarrierLinkRaw_endpoints_mem
        graph translatedLinkMember).1
  have endpointBounds :
      (drawing graph).SegmentEndpointsInExpandedSquare := by
    intro indexed indexedMember
    have bounds :=
      drawing_indexedSegment_endpoints_inExpandedDrawingSquare
        wellFormed degree isLocal indexedMember
    simpa [PeriodicGridDrawing.PositionInExpandedSquare,
      InExpandedDrawingSquare, drawing_gridSize] using bounds
  have normalizedCondition :
      second.segmentWitness.routeWitness.metadata.source.RetainedOrbitCondition
        formula
        (Cell.neg second.segmentWitness.sourceClauseAnchor) := by
    simpa only [
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (second.segmentWitness.routeWitness.metadata
        |>.noncarrier_anchorNormalize_retainedOrbitCondition
          wellFormed degree isLocal
          second.segmentWitness.metadata_retainedValid
          secondNonempty secondNotCarrier)
  have normalizedNeighbors :
      IsNeighborTranslation
          (Cell.add crossing.firstTranslate
            (Cell.neg second.segmentWitness.sourceClauseAnchor)) ∧
        IsNeighborTranslation
          (Cell.add crossing.secondTranslate
            (Cell.neg second.segmentWitness.sourceClauseAnchor)) := by
    rw [secondSourceEq] at normalizedCondition
    exact normalizedCondition
  have crossingBasesClose :
      Cell.sub
          (Cell.add crossing.firstTranslate
            (Cell.neg second.segmentWitness.sourceClauseAnchor))
          (Cell.add crossing.secondTranslate
            (Cell.neg second.segmentWitness.sourceClauseAnchor)) ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      normalizedNeighbors.1.sub_mem_doubleNeighborTranslations
        normalizedNeighbors.2
  have carrierContainsTranslated :
      (translatedLink.first.indexed.segment.translate
        ((drawing graph).periodTranslation
          translatedLink.first.translate)).Contains
        translatedCrossing.point := by
    simpa [translatedCrossing, CrossingRecord.periodTranslate,
      graph, anchorShift, sourceShift, translatedLink,
      CarrierNode.supportingSegment] using carrierContains
  have firstRelativeClose :
      Cell.sub translatedLink.first.translate
          translatedCrossing.firstTranslate ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
        endpointBounds carrierIndexedMember
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate] using crossingSound.1)
        carrierContainsTranslated
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate,
            CrossingRecord.firstSegment] using
            GridSegment.contains_of_interiorContains
              firstInteriorContains)
  have secondRelativeClose :
      Cell.sub translatedLink.first.translate
          translatedCrossing.secondTranslate ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
        endpointBounds carrierIndexedMember
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate] using crossingSound.2.1)
        carrierContainsTranslated
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate,
            CrossingRecord.secondSegment] using
            GridSegment.contains_of_interiorContains
              secondInteriorContains)
  have desiredEq (crossingTranslate : Cell) :
      Cell.sub
          (Cell.add
            (Cell.add link.first.translate
              (Cell.neg first.segmentWitness.sourceClauseAnchor))
            (Cell.sub firstShift secondShift))
          (Cell.add crossingTranslate
            (Cell.neg second.segmentWitness.sourceClauseAnchor)) =
        Cell.sub translatedLink.first.translate
          (Cell.add crossingTranslate sourceShift) := by
    have translatedLinkTranslateEq :
        translatedLink.first.translate =
          Cell.add link.first.translate anchorShift := by
      simp [translatedLink, carrierLinkPeriodTranslate_first,
        CarrierNode.translate_periodTranslate]
    rw [translatedLinkTranslateEq]
    simp only [sourceShift]
    rw [second.segmentWitness.physicalShift_eq]
    apply Prod.ext <;>
      simp [anchorShift, Cell.sub, Cell.add, Cell.neg] <;>
      ring
  apply
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier_of_balanced_two_source_coordinates
      formula wellFormed degree isLocal clausesNonempty
      first second link firstComponentEq secondNotCarrier
      (Cell.add crossing.firstTranslate
        (Cell.neg second.segmentWitness.sourceClauseAnchor))
      (Cell.add crossing.secondTranslate
        (Cell.neg second.segmentWitness.sourceClauseAnchor))
      crossingBasesClose
  · intro adjustment firstNeighbor secondNeighbor
    rw [secondSourceEq]
    constructor
    · simpa [Cell.add, add_assoc] using firstNeighbor
    · simpa [Cell.add, add_assoc] using secondNeighbor
  · rw [desiredEq crossing.firstTranslate]
    simpa [translatedCrossing,
      CrossingRecord.periodTranslate] using firstRelativeClose
  · rw [desiredEq crossing.secondTranslate]
    simpa [translatedCrossing,
      CrossingRecord.periodTranslate] using secondRelativeClose
  · exact equal

/-- A final carrier route-point occurrence and any final noncarrier
route-point occurrence can coincide only at outer endpoints. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier secondLink)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  generalize sourceEq :
    second.segmentWitness.routeWitness.metadata.source = source
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_crossover
          formula wellFormed degree isLocal clausesNonempty
          first second link firstComponentEq
          crossing localClauseIndex sourceEq equal
  | carrier secondLink localClauseIndex =>
      exact False.elim
        (secondNotCarrier
          ⟨secondLink, by
            rw [sourceEq]
            rfl⟩)
  | bend routeBend localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_bend
          formula wellFormed degree isLocal clausesNonempty
          first second link firstComponentEq
          routeBend localClauseIndex sourceEq equal
  | routedClause site =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_routedClause
          formula wellFormed degree isLocal clausesNonempty
          first second link firstComponentEq site sourceEq equal
  | routedVariable site armIndex arm routedLink localClauseIndex =>
      have sourceMember :=
        second.segmentWitness.source_retainedComponentMember
      rw [sourceEq] at sourceMember
      rcases
          exists_routeOccurrence_of_routedVariableLinkMember
            formula site sourceMember.2.1 with
        ⟨occurrence, occurrenceMember, linkFirstEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_routedVariable
          formula wellFormed degree isLocal clausesNonempty
          first second link firstComponentEq
          site armIndex arm routedLink localClauseIndex sourceEq
          occurrence occurrenceMember linkFirstEq equal

/-- The reverse noncarrier--carrier ordering follows by symmetry. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_noncarrier_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (firstNotCarrier :
      ¬∃ firstLink,
        first.segmentWitness.routeWitness.metadata.source.component =
          .carrier firstLink)
    (secondLink : EqualityLink CarrierNode)
    (secondComponentEq :
      second.segmentWitness.routeWitness.metadata.source.component =
        .carrier secondLink)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  have endpoints :=
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier
      formula wellFormed degree isLocal clausesNonempty
      second first secondLink secondComponentEq firstNotCarrier equal.symm
  exact endpoints.symm

end PeriodicOrthocrossing
end LeanTrominoes
