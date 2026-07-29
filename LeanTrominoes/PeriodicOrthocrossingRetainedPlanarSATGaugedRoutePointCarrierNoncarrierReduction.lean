import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierContactReduction
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointLocalRouteAvoidance

/-!
# Carrier--noncarrier route-point contact reduction

The continuous carrier--noncarrier proof reduces a contact to overlap
between a raw carrier rectangle and a translated noncarrier macrocell.
Listed route-point equality supplies the same overlap directly.  This file
records the pointwise normalization and bounding lemmas needed to reuse the
existing raw-carrier separation API.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Translating a point by a source shift and then by the remaining
physical shift equals translating it directly by the physical shift. -/
private theorem routePoint_add_placement_add_sub
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (point : Cell)
    (physicalShift sourceShift : Cell) :
    Cell.add
        (Cell.add point (placement.translation sourceShift))
        (placement.translation
          (Cell.sub physicalShift sourceShift)) =
      Cell.add point (placement.translation physicalShift) := by
  rcases point with ⟨pointX, pointY⟩
  rcases physicalShift with ⟨physicalX, physicalY⟩
  rcases sourceShift with ⟨sourceX, sourceY⟩
  simp only [PeriodicVariablePlacement.translation,
    Cell.scale, Cell.add, Cell.sub, Prod.mk.injEq]
  constructor <;> ring

/-- Cancel the carrier occurrence's final translate in an equality of final
route points.  The noncarrier physical point is left translated by its
physical shift minus the carrier's final shift. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.anchorAlignedPhysicalPoint_eq_of_final
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    (_first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.point =
      Cell.add
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub second.segmentWitness.physicalShift firstShift))
        second.physicalPoint := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let sourceShift :=
    Cell.sub second.segmentWitness.physicalShift firstShift
  have liftedEq :
      Cell.add firstIndexed.point
          (placement.translation firstShift) =
        Cell.add second.physicalPoint
          (placement.translation second.segmentWitness.physicalShift) := by
    simpa only [
      retainedDeduplicatedGaugedWrappedDrawing_periodTranslation_eq_placement]
      using equal.trans second.pointEq
  have alignedEq :
      Cell.add
          (Cell.add second.physicalPoint
            (placement.translation sourceShift))
          (placement.translation firstShift) =
        Cell.add second.physicalPoint
          (placement.translation second.segmentWitness.physicalShift) := by
    simpa [sourceShift, Cell.sub] using
      routePoint_add_placement_add_sub placement second.physicalPoint
        second.segmentWitness.physicalShift sourceShift
  have pointEq :
      firstIndexed.point =
        Cell.add second.physicalPoint
          (placement.translation sourceShift) := by
    exact
      Cell.add_right_injective
        (placement.translation firstShift)
        (liftedEq.trans alignedEq.symm)
  have offsetEq :
      placement.translation sourceShift =
        carrierMacroPeriodTranslation
          formula.incidenceGraph sourceShift :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula sourceShift
  simpa only [sourceShift, offsetEq, Cell.add, add_comm] using pointEq

/-- Translating a noncarrier route point translates its macrocell
certificate by the same source period shift. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.translatedPhysicalPoint_in_macrocell
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift)
    (notCarrier :
      ¬∃ link,
        witness.segmentWitness.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link)
    (center : Cell)
    (centerEq :
      witness.segmentWitness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some center)
    (sourceShift : Cell) :
    InPlanarSATMacrocell
      (Cell.add center
        ((drawing formula.incidenceGraph).periodTranslation sourceShift))
      (Cell.add
        (carrierMacroPeriodTranslation formula.incidenceGraph sourceShift)
        witness.physicalPoint) := by
  have valid :=
    witness.segmentWitness.routeWitness.metadata
      |>.valid_of_retainedValid_of_not_carrier
        witness.segmentWitness.metadata_retainedValid notCarrier
  have bounded :=
    witness.segmentWitness.routeWitness.metadata
      |>.localRoutePoints_inPlanarSATMacrocell
        wellFormed degree isLocal valid center centerEq
        witness.segmentWitness.routeWitness.literalMember
        (List.fst_mem_of_mem_zipIdx witness.physicalPoint_mem_sourceRoute)
  have translated :=
    inPlanarSATMacrocell_translate
      (shift := sourceShift)
      (drawingGridSize formula.incidenceGraph) bounded
  simpa [carrierMacroPeriodTranslation,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale, planarMacroScale,
    add_comm, mul_assoc, mul_comm, mul_left_comm] using translated

/-- An anchor-normalized carrier route point lies in the explicit
rectangle of the correspondingly translated raw carrier link. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.indexedPoint_in_anchorNormalizedCarrierRectangle
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.segmentWitness.routeWitness.metadata.source.component =
        .carrier link) :
    let anchorShift :=
      Cell.neg witness.segmentWitness.sourceClauseAnchor
    let translatedLink :=
      carrierLinkPeriodTranslate formula.incidenceGraph link anchorShift
    InClosedGridRectangle
      (drawingCompleteCarrierLinkRectangleLower
        formula.incidenceGraph translatedLink)
      (drawingCompleteCarrierLinkRectangleUpper
        formula.incidenceGraph translatedLink)
      indexed.point := by
  rcases
      witness.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have nonempty :
      witness.segmentWitness.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember :=
      witness.segmentWitness.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  let anchorShift :=
    Cell.neg witness.segmentWitness.sourceClauseAnchor
  let translatedLink :=
    carrierLinkPeriodTranslate formula.incidenceGraph link anchorShift
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph := by
    simpa only [translatedLink, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (witness.segmentWitness.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal
          witness.segmentWitness.metadata_retainedValid
          nonempty link localClauseIndex sourceEq)
  have sourceLocalClauseMember :
      (witness.segmentWitness.routeWitness.metadata.clause,
          witness.segmentWitness.routeWitness.metadata.source.localClauseIndex) ∈
        (witness.segmentWitness.routeWitness.metadata.source.clauseFormula
          formula).zipIdx :=
    (witness.segmentWitness.routeWitness.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp
          witness.segmentWitness.metadata_retainedValid |>.2
  rcases
      witness.segmentWitness.routeWitness.metadata.source
        |>.exists_periodTranslatedClauseLiteral
          formula anchorShift
          witness.segmentWitness.routeWitness.metadata.clause
          sourceLocalClauseMember
          witness.segmentWitness.routeWitness.literal
          witness.segmentWitness.taggedLiteral.2
          witness.segmentWitness.routeWitness.literalMember with
    ⟨translatedClause, translatedLiteral,
      translatedClauseMember, translatedLiteralMember⟩
  have translatedSourceEq :
      witness.segmentWitness.routeWitness.metadata.source.periodTranslate
          formula anchorShift =
        .carrier translatedLink localClauseIndex := by
    rw [sourceEq]
    rfl
  have sourceLocalClauseIndexEq :
      witness.segmentWitness.routeWitness.metadata.source.localClauseIndex =
        localClauseIndex := by
    rw [sourceEq]
    rfl
  have translatedFormulaClauseMember :
      (translatedClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) translatedLink).zipIdx := by
    rw [translatedSourceEq] at translatedClauseMember
    simpa [DrawingPlanarSATClauseSource.localClauseIndex,
      DrawingPlanarSATClauseSource.clauseFormula] using
        translatedClauseMember
  have translatedDrawingClauseMember :
      (translatedClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula translatedLink).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal translatedLinkMember]
    exact translatedFormulaClauseMember
  have translatedPointMember :=
    witness.physicalPoint_periodTranslate_mem_sourceRoute anchorShift
  rw [translatedSourceEq, sourceLocalClauseIndexEq]
    at translatedPointMember
  have bounded :=
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded_of_raw
      wellFormed degree isLocal translatedLinkMember
  have pointBounded :=
    bounded.of_members translatedDrawingClauseMember
      translatedLiteralMember
      (List.fst_mem_of_mem_zipIdx translatedPointMember)
  have pointEq :
      indexed.point =
        Cell.add
          (carrierMacroPeriodTranslation formula.incidenceGraph anchorShift)
          witness.physicalPoint := by
    have translatedFirstPointEq :
        Cell.add
            (carrierMacroPeriodTranslation formula.incidenceGraph anchorShift)
            witness.physicalPoint =
          indexed.point := by
      have lifted :=
        witness.anchorAlignedPhysicalPoint_eq_of_final witness rfl
      simpa [anchorShift,
        FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
        Cell.sub, Cell.neg] using lifted.symm
    exact translatedFirstPointEq.symm
  simpa only [anchorShift, translatedLink, pointEq] using pointBounded

/-- Equality of a carrier and noncarrier route point forces the
anchor-normalized carrier corridor to overlap the translated noncarrier
macrocell.  Consequently the raw carrier's supporting segment passes
through that macrocell's center. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.anchorNormalizedCarrier_supportingSegment_contains_translatedMacrocellCenter_of_pointEquality
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (center : Cell)
    (centerEq :
      second.segmentWitness.routeWitness.metadata.source.component.macrocellCenter
          formula =
          some center)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    let graph := formula.incidenceGraph
    let anchorShift :=
      Cell.neg first.segmentWitness.sourceClauseAnchor
    let sourceShift :=
      Cell.sub second.segmentWitness.physicalShift firstShift
    let translatedLink :=
      carrierLinkPeriodTranslate graph link anchorShift
    (translatedLink.first.supportingSegment graph).Contains
      (Cell.add center
        ((drawing graph).periodTranslation sourceShift)) := by
  let graph := formula.incidenceGraph
  let anchorShift :=
    Cell.neg first.segmentWitness.sourceClauseAnchor
  let sourceShift :=
    Cell.sub second.segmentWitness.physicalShift firstShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  rcases
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
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
          firstNonempty link localClauseIndex firstSourceEq)
  have firstBounded :=
    first.indexedPoint_in_anchorNormalizedCarrierRectangle
      wellFormed degree isLocal link firstComponentEq
  have secondBounded :=
    second.translatedPhysicalPoint_in_macrocell
      wellFormed degree isLocal secondNotCarrier
      center centerEq sourceShift
  have aligned :=
    first.anchorAlignedPhysicalPoint_eq_of_final second equal
  have notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          graph translatedLink)
        (drawingCompleteCarrierLinkRectangleUpper
          graph translatedLink)
        (planarSATMacrocellRouteLower
          (Cell.add center
            ((drawing graph).periodTranslation sourceShift)))
        (planarSATMacrocellRouteUpper
          (Cell.add center
            ((drawing graph).periodTranslation sourceShift))) := by
    intro separated
    exact
      (ne_of_inClosedGridRectangles_of_separated
        firstBounded secondBounded separated)
        (by simpa only [graph, sourceShift] using aligned)
  exact
    retainedDrawingCompleteCarrierLinkRaw_supportingSegment_contains_of_macrocell_overlap
      wellFormed degree isLocal translatedLinkMember
      (Cell.add center
        ((drawing graph).periodTranslation sourceShift))
      notSeparated

/-- The common-shift raw-carrier bridge transfers full finite local-route
avoidance to endpoint-only contact of final route points. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
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
    (firstSourceShift secondSourceShift : Cell)
    (commonShiftEq :
      Cell.sub first.segmentWitness.physicalShift firstSourceShift =
        Cell.sub second.segmentWitness.physicalShift secondSourceShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.segmentWitness.routeWitness.metadata.source.component =
        .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.segmentWitness.routeWitness.metadata.source.component =
          .carrier secondLink)
    (translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link
          firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph link
          firstSourceShift).first.translate))
    (translatedSecondCondition :
      second.segmentWitness.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift)
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  rcases
      first.segmentWitness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have routeAvoid :=
    first.segmentWitness.routeWitness.metadata
      |>.two_periodTranslate_localRoutes_avoidEachOther_of_raw_carrier_retainedOrbitCondition
        wellFormed degree isLocal
        second.segmentWitness.routeWitness.metadata
        first.segmentWitness.metadata_retainedValid
        second.segmentWitness.metadata_retainedValid
        firstSourceShift secondSourceShift
        link localClauseIndex firstSourceEq
        translatedLinkMember translatedFirstNeighbor
        translatedSecondCondition
        first.segmentWitness.routeWitness.literalMember
        second.segmentWitness.routeWitness.literalMember
        secondNotCarrier
  exact
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_two_periodTranslate_localRoutesAvoidEachOther
      formula wellFormed degree isLocal clausesNonempty
      first second firstSourceShift secondSourceShift
      commonShiftEq routeAvoid equal

end PeriodicOrthocrossing
end LeanTrominoes
