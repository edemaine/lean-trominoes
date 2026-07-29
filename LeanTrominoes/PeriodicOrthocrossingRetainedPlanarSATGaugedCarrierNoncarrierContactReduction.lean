import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierPeriodicSeparation

/-!
# Reducing carrier--noncarrier contact to finite-halo closure

A selected carrier source is already a neighboring raw retained link.  To
compare it with an arbitrary final noncarrier occurrence, keep that carrier
source fixed and translate the noncarrier source by the difference of their
physical shifts.  Both resulting finite routes then use the carrier's physical
shift as their common external translate.

Consequently, periodic carrier--noncarrier separation is reduced to one
geometric closure fact: if the two final segments met, the translated
noncarrier source would still belong to the retained finite halo.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Undo the two quotient gauges in a final contact, then cancel the carrier's
common physical translate.  The result is a contact between the carrier's
original finite segment and the noncarrier segment translated by exactly the
source shift used by the halo-closure reduction below. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.alignedPhysicalSegments_interiorsMeet_of_final
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
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    GridSegment.InteriorsMeet
      first.physicalSegment
      (second.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub second.physicalShift first.physicalShift))) := by
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq,
    secondRepresentative.segmentEq] at meet
  change
    GridSegment.InteriorsMeet
      (first.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation first.physicalShift))
      (second.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation second.physicalShift)) at meet
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let sourceShift :=
    Cell.sub second.physicalShift first.physicalShift
  have secondAlignedEq :
      (second.physicalSegment.translate
        (placement.translation sourceShift)).translate
          (placement.translation first.physicalShift) =
        second.physicalSegment.translate
          (placement.translation second.physicalShift) := by
    exact segment_translate_placement_sub_add
      placement second.physicalSegment
      second.physicalShift first.physicalShift
  rw [← secondAlignedEq] at meet
  have aligned :
      GridSegment.InteriorsMeet
        first.physicalSegment
        (second.physicalSegment.translate
          (placement.translation sourceShift)) :=
    (GridSegment.interiorsMeet_translate_both_iff
      first.physicalSegment
      (second.physicalSegment.translate
        (placement.translation sourceShift))
      (placement.translation first.physicalShift)).mp meet
  have offsetEq :
      placement.translation sourceShift =
        carrierMacroPeriodTranslation
          formula.incidenceGraph sourceShift :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula sourceShift
  simpa only [sourceShift, offsetEq] using aligned

/-- A retained carrier metadata source supplies the raw-link membership and
neighboring first occurrence required by the finite carrier separation API. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.carrier_source_raw_and_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.routeWitness.metadata.source.component = .carrier link) :
    link ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph ∧
      IsNeighborTranslation link.first.translate := by
  rcases
      witness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have sourceMember :=
    witness.source_retainedComponentMember
  rw [sourceEq] at sourceMember
  have selectedMember :
      link ∈
        retainedDrawingCompleteCarrierLinks formula.incidenceGraph := by
    simpa only [
      DrawingPlanarSATClauseSource.RetainedComponentMember] using
      sourceMember
  exact
    ⟨((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph link).mp selectedMember).1,
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        formula.incidenceGraph selectedMember⟩

/-- If a hypothetical final carrier--noncarrier contact keeps the physically
aligned noncarrier source in the retained halo, finite raw-carrier planarity
already gives a contradiction. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_contact_retained
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (contactRetained :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        (second.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub second.physicalShift first.physicalShift)
            |>.RetainedComponentMember formula)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  intro meet
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have commonShiftEq :
      Cell.sub first.physicalShift (0, 0) =
        Cell.sub second.physicalShift
          (Cell.sub second.physicalShift first.physicalShift) := by
    rcases first.physicalShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    simp only [Cell.sub, Prod.mk.injEq]
    constructor <;> ring
  have translatedLinkEq :
      carrierLinkPeriodTranslate formula.incidenceGraph link (0, 0) =
        link := by
    rcases link with ⟨firstNode, secondNode, positions⟩
    rcases firstNode with firstBoundary | firstTerminal <;>
      rcases secondNode with secondBoundary | secondTerminal <;>
      simp [carrierLinkPeriodTranslate,
        CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        CrossingBoundary.periodTranslate,
        CrossingRecord.periodTranslate,
        EqualityPositions.periodTranslate,
        carrierMacroPeriodTranslation,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale]
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw
      formula wellFormed degree isLocal first second
      (0, 0) (Cell.sub second.physicalShift first.physicalShift)
      commonShiftEq link firstComponentEq secondNotCarrier
      (by simpa only [translatedLinkEq] using carrierData.1)
      (by simpa using carrierData.2)
      (contactRetained meet))
      meet

/-- Equivalently, any hypothetical contact would force the physically aligned
noncarrier source outside the retained halo.  Later family-specific geometry
will contradict this escape conclusion. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_translated_noncarrier_not_retained_of_carrier_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    ¬((second.routeWitness.metadata.source.periodTranslate formula
        (Cell.sub second.physicalShift first.physicalShift))
          |>.RetainedComponentMember formula) := by
  intro translatedMember
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_contact_retained
      formula wellFormed degree isLocal first second link
      firstComponentEq secondNotCarrier
      (fun _ => translatedMember))
      meet

end PeriodicOrthocrossing
end LeanTrominoes
