import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATRawCarrierTranslationSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation

/-!
# Final carrier--noncarrier separation from raw retention

The generic final-occurrence bridge compares the first finite source after
translation by the difference of the two physical shifts.  For a carrier
source, this file reduces final periodic separation to the two geometric
facts needed by the raw retained carrier API: membership of that translated
link in the raw window and neighboring placement of its first occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A final carrier occurrence avoids a final noncarrier occurrence once
the physically aligned carrier link is known to be a neighboring raw
retained link. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_aligned_raw
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
    (alignedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link
          (Cell.sub first.physicalShift second.physicalShift) ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (alignedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph link
          (Cell.sub first.physicalShift
            second.physicalShift)).first.translate)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have routeAvoid :=
    first.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_raw_carrier
        wellFormed degree isLocal second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        reindexShift link localClauseIndex firstSourceEq
        (by simpa only [reindexShift] using alignedLinkMember)
        (by simpa only [reindexShift] using alignedFirstNeighbor)
        first.routeWitness.literalMember
        second.routeWitness.literalMember secondNotCarrier
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_periodTranslate_localRoutesAvoidEachOther
      formula first second
  simpa only [reindexShift] using routeAvoid

end PeriodicOrthocrossing
end LeanTrominoes
