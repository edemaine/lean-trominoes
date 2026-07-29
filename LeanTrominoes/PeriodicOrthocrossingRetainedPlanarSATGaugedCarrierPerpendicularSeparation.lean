import LeanTrominoes.PeriodicOrthocrossingRetainedTranslatedPerpendicularCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierParallelSeparation

/-!
# Periodic separation of perpendicular carrier components

After aligning two final carrier occurrences by their physical gauge shifts,
perpendicular source carriers have disjoint lens rectangles and hence
disjoint continuous segment interiors.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Metadata routes from aligned perpendicular carrier components avoid one
another. -/
theorem
    DrawingPlanarSATClauseMetadata.periodTranslate_localRoutes_avoidEachOther_of_carrier_perpendicular
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (shift : Cell)
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstClauseIndex secondClauseIndex : Nat)
    (firstSourceEq :
      first.source = .carrier firstLink firstClauseIndex)
    (secondSourceEq :
      second.source = .carrier secondLink secondClauseIndex)
    (perpendicular :
      CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift)
        secondLink)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula shift).incidenceDrawing
          formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  have firstValid' := firstValid
  have secondValid' := secondValid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid
    at firstValid' secondValid'
  rw [firstSourceEq] at firstValid'
  rw [secondSourceEq] at secondValid'
  have firstClauseMember :
      (first.clause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal firstValid'.1]
    exact firstValid'.2
  have secondClauseMember :
      (second.clause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal secondValid'.1]
    exact secondValid'.2
  have routeAvoid :=
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_periodTranslate_of_perpendicular
      wellFormed degree isLocal firstValid'.1 secondValid'.1 shift
      perpendicular firstClauseMember firstLiteralMember
      secondClauseMember secondLiteralMember
  simpa [firstSourceEq, secondSourceEq,
    DrawingPlanarSATClauseSource.periodTranslate,
    DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using routeAvoid

/-- Final carrier occurrences on perpendicular aligned source axes have
disjoint continuous segment interiors. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carriers_perpendicular
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
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier firstLink)
    (secondComponentEq :
      second.routeWitness.metadata.source.component = .carrier secondLink)
    (perpendicular :
      CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
          (Cell.sub first.physicalShift second.physicalShift))
        secondLink) :
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
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  have routeAvoid :=
    first.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_perpendicular
        wellFormed degree isLocal second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        reindexShift firstLink secondLink
        firstClauseIndex secondClauseIndex
        firstSourceEq secondSourceEq
        (by simpa only [reindexShift] using perpendicular)
        first.routeWitness.literalMember
        second.routeWitness.literalMember
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_periodTranslate_localRoutesAvoidEachOther
      formula first second
  simpa only [reindexShift] using routeAvoid

/-- Final carrier occurrences on perpendicular aligned source axes also
satisfy asymmetric interior-versus-closed avoidance. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carriers_perpendicular
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
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier firstLink)
    (secondComponentEq :
      second.routeWitness.metadata.source.component = .carrier secondLink)
    (perpendicular :
      CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
          (Cell.sub first.physicalShift second.physicalShift))
        secondLink)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  have routeAvoid :=
    first.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_perpendicular
        wellFormed degree isLocal second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        reindexShift firstLink secondLink
        firstClauseIndex secondClauseIndex
        firstSourceEq secondSourceEq
        (by simpa only [reindexShift] using perpendicular)
        first.routeWitness.literalMember
        second.routeWitness.literalMember
  apply
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_periodTranslate_localRoutesAvoidEachOther
      formula first second
  · simpa only [reindexShift] using routeAvoid
  · exact firstContains

end PeriodicOrthocrossing
end LeanTrominoes
