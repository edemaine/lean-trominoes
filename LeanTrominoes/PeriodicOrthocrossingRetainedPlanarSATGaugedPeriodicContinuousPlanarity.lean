import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierContactReduction
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierParallelSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierPerpendicularSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation

/-!
# Continuous planarity of the final gauged periodic drawing

The component-specific separation theorems assemble into global disjointness
of the relative interiors of all distinct segment occurrences in the final
periodic lift.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A final carrier occurrence has disjoint interior from every final
noncarrier occurrence. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
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
          .carrier secondLink) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  generalize sourceEq :
    second.routeWitness.metadata.source = source
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_crossover
          formula wellFormed degree isLocal first second
          link firstComponentEq crossing localClauseIndex sourceEq
  | carrier secondLink localClauseIndex =>
      exact False.elim
        (secondNotCarrier
          ⟨secondLink, by
            rw [sourceEq]
            rfl⟩)
  | bend routeBend localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_bend
          formula wellFormed degree isLocal first second
          link firstComponentEq routeBend localClauseIndex sourceEq
  | routedClause site =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedClause
          formula wellFormed degree isLocal clausesNonempty
          firstMember first second link firstComponentEq site sourceEq
  | routedVariable site armIndex arm routedLink localClauseIndex =>
      have sourceMember := second.source_retainedComponentMember
      rw [sourceEq] at sourceMember
      rcases
          exists_routeOccurrence_of_routedVariableLinkMember
            formula site sourceMember.2.1 with
        ⟨occurrence, occurrenceMember, linkFirstEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedVariable
          formula wellFormed degree isLocal first second
          link firstComponentEq
          site armIndex arm routedLink localClauseIndex sourceEq
          occurrence occurrenceMember linkFirstEq

/-- A final carrier occurrence's relative interior avoids every closed final
noncarrier occurrence. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift point : Cell}
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
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  generalize sourceEq :
    second.routeWitness.metadata.source = source
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_crossover
          formula wellFormed degree isLocal first second
          link firstComponentEq crossing localClauseIndex sourceEq
          firstContains
  | carrier secondLink localClauseIndex =>
      exact False.elim
        (secondNotCarrier
          ⟨secondLink, by
            rw [sourceEq]
            rfl⟩)
  | bend routeBend localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_bend
          formula wellFormed degree isLocal first second
          link firstComponentEq routeBend localClauseIndex sourceEq
          firstContains
  | routedClause site =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_routedClause
          formula wellFormed degree isLocal clausesNonempty
          firstMember first second link firstComponentEq site sourceEq
          firstContains
  | routedVariable site armIndex arm routedLink localClauseIndex =>
      have sourceMember := second.source_retainedComponentMember
      rw [sourceEq] at sourceMember
      rcases
          exists_routeOccurrence_of_routedVariableLinkMember
            formula site sourceMember.2.1 with
        ⟨occurrence, occurrenceMember, linkFirstEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_routedVariable
          formula wellFormed degree isLocal first second
          link firstComponentEq
          site armIndex arm routedLink localClauseIndex sourceEq
          occurrence occurrenceMember linkFirstEq firstContains

/-- Every final noncarrier occurrence's relative interior avoids each closed
final carrier occurrence. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarrier_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift point : Cell}
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
    (secondContains :
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).InteriorContains point) :
    ¬(firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).Contains point := by
  generalize sourceEq :
    second.routeWitness.metadata.source = source
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_crossover_carrier
          formula wellFormed degree isLocal first second
          link firstComponentEq crossing localClauseIndex sourceEq
          secondContains
  | carrier secondLink localClauseIndex =>
      exact False.elim
        (secondNotCarrier
          ⟨secondLink, by
            rw [sourceEq]
            rfl⟩)
  | bend routeBend localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_bend_carrier
          formula wellFormed degree isLocal first second
          link firstComponentEq routeBend localClauseIndex sourceEq
          secondContains
  | routedClause site =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_routedClause_carrier
          formula wellFormed degree isLocal clausesNonempty
          firstMember first second link firstComponentEq site sourceEq
          secondContains
  | routedVariable site armIndex arm routedLink localClauseIndex =>
      have sourceMember := second.source_retainedComponentMember
      rw [sourceEq] at sourceMember
      rcases
          exists_routeOccurrence_of_routedVariableLinkMember
            formula site sourceMember.2.1 with
        ⟨occurrence, occurrenceMember, linkFirstEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_routedVariable_carrier
          formula wellFormed degree isLocal first second
          link firstComponentEq
          site armIndex arm routedLink localClauseIndex sourceEq
          occurrence occurrenceMember linkFirstEq secondContains

/-- Every pair of distinct final segment occurrences has disjoint relative
interiors. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (secondMember :
      secondIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  by_cases firstCarrier :
      ∃ firstLink,
        first.routeWitness.metadata.source.component =
          .carrier firstLink
  · rcases firstCarrier with ⟨firstLink, firstComponentEq⟩
    by_cases secondCarrier :
        ∃ secondLink,
          second.routeWitness.metadata.source.component =
            .carrier secondLink
    · rcases secondCarrier with ⟨secondLink, secondComponentEq⟩
      let translatedFirstLink :=
        carrierLinkPeriodTranslate formula.incidenceGraph firstLink
          (Cell.sub first.physicalShift second.physicalShift)
      by_cases perpendicular :
          CarrierLinksPerpendicular translatedFirstLink secondLink
      · exact
          retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carriers_perpendicular
            formula wellFormed degree isLocal first second
            firstLink secondLink firstComponentEq secondComponentEq
            (by simpa only [translatedFirstLink] using perpendicular)
      · by_cases samePhysicalKey :
          translatedFirstLink.first.carrierKey =
            secondLink.first.carrierKey
        · exact
            retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carriers_same_physical_key
              formula wellFormed degree isLocal clausesNonempty
              first second firstLink secondLink
              firstComponentEq secondComponentEq
              (by simpa only [translatedFirstLink] using samePhysicalKey)
              different
        · exact
            retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carriers_parallel_key_ne
              formula wellFormed degree isLocal first second
              firstLink secondLink firstComponentEq secondComponentEq
              (by simpa only [translatedFirstLink] using perpendicular)
              (by simpa only [translatedFirstLink] using samePhysicalKey)
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier
          formula wellFormed degree isLocal clausesNonempty
          firstMember first second firstLink firstComponentEq secondCarrier
  · by_cases secondCarrier :
      ∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink
    · rcases secondCarrier with ⟨secondLink, secondComponentEq⟩
      intro meet
      exact
        (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier
          formula wellFormed degree isLocal clausesNonempty
          secondMember second first secondLink secondComponentEq firstCarrier)
          ((GridSegment.interiorsMeet_comm _ _).mpr meet)
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_noncarriers
          formula wellFormed degree isLocal clausesNonempty
          first second firstCarrier secondCarrier different

/-- The final gauged periodic incidence drawing has globally disjoint
relative interiors for all distinct segment occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesHaveDisjointInteriors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).RoutesHaveDisjointInteriors := by
  intro first firstMember second secondMember
    firstShift secondShift different
  rcases
      exists_retainedPhysicalSegment_of_finalSegmentOccurrence
        formula wellFormed degree isLocal clausesNonempty
        first firstMember firstShift with
    ⟨firstWitness⟩
  rcases
      exists_retainedPhysicalSegment_of_finalSegmentOccurrence
        formula wellFormed degree isLocal clausesNonempty
        second secondMember secondShift with
    ⟨secondWitness⟩
  exact
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstWitness secondWitness different

end PeriodicOrthocrossing
end LeanTrominoes
