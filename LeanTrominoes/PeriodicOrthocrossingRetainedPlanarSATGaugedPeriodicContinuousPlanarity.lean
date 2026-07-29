import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierContactReduction
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierParallelSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierPerpendicularSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage

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

private theorem wrapPeriodicPlanarSATFormula_clausesNonempty
    {Original : Type*}
    (source : PeriodicCNF Original)
    (clausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈ (wrapPeriodicPlanarSATFormula source).clauses,
      clause ≠ [] := by
  intro clause clauseMember
  unfold wrapPeriodicPlanarSATFormula at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  intro empty
  apply clausesNonempty sourceClause sourceClauseMember
  apply List.length_eq_zero_iff.mp
  have lengthZero := congrArg List.length empty
  simpa [wrapPeriodicPlanarSATClause] using lengthZero

private theorem PeriodicCNF.variableGauge_clausesNonempty
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell)
    (clausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈ (source.variableGauge gauge).clauses,
      clause ≠ [] := by
  intro clause clauseMember
  unfold PeriodicCNF.variableGauge at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  intro empty
  apply clausesNonempty sourceClause sourceClauseMember
  apply List.length_eq_zero_iff.mp
  have lengthZero := congrArg List.length empty
  simpa using lengthZero

private theorem PeriodicCNF.anchorNormalize_clausesNonempty
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (clausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈ source.anchorNormalize.clauses,
      clause ≠ [] := by
  intro clause clauseMember
  unfold PeriodicCNF.anchorNormalize at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  intro empty
  apply clausesNonempty sourceClause sourceClauseMember
  apply List.length_eq_zero_iff.mp
  have lengthZero := congrArg List.length empty
  simpa using lengthZero

/-- The final gauging, anchor normalization, wrapping, and deduplication
pipeline preserves nonemptiness of every retained clause. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    ∀ clause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.clauses,
      clause ≠ [] := by
  have periodicNonempty :
      ∀ clause ∈
          (retainedDrawingPeriodicPlanarSATFormula formula).clauses,
        clause ≠ [] := by
    intro clause clauseMember
    unfold retainedDrawingPeriodicPlanarSATFormula at clauseMember
    rcases List.mem_map.mp clauseMember with
      ⟨embeddedClause, embeddedClauseMember, rfl⟩
    intro empty
    apply clausesNonempty embeddedClause embeddedClauseMember
    apply List.length_eq_zero_iff.mp
    have lengthZero := congrArg List.length empty
    simpa [periodicizePlanarSATClause] using lengthZero
  have wrappedNonempty :
      ∀ clause ∈
          (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase.clauses,
        clause ≠ [] := by
    rw [retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
    exact
      wrapPeriodicPlanarSATFormula_clausesNonempty
        (retainedDrawingPeriodicPlanarSATFormula formula)
        periodicNonempty
  have gaugedNonempty :
      ∀ clause ∈
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase.clauses,
        clause ≠ [] := by
    rw [retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      PositionedPeriodicCNF.erase_variableGauge]
    exact
      PeriodicCNF.variableGauge_clausesNonempty
        (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
        wrappedNonempty
  have anchorNormalizedNonempty :
      ∀ clause ∈
          (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase.clauses,
        clause ≠ [] := by
    rw [
      retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      PositionedPeriodicCNF.erase_anchorNormalize]
    exact
      PeriodicCNF.anchorNormalize_clausesNonempty
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase
        gaugedNonempty
  intro clause clauseMember
  apply anchorNormalizedNonempty clause
  rw [
    ← PositionedPeriodicCNF.clause_mem_erase_deduplicateByLiterals_iff,
    ← retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
  exact clauseMember

/-- Exact endpoints cover every graph vertex of the final gauged periodic
incidence drawing. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_vertexPositionsCoveredBySegmentEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).VertexPositionsCoveredBySegmentEndpoints := by
  apply
    PeriodicCNF.incidenceDrawing_vertexPositionsCoveredBySegmentEndpoints
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula)
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty
        formula clausesNonempty

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

/-- A final carrier occurrence's relative interior avoids both endpoints
of every final noncarrier occurrence, including diagonal noncarrier
segments. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carrier_noncarrier
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
    point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).start ∧
      point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).finish := by
  generalize sourceEq :
    second.routeWitness.metadata.source = source
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carrier_crossover
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
        retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carrier_bend
          formula wellFormed degree isLocal first second
          link firstComponentEq routeBend localClauseIndex sourceEq
          firstContains
  | routedClause site =>
      exact
        retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carrier_routedClause
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
        retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carrier_routedVariable
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

/-- The relative interior of every final segment occurrence avoids every
distinct closed final segment occurrence. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior
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
    {firstShift secondShift point : Cell}
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
          secondIndexed secondShift)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
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
          retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carriers_perpendicular
            formula wellFormed degree isLocal first second
            firstLink secondLink firstComponentEq secondComponentEq
            (by simpa only [translatedFirstLink] using perpendicular)
            point firstContains
      · by_cases samePhysicalKey :
          translatedFirstLink.first.carrierKey =
            secondLink.first.carrierKey
        · exact
            retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carriers_same_physical_key
              formula wellFormed degree isLocal clausesNonempty
              first second firstLink secondLink
              firstComponentEq secondComponentEq
              (by simpa only [translatedFirstLink] using samePhysicalKey)
              different point firstContains
        · exact
            retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carriers_parallel_key_ne
              formula wellFormed degree isLocal first second
              firstLink secondLink firstComponentEq secondComponentEq
              (by simpa only [translatedFirstLink] using perpendicular)
              (by simpa only [translatedFirstLink] using samePhysicalKey)
              point firstContains
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier
          formula wellFormed degree isLocal clausesNonempty
          firstMember first second firstLink firstComponentEq secondCarrier
          firstContains
  · by_cases secondCarrier :
      ∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink
    · rcases secondCarrier with ⟨secondLink, secondComponentEq⟩
      exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarrier_carrier
          formula wellFormed degree isLocal clausesNonempty
          secondMember second first secondLink secondComponentEq firstCarrier
          firstContains
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarriers
          formula wellFormed degree isLocal clausesNonempty
          first second firstCarrier secondCarrier different
          point firstContains

/-- The relative interior of every final segment occurrence avoids both
endpoints of every distinct final segment occurrence. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior
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
    {firstShift secondShift point : Cell}
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
          secondIndexed secondShift)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).start ∧
      point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).finish := by
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
          retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carriers_perpendicular
            formula wellFormed degree isLocal first second
            firstLink secondLink firstComponentEq secondComponentEq
            (by simpa only [translatedFirstLink] using perpendicular)
            point firstContains
      · by_cases samePhysicalKey :
          translatedFirstLink.first.carrierKey =
            secondLink.first.carrierKey
        · exact
            retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carriers_same_physical_key
              formula wellFormed degree isLocal clausesNonempty
              first second firstLink secondLink
              firstComponentEq secondComponentEq
              (by simpa only [translatedFirstLink] using samePhysicalKey)
              different point firstContains
        · exact
            retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carriers_parallel_key_ne
              formula wellFormed degree isLocal first second
              firstLink secondLink firstComponentEq secondComponentEq
              (by simpa only [translatedFirstLink] using perpendicular)
              (by simpa only [translatedFirstLink] using samePhysicalKey)
              point firstContains
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_carrier_noncarrier
          formula wellFormed degree isLocal clausesNonempty
          firstMember first second firstLink firstComponentEq secondCarrier
          firstContains
  · by_cases secondCarrier :
      ∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink
    · rcases secondCarrier with ⟨secondLink, secondComponentEq⟩
      have avoids :=
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarrier_carrier
          formula wellFormed degree isLocal clausesNonempty
          secondMember second first secondLink secondComponentEq firstCarrier
          firstContains
      have secondAligned :
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)).IsAxisAligned :=
        (GridSegment.isAxisAligned_translate _ _).mpr
          (second.indexedSegment_isAxisAligned_of_carrier
            wellFormed degree isLocal secondLink secondComponentEq)
      constructor
      · intro pointEq
        apply avoids
        rw [pointEq]
        exact
          GridSegment.contains_start_of_axisAligned secondAligned
      · intro pointEq
        apply avoids
        rw [pointEq]
        exact
          GridSegment.contains_finish_of_axisAligned secondAligned
    · exact
        retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_noncarriers
          formula wellFormed degree isLocal clausesNonempty
          first second firstCarrier secondCarrier different
          point firstContains

/-- The final gauged periodic incidence drawing has globally ordered
interior-versus-closed route separation. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAvoidInteriors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).RoutesAvoidInteriors := by
  intro first firstMember second secondMember
    firstShift secondShift point different firstContains
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
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstWitness secondWitness
      different firstContains

/-- The final gauged periodic incidence drawing has globally ordered
interior-versus-endpoint separation, including for diagonal target
segments. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsAvoidInteriors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).SegmentEndpointsAvoidInteriors := by
  intro first firstMember second secondMember
    firstShift secondShift point different firstContains
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
    retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstWitness secondWitness
      different firstContains

/-- No lifted graph vertex lies in the relative interior of a final route
segment.  Endpoint-aware separation is needed here because a retained
straight incidence route may be diagonal. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_verticesAvoidRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).VerticesAvoidRouteInteriors := by
  apply
    PeriodicGridDrawing.verticesAvoidRouteInteriors_of_endpointCoverage_of_segmentEndpointsAvoidInteriors
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_vertexPositionsCoveredBySegmentEndpoints
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsAvoidInteriors
        formula wellFormed degree isLocal clausesNonempty

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

/-- The final gauged periodic incidence drawing is planar. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).IsPlanar := by
  constructor
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesAvoidInteriors
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_verticesAvoidRouteInteriors
        formula wellFormed degree isLocal clausesNonempty

/-- The final gauged periodic incidence drawing is continuously planar. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).IsContinuouslyPlanar := by
  constructor
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isPlanar
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routesHaveDisjointInteriors
        formula wellFormed degree isLocal clausesNonempty

end PeriodicOrthocrossing
end LeanTrominoes
