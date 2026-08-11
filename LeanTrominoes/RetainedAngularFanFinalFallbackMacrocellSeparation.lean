import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceUniformity
import LeanTrominoes.RetainedFinalFlatRouteShapeClassification

/-!
# Failed choices cannot share an oblique direct macrocell

An oblique final segment forces its noncarrier component to be one of the
direct two-point families.  Equality of translated macrocell centers
transfers that classification to the other route.  But every genuine route
from a direct family admits a successful final direct-source choice, so a
failed choice cannot occupy that same translated macrocell.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

set_option maxHeartbeats 400000

/-- A successful final selector certifies that the representative physical
route witness consulted by that selector comes from one of the three direct
component families. -/
theorem
    FinalGaugedRouteOccurrenceWitness.componentIsDirect_of_finalChoiceSome
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice) :
    witness.metadata.source.component.IsDirect := by
  rcases
      retainedFinalDirectSourceRouteChoice_exists_raw
        formula clauseIndex literalIndex choice choiceLookup with
    ⟨metadata, rawChoice, metadataLookup, rawLookup, choiceEq⟩
  have witnessMetadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some witness.metadata := by
    have representativeLookup := witness.representativeMetadataLookup
    unfold retainedFinalDirectSourceMetadata?
    exact retainedRepresentativeItem?_eq_some_of_lookups
      (Variable := Variable)
      (Item := DrawingPlanarSATClauseMetadata Variable)
      formula (retainedDrawingPlanarSATClauseMetadata formula)
      clauseIndex witness.finalClause witness.metadata
      witness.finalClauseLookup representativeLookup
  have metadataEq : metadata = witness.metadata :=
    Option.some.inj (metadataLookup.symm.trans witnessMetadataLookup)
  clear choiceEq metadataLookup witnessMetadataLookup
  subst metadata
  cases sourceEq : witness.metadata.source with
  | crossover crossing localClauseIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect]
  | carrier link localClauseIndex =>
      rw [sourceEq] at rawLookup
      simp [retainedDirectSourceRouteChoice?] at rawLookup
  | bend routeBend localClauseIndex =>
      rw [sourceEq] at rawLookup
      simp [retainedDirectSourceRouteChoice?] at rawLookup
  | routedClause site =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect]
  | routedVariable site armIndex arm link localClauseIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect]

/-- The macrocell packaging of a route preserves the direct-component
certificate recovered from a successful final choice. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.componentIsDirect_of_finalChoiceSome
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteMacrocellWitness formula taggedRoute)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula witness.coordinates.taggedClause.2
            witness.coordinates.taggedLiteral.2 = some choice) :
    witness.routeWitness.metadata.source.component.IsDirect := by
  exact
    witness.routeWitness.componentIsDirect_of_finalChoiceSome
      formula choice choiceLookup

/-- A macrocell route whose final direct-source choice fails cannot share a
translated center with a macrocell route already known to come from a direct
component. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_choice_none_of_second_component_isDirect
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {failedTaggedRoute referenceTaggedRoute : List Cell × Nat}
    (failed :
      FinalGaugedFlatRouteMacrocellWitness
        formula failedTaggedRoute)
    (reference :
      FinalGaugedFlatRouteMacrocellWitness
        formula referenceTaggedRoute)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failed.coordinates.taggedClause.2
            failed.coordinates.taggedLiteral.2 = none)
    (referenceDirect :
      reference.routeWitness.metadata.source.component.IsDirect) :
    failed.translatedCenter ≠ reference.translatedCenter := by
  intro centersEqual
  have failedDirect :=
    failed.first_component_isDirect_of_translatedCenters_eq
      formula wellFormed degree isLocal
      reference centersEqual referenceDirect
  have directCases :
      (∃ crossing localClauseIndex,
          failed.routeWitness.metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          failed.routeWitness.metadata.source =
            .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          failed.routeWitness.metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex) := by
    cases sourceEq : failed.routeWitness.metadata.source with
    | crossover crossing localClauseIndex =>
        exact Or.inl ⟨crossing, localClauseIndex, rfl⟩
    | carrier link localClauseIndex =>
        rw [sourceEq] at failedDirect
        simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.IsDirect] at failedDirect
    | bend routeBend localClauseIndex =>
        rw [sourceEq] at failedDirect
        simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.IsDirect] at failedDirect
    | routedClause site =>
        exact Or.inr (Or.inl ⟨site, rfl⟩)
    | routedVariable site armIndex arm link localClauseIndex =>
        exact Or.inr (Or.inr
          ⟨site, armIndex, arm, link, localClauseIndex, rfl⟩)
  rcases
      exists_finalDirectSourceRouteChoice_of_witness_directCases
        formula failed.routeWitness directCases with
    ⟨choice, choiceSome⟩
  rw [choiceNone] at choiceSome
  cases choiceSome

/-- A failed final direct-source choice cannot occupy the translated
macrocell center of any successfully selected direct-source route. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_choice_none_of_second_choice_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {failedTaggedRoute referenceTaggedRoute : List Cell × Nat}
    (failed :
      FinalGaugedFlatRouteMacrocellWitness
        formula failedTaggedRoute)
    (reference :
      FinalGaugedFlatRouteMacrocellWitness
        formula referenceTaggedRoute)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failed.coordinates.taggedClause.2
            failed.coordinates.taggedLiteral.2 = none)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula reference.coordinates.taggedClause.2
            reference.coordinates.taggedLiteral.2 = some choice) :
    failed.translatedCenter ≠ reference.translatedCenter := by
  exact
    failed.translatedCenter_ne_of_choice_none_of_second_component_isDirect
      formula wellFormed degree isLocal reference choiceNone
      (reference.componentIsDirect_of_finalChoiceSome
        formula choice choiceSome)

/-- A macrocell route whose final direct-source choice fails has translated
center different from every macrocell route with an oblique final segment. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_choice_none_of_second_finalSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {failedTaggedRoute referenceTaggedRoute : List Cell × Nat}
    (failed :
      FinalGaugedFlatRouteMacrocellWitness
        formula failedTaggedRoute)
    (reference :
      FinalGaugedFlatRouteMacrocellWitness
        formula referenceTaggedRoute)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failed.coordinates.taggedClause.2
            failed.coordinates.taggedLiteral.2 = none)
    (referenceLength : 2 ≤ referenceTaggedRoute.1.length)
    {referenceTarget : Cell}
    (referenceLast :
      referenceTaggedRoute.1.getLast? = some referenceTarget)
    (referenceOblique :
      ¬(⟨polylineLastEntrance referenceTaggedRoute.1,
          referenceTarget⟩ : GridSegment).IsAxisAligned) :
    failed.translatedCenter ≠ reference.translatedCenter := by
  have referenceDirect :=
    reference.component_isDirect_of_finalSegment_not_axisAligned
      formula wellFormed degree isLocal
      referenceLength referenceLast referenceOblique
  exact
    failed.translatedCenter_ne_of_choice_none_of_second_component_isDirect
      formula wellFormed degree isLocal
      reference choiceNone referenceDirect

end PeriodicOrthocrossing
end LeanTrominoes
