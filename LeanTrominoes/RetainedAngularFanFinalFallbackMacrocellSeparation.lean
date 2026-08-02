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

set_option maxHeartbeats 400000

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
