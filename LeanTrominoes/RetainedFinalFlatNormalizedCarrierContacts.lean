/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatNormalizedSourceOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentProximity

/-!
# Carrier contacts with normalized direct components

The last unresolved carrier--fan case has overlapping enclosing rectangles
and an oblique noncarrier terminal.  In the common anchor-normalized frame,
the retained-carrier proximity theorems turn this overlap into genuine local
incidence.

This file packages the three possible contact certificates without losing
the normalized source constructor.  Subsequent fan geometry may therefore
reason directly about the exact crossover route, routed-clause occurrence,
or routed-variable occurrence selected by the final route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The three incidence certificates obtainable when a raw normalized
carrier overlaps a direct normalized macrocell source. -/
def FinalGaugedFlatNormalizedCarrierContact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell) : Prop :=
  (∃ crossing localClauseIndex,
      normalized.source =
          .crossover crossing localClauseIndex ∧
        CarrierLinkIncidentToCrossover
          carrier.normalizedLink crossing) ∨
    (∃ site occurrence,
      normalized.source = .routedClause site ∧
        occurrence ∈ clauseRouteOccurrencesAt formula site ∧
        CarrierLinkIncidentToSourceTerminal
          formula carrier.normalizedLink occurrence) ∨
    (∃ site armIndex arm link localClauseIndex occurrence,
      normalized.source =
          .routedVariable
            site armIndex arm link localClauseIndex ∧
        occurrence ∈ variableRouteOccurrencesAt formula site ∧
        CarrierLinkIncidentToTargetTerminal
          formula carrier.normalizedLink occurrence)

/-- Rectangle overlap with a direct normalized source forces one of the
three exact local incidence certificates. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.normalizedDirectContact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (direct : normalized.source.component.IsDirect)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    FinalGaugedFlatNormalizedCarrierContact
      formula carrier macrocell normalized := by
  have linkMem :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  have firstTranslateNeighbor :=
    carrier.normalizedLink_first_neighbor
      formula wellFormed degree isLocal
  have overlap :=
    carrier.normalizedLink_macrocell_overlap
      macrocell notSeparated
  rcases normalized.directCases direct with
      crossoverCase | terminalCase
  · rcases crossoverCase with
      ⟨crossing, localClauseIndex, sourceEq⟩
    have crossingMember := normalized.sourceMember
    rw [sourceEq] at crossingMember
    have centerEq := normalized.centerEq
    rw [sourceEq] at centerEq
    simp [DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.macrocellCenter] at centerEq
    have crossingOverlap :
        ¬ClosedGridRectanglesSeparated
          (drawingCompleteCarrierLinkRectangleLower
            formula.incidenceGraph carrier.normalizedLink)
          (drawingCompleteCarrierLinkRectangleUpper
            formula.incidenceGraph carrier.normalizedLink)
          (planarSATMacrocellRouteLower crossing.point)
          (planarSATMacrocellRouteUpper crossing.point) := by
      simpa [centerEq] using overlap
    exact Or.inl
      ⟨crossing, localClauseIndex, sourceEq,
        retainedDrawingCompleteCarrierLinkRaw_incidentToCrossover_of_overlap
          wellFormed degree isLocal linkMem
          crossingMember crossingOverlap⟩
  · rcases terminalCase with routedClauseCase | routedVariableCase
    · rcases routedClauseCase with ⟨site, sourceEq⟩
      rcases
          normalized.exists_clauseRouteOccurrence_of_source_eq
            formula wellFormed degree isLocal sourceEq with
        ⟨representedOccurrence, representedOccurrenceMember⟩
      have centerEq := normalized.centerEq
      rw [sourceEq] at centerEq
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] at centerEq
      have clauseOverlap :
          ¬ClosedGridRectanglesSeparated
            (drawingCompleteCarrierLinkRectangleLower
              formula.incidenceGraph carrier.normalizedLink)
            (drawingCompleteCarrierLinkRectangleUpper
              formula.incidenceGraph carrier.normalizedLink)
            (planarSATMacrocellRouteLower
              (liftedIncidenceVertexPosition
                formula (.clause site.1) site.2))
            (planarSATMacrocellRouteUpper
              (liftedIncidenceVertexPosition
                formula (.clause site.1) site.2)) := by
        simpa [centerEq] using overlap
      rcases
          retainedDrawingCompleteCarrierLinkRaw_exists_sourceOccurrence_of_clauseMacrocell_overlap
            wellFormed degree isLocal linkMem
            firstTranslateNeighbor site
            representedOccurrenceMember clauseOverlap with
        ⟨occurrence, occurrenceMember, incident⟩
      exact Or.inr (Or.inl
        ⟨site, occurrence, sourceEq,
          occurrenceMember, incident⟩)
    · rcases routedVariableCase with
        ⟨site, armIndex, arm, link,
          localClauseIndex, sourceEq⟩
      rcases
          normalized.exists_variableRouteOccurrence_of_source_eq
            sourceEq with
        ⟨representedOccurrence, representedOccurrenceMember,
          _firstEndpointEq⟩
      have centerEq := normalized.centerEq
      rw [sourceEq] at centerEq
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] at centerEq
      have variableOverlap :
          ¬ClosedGridRectanglesSeparated
            (drawingCompleteCarrierLinkRectangleLower
              formula.incidenceGraph carrier.normalizedLink)
            (drawingCompleteCarrierLinkRectangleUpper
              formula.incidenceGraph carrier.normalizedLink)
            (planarSATMacrocellRouteLower
              (liftedIncidenceVertexPosition
                formula (.variable site.1) site.2))
            (planarSATMacrocellRouteUpper
              (liftedIncidenceVertexPosition
                formula (.variable site.1) site.2)) := by
        simpa [centerEq] using overlap
      rcases
          retainedDrawingCompleteCarrierLinkRaw_exists_targetOccurrence_of_variableMacrocell_overlap
            wellFormed degree isLocal linkMem
            firstTranslateNeighbor site
            representedOccurrenceMember variableOverlap with
        ⟨occurrence, occurrenceMember, incident⟩
      exact Or.inr (Or.inr
        ⟨site, armIndex, arm, link,
          localClauseIndex, occurrence, sourceEq,
          occurrenceMember, incident⟩)

/-- The oblique final-segment hypothesis supplies directness automatically,
so an unresolved final rectangle overlap already yields a local contact
certificate. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.normalizedContact_of_finalSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (routeLength : 2 ≤ macrocellTaggedRoute.1.length)
    {target : Cell}
    (routeLast :
      macrocellTaggedRoute.1.getLast? = some target)
    (finalSegmentNotAxisAligned :
      ¬(⟨polylineLastEntrance macrocellTaggedRoute.1,
          target⟩ : GridSegment).IsAxisAligned)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    FinalGaugedFlatNormalizedCarrierContact
      formula carrier macrocell normalized := by
  apply carrier.normalizedDirectContact
    formula wellFormed degree isLocal
    macrocell normalized
  · apply normalized.componentIsDirect
    exact
      macrocell.component_isDirect_of_finalSegment_not_axisAligned
        formula wellFormed degree isLocal
        routeLength routeLast finalSegmentNotAxisAligned
  · exact notSeparated

end PeriodicOrthocrossing
end LeanTrominoes
