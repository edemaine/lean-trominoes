/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatNormalizedRouteSelections
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentAllSeparation

/-!
# Route separation at normalized final carrier contacts

The normalized contact certificate identifies a carrier boundary shared with
a direct crossover or terminal component.  The normalized route selections
identify the two final lists with genuine routes of those drawings.

Combining these packages with the retained carrier-interface theorems proves
the complete continuous route-avoidance predicate for the final pair.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Final flat carrier and noncarrier routes avoid each other whenever their
normalized components carry one of the three exact contact certificates. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.routesAvoidEachOther_of_normalizedContact
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
    (contact :
      FinalGaugedFlatNormalizedCarrierContact
        formula carrier macrocell normalized) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      carrierTaggedRoute.1 macrocellTaggedRoute.1 := by
  rcases
      carrier.exists_normalizedRouteSelection
        formula wellFormed degree isLocal with
    ⟨carrierClauseIndex, ⟨carrierSelection⟩⟩
  rcases
      normalized.exists_routeSelection
        formula wellFormed degree isLocal with
    ⟨macrocellSelection⟩
  have normalizedLinkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  have firstTranslateNeighbor :=
    carrier.normalizedLink_first_neighbor
      formula wellFormed degree isLocal
  rw [carrierSelection.routeEq, macrocellSelection.routeEq]
  rcases contact with crossoverContact | terminalContact
  · rcases crossoverContact with
      ⟨crossing, localClauseIndex, sourceEq, incident⟩
    have avoid :=
      retainedDrawingPlanarSATCarrierCrossoverRoutesAvoidEachOther_of_raw_incident
        wellFormed degree isLocal normalizedLinkMember incident
        (by
          simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex] using
              carrierSelection.clauseMember)
        carrierSelection.literalMember
        (by
          simpa [sourceEq,
            DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex] using
              macrocellSelection.clauseMember)
        macrocellSelection.literalMember
    simpa [sourceEq,
      DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex] using avoid
  · rcases terminalContact with
      routedClauseContact | routedVariableContact
    · rcases routedClauseContact with
        ⟨site, occurrence, sourceEq,
          occurrenceMember, incident⟩
      have avoid :=
        retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther_of_raw_incident
          (routedClauseIndex := 0)
          wellFormed degree isLocal normalizedLinkMember
          occurrenceMember incident
          (by
            simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
              DrawingPlanarSATClauseSource.localClauseIndex] using
                carrierSelection.clauseMember)
          carrierSelection.literalMember
          (by
            simpa [sourceEq,
              DrawingPlanarSATClauseSource.incidenceDrawing,
              DrawingPlanarSATClauseSource.localClauseIndex] using
                macrocellSelection.clauseMember)
          macrocellSelection.literalMember
      simpa [sourceEq,
        DrawingPlanarSATClauseSource.incidenceDrawing,
        DrawingPlanarSATClauseSource.localClauseIndex] using avoid
    · rcases routedVariableContact with
        ⟨site, armIndex, arm, link,
          localClauseIndex, occurrence, sourceEq,
          _occurrenceMember, _incident⟩
      have sourceMember := normalized.sourceMember
      rw [sourceEq] at sourceMember
      have routedLinkMember :
          link ∈ routedVariableLinksAt formula site :=
        List.fst_mem_of_mem_zipIdx sourceMember.2.1
      have avoid :=
        retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_raw
          wellFormed degree isLocal normalizedLinkMember
          firstTranslateNeighbor routedLinkMember
          (by
            simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
              DrawingPlanarSATClauseSource.localClauseIndex] using
                carrierSelection.clauseMember)
          carrierSelection.literalMember
          (by
            simpa [sourceEq,
              DrawingPlanarSATClauseSource.incidenceDrawing,
              DrawingPlanarSATClauseSource.localClauseIndex] using
                macrocellSelection.clauseMember)
          macrocellSelection.literalMember
      simpa [sourceEq,
        DrawingPlanarSATClauseSource.incidenceDrawing,
        DrawingPlanarSATClauseSource.localClauseIndex] using avoid

end PeriodicOrthocrossing
end LeanTrominoes
