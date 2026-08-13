/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCarrierFrameOverlapNormalization
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLiftedVertexOccurrenceProximity

/-!
# Terminal contacts in the selected final carrier frame

For an overlapping carrier occurrence and direct macrocell occurrence, keep
the carrier's original selected link fixed and translate the direct component
by the relative physical shift.  The routed-clause and routed-variable cases
then meet the carrier at an exact source or target terminal, respectively.

The only direct constructor not covered by this terminal argument is a
translated crossover.  The main reduction theorem exposes that case
separately for the crossover-boundary argument.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Terminal incidence data for a relatively translated direct component
against the original selected carrier link. -/
def FinalGaugedCarrierFrameTerminalContact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift) :
    Prop :=
  (∃ site occurrence,
      macrocell.metadata.source.periodTranslate formula
          (macrocell.relativeShiftFrom carrier) =
        .routedClause site ∧
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
      occurrence ∈ clauseRouteOccurrencesAt formula site ∧
      CarrierLinkIncidentToSourceTerminal
        formula carrier.link occurrence) ∨
    (∃ site armIndex arm link localClauseIndex occurrence,
      macrocell.metadata.source.periodTranslate formula
          (macrocell.relativeShiftFrom carrier) =
        .routedVariable
          site armIndex arm link localClauseIndex ∧
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
      occurrence ∈ variableRouteOccurrencesAt formula site ∧
      CarrierLinkIncidentToTargetTerminal
        formula carrier.link occurrence)

/-- An overlapping selected carrier and direct macrocell yield either the
single translated-crossover residue or an exact translated terminal contact. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.crossover_or_carrierFrameTerminalContact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (direct : macrocell.metadata.source.component.IsDirect)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    (∃ crossing localClauseIndex,
        macrocell.metadata.source =
          .crossover crossing localClauseIndex) ∨
      FinalGaugedCarrierFrameTerminalContact
        formula carrier macrocell := by
  let relativeShift := macrocell.relativeShiftFrom carrier
  have sourceMember :=
    (macrocell.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp macrocell.metadata_retainedValid |>.1
  have overlap :=
    carrier.link_relativeMacrocell_overlap macrocell notSeparated
  cases sourceEq : macrocell.metadata.source with
  | crossover crossing localClauseIndex =>
      exact Or.inl ⟨crossing, localClauseIndex, rfl⟩
  | carrier link localClauseIndex =>
      simp [sourceEq, DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect] at direct
  | bend routeBend localClauseIndex =>
      simp [sourceEq, DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect] at direct
  | routedClause site =>
      have siteMember : site ∈ drawingClauseRouteSites formula := by
        rw [sourceEq] at sourceMember
        exact sourceMember
      let targetSite :=
        clauseRouteSitePeriodTranslate site relativeShift
      have translatedSourceEq :
          macrocell.metadata.source.periodTranslate formula
              relativeShift =
            .routedClause targetSite := by
        simp [sourceEq, targetSite,
          DrawingPlanarSATClauseSource.periodTranslate]
      have centerEq :
          macrocell.center =
            liftedIncidenceVertexPosition
              formula (.clause site.1) site.2 := by
        have advertised := macrocell.centerEq
        rw [sourceEq] at advertised
        simpa [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.macrocellCenter] using
            Option.some.inj advertised.symm
      have relativeCenterEq :
          macrocell.relativeCenterFrom carrier =
            liftedIncidenceVertexPosition
              formula (.clause targetSite.1) targetSite.2 := by
        rw [show targetSite.1 = site.1 by rfl,
          show targetSite.2 = Cell.add site.2 relativeShift by rfl,
          liftedIncidenceVertexPosition_periodTranslate]
        simp [FinalGaugedRouteMacrocellOccurrenceWitness.relativeCenterFrom,
          relativeShift, centerEq]
      have targetOverlap :
          ¬ClosedGridRectanglesSeparated
            (drawingCompleteCarrierLinkRectangleLower
              formula.incidenceGraph carrier.link)
            (drawingCompleteCarrierLinkRectangleUpper
              formula.incidenceGraph carrier.link)
            (planarSATMacrocellRouteLower
              (liftedIncidenceVertexPosition
                formula (.clause targetSite.1) targetSite.2))
            (planarSATMacrocellRouteUpper
              (liftedIncidenceVertexPosition
                formula (.clause targetSite.1) targetSite.2)) := by
        simpa only [← relativeCenterEq] using overlap
      obtain ⟨occurrence, occurrenceData⟩ :=
          retainedDrawingCompleteCarrierLink_exists_sourceOccurrence_of_liftedClauseMacrocell_overlap
            wellFormed degree isLocal carrier.link_mem
            targetSite.1
            (by
              simpa only [targetSite,
                clauseRouteSitePeriodTranslate] using
                drawingClauseRouteSite_vertex_mem formula siteMember)
            targetSite.2 targetOverlap
      have occurrenceGlobal := occurrenceData.1
      have occurrenceMember := occurrenceData.2.1
      have incident := occurrenceData.2.2
      exact Or.inr (Or.inl
        ⟨targetSite, occurrence, translatedSourceEq,
          occurrenceGlobal, occurrenceMember, incident⟩)
  | routedVariable
      site armIndex arm link localClauseIndex =>
      have siteMember : site ∈ drawingVariableRouteSites formula := by
        rw [sourceEq] at sourceMember
        exact sourceMember.1
      let targetSite :=
        variableRouteSitePeriodTranslate site relativeShift
      let targetLink :=
        planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link relativeShift
      have translatedSourceEq :
          macrocell.metadata.source.periodTranslate formula
              relativeShift =
            .routedVariable
              targetSite armIndex arm targetLink localClauseIndex := by
        simp [sourceEq, targetSite, targetLink,
          DrawingPlanarSATClauseSource.periodTranslate]
      have centerEq :
          macrocell.center =
            liftedIncidenceVertexPosition
              formula (.variable site.1) site.2 := by
        have advertised := macrocell.centerEq
        rw [sourceEq] at advertised
        simpa [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.macrocellCenter] using
            Option.some.inj advertised.symm
      have relativeCenterEq :
          macrocell.relativeCenterFrom carrier =
            liftedIncidenceVertexPosition
              formula (.variable targetSite.1) targetSite.2 := by
        rw [show targetSite.1 = site.1 by rfl,
          show targetSite.2 = Cell.add site.2 relativeShift by rfl,
          liftedIncidenceVertexPosition_periodTranslate]
        simp [FinalGaugedRouteMacrocellOccurrenceWitness.relativeCenterFrom,
          relativeShift, centerEq]
      have targetOverlap :
          ¬ClosedGridRectanglesSeparated
            (drawingCompleteCarrierLinkRectangleLower
              formula.incidenceGraph carrier.link)
            (drawingCompleteCarrierLinkRectangleUpper
              formula.incidenceGraph carrier.link)
            (planarSATMacrocellRouteLower
              (liftedIncidenceVertexPosition
                formula (.variable targetSite.1) targetSite.2))
            (planarSATMacrocellRouteUpper
              (liftedIncidenceVertexPosition
                formula (.variable targetSite.1) targetSite.2)) := by
        simpa only [← relativeCenterEq] using overlap
      obtain ⟨occurrence, occurrenceData⟩ :=
          retainedDrawingCompleteCarrierLink_exists_targetOccurrence_of_liftedVariableMacrocell_overlap
            wellFormed degree isLocal carrier.link_mem
            targetSite.1
            (by
              simpa only [targetSite,
                variableRouteSitePeriodTranslate] using
                drawingVariableRouteSite_vertex_mem formula siteMember)
            targetSite.2 targetOverlap
      have occurrenceGlobal := occurrenceData.1
      have occurrenceMember := occurrenceData.2.1
      have incident := occurrenceData.2.2
      exact Or.inr (Or.inr
        ⟨targetSite, armIndex, arm, targetLink,
          localClauseIndex, occurrence, translatedSourceEq,
          occurrenceGlobal, occurrenceMember, incident⟩)

end PeriodicOrthocrossing
end LeanTrominoes
