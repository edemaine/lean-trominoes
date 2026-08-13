/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentProximity

/-!
# Retained carriers at arbitrary lifted routed vertices

The existing routed-clause and routed-variable proximity wrappers assume a
represented route occurrence at the lifted site.  A period-translated direct
component may lie outside the finite site enumeration even though its base
graph vertex is still declared.  The lower-level terminal theorem already
supports an arbitrary lift translation.

These wrappers start from base-vertex membership instead.  The terminal
found on the retained carrier is converted back into a finite route endpoint;
injectivity of lifted vertex positions then identifies an occurrence at the
requested translated site.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Overlap with the macrocell of any lift of a declared variable vertex
forces incidence to the target terminal of an occurrence at that exact
lifted site. -/
theorem
    retainedDrawingCompleteCarrierLink_exists_targetOccurrence_of_liftedVariableMacrocell_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (atom : Variable)
    (variableMem :
      (CNFVertex.variable atom) ∈
        formula.incidenceGraph.vertices)
    (translate : Cell)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph link)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph link)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula (.variable atom) translate))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula (.variable atom) translate))) :
    ∃ occurrence,
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
        occurrence ∈
          variableRouteOccurrencesAt formula (atom, translate) ∧
        CarrierLinkIncidentToTargetTerminal
          formula link occurrence := by
  let graph := formula.incidenceGraph
  rcases
      retainedDrawingCompleteCarrierLink_incidentToTerminalAtLiftedVertex_of_macrocell_overlap
        wellFormed degree isLocal linkMem variableMem translate
        notSeparated with
    ⟨terminal, terminalMem, terminalPoint, linkIncident⟩
  rcases
      drawingSegmentTerminal_routeEndpoint_of_drawingPoint_eq_liftedVertex
        wellFormed degree isLocal terminalMem variableMem translate
        terminalPoint with
    ⟨endpoint, endpointMem, terminalEq⟩
  rcases drawingRouteEndpoint_exists_CNFRouteEndpoint
      formula endpointMem with
    ⟨routeEndpoint, occurrenceMem,
      routeEndpointMem, endpointEq⟩
  have endpointCanonical :=
    routeEndpoint.terminal_eq_source_or_target
      formula routeEndpointMem
  have terminalEndpointEq :
      terminal = routeEndpoint.endpoint.terminal := by
    exact terminalEq.trans
      (congrArg RouteEndpoint.terminal endpointEq.symm)
  have occurrenceEdgeMem :=
    routeEndpoint.occurrence.taggedEdge_mem formula occurrenceMem
  rcases endpointCanonical with sourceData | targetData
  · have sourceVertexMem :
        (CNFVertex.clause
          routeEndpoint.occurrence.clauseOccurrence.1) ∈
            graph.vertices := by
      have rawSourceMem :=
        (wellFormed.2 routeEndpoint.occurrence.edge
          (List.fst_mem_of_mem_zipIdx occurrenceEdgeMem)).1
      simpa [graph, CNFRouteOccurrence.edge,
        CNFRouteOccurrence.clauseOccurrence] using rawSourceMem
    have sourcePoint :=
      CNFRouteOccurrence.sourceTerminal_drawingPoint_eq_lifted
        formula wellFormed routeEndpoint.occurrence
        occurrenceEdgeMem
    have liftedEq :
        liftedIncidenceVertexPosition formula
            (.clause
              routeEndpoint.occurrence.clauseOccurrence.1)
            routeEndpoint.occurrence.clauseOccurrence.2 =
          liftedIncidenceVertexPosition formula
            (.variable atom) translate := by
      rw [← sourcePoint, ← sourceData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have impossible :=
      liftedDrawingVertexPosition_eq
        graph sourceVertexMem variableMem liftedEq
    cases impossible.1
  · have targetPoint :=
      routeEndpoint.occurrence.targetTerminal_drawingPoint_eq_lifted
        formula wellFormed occurrenceMem
    have targetVertexMem :
        (CNFVertex.variable
          routeEndpoint.occurrence.variableOccurrence.1) ∈
            graph.vertices := by
      have rawTargetMem :=
        (wellFormed.2 routeEndpoint.occurrence.edge
          (List.fst_mem_of_mem_zipIdx occurrenceEdgeMem)).2
      simpa [graph, CNFRouteOccurrence.edge,
        CNFRouteOccurrence.variableOccurrence] using rawTargetMem
    have liftedEq :
        liftedIncidenceVertexPosition formula
            (.variable
              routeEndpoint.occurrence.variableOccurrence.1)
            routeEndpoint.occurrence.variableOccurrence.2 =
          liftedIncidenceVertexPosition formula
            (.variable atom) translate := by
      rw [← targetPoint, ← targetData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have siteData :=
      liftedDrawingVertexPosition_eq
        graph targetVertexMem variableMem liftedEq
    have occurrenceSiteEq :
        routeEndpoint.occurrence.variableOccurrence =
          (atom, translate) := by
      apply Prod.ext
      · exact CNFVertex.variable.inj siteData.1
      · exact siteData.2
    refine
      ⟨routeEndpoint.occurrence,
        occurrenceMem,
        routeEndpoint.occurrence
          |>.mem_variableRouteOccurrencesAt_of_mem_drawing
            formula occurrenceMem (atom, translate)
              occurrenceSiteEq,
        ?_⟩
    simpa [CarrierLinkIncidentToTargetTerminal,
      terminalEndpointEq, targetData.2] using linkIncident

/-- Overlap with the macrocell of any lift of a declared clause vertex
forces incidence to the source terminal of an occurrence at that exact
lifted site. -/
theorem
    retainedDrawingCompleteCarrierLink_exists_sourceOccurrence_of_liftedClauseMacrocell_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (clauseIndex : Nat)
    (clauseMem :
      (CNFVertex.clause clauseIndex) ∈
        formula.incidenceGraph.vertices)
    (translate : Cell)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph link)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph link)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula (.clause clauseIndex) translate))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula (.clause clauseIndex) translate))) :
    ∃ occurrence,
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
        occurrence ∈
          clauseRouteOccurrencesAt formula (clauseIndex, translate) ∧
        CarrierLinkIncidentToSourceTerminal
          formula link occurrence := by
  let graph := formula.incidenceGraph
  rcases
      retainedDrawingCompleteCarrierLink_incidentToTerminalAtLiftedVertex_of_macrocell_overlap
        wellFormed degree isLocal linkMem clauseMem translate
        notSeparated with
    ⟨terminal, terminalMem, terminalPoint, linkIncident⟩
  rcases
      drawingSegmentTerminal_routeEndpoint_of_drawingPoint_eq_liftedVertex
        wellFormed degree isLocal terminalMem clauseMem translate
        terminalPoint with
    ⟨endpoint, endpointMem, terminalEq⟩
  rcases drawingRouteEndpoint_exists_CNFRouteEndpoint
      formula endpointMem with
    ⟨routeEndpoint, occurrenceMem,
      routeEndpointMem, endpointEq⟩
  have endpointCanonical :=
    routeEndpoint.terminal_eq_source_or_target
      formula routeEndpointMem
  have terminalEndpointEq :
      terminal = routeEndpoint.endpoint.terminal := by
    exact terminalEq.trans
      (congrArg RouteEndpoint.terminal endpointEq.symm)
  have occurrenceEdgeMem :=
    routeEndpoint.occurrence.taggedEdge_mem formula occurrenceMem
  rcases endpointCanonical with sourceData | targetData
  · have sourcePoint :=
      CNFRouteOccurrence.sourceTerminal_drawingPoint_eq_lifted
        formula wellFormed routeEndpoint.occurrence
        occurrenceEdgeMem
    have sourceVertexMem :
        (CNFVertex.clause
          routeEndpoint.occurrence.clauseOccurrence.1) ∈
            graph.vertices := by
      have rawSourceMem :=
        (wellFormed.2 routeEndpoint.occurrence.edge
          (List.fst_mem_of_mem_zipIdx occurrenceEdgeMem)).1
      simpa [graph, CNFRouteOccurrence.edge,
        CNFRouteOccurrence.clauseOccurrence] using rawSourceMem
    have liftedEq :
        liftedIncidenceVertexPosition formula
            (.clause
              routeEndpoint.occurrence.clauseOccurrence.1)
            routeEndpoint.occurrence.clauseOccurrence.2 =
          liftedIncidenceVertexPosition formula
            (.clause clauseIndex) translate := by
      rw [← sourcePoint, ← sourceData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have siteData :=
      liftedDrawingVertexPosition_eq
        graph sourceVertexMem clauseMem liftedEq
    have occurrenceSiteEq :
        routeEndpoint.occurrence.clauseOccurrence =
          (clauseIndex, translate) := by
      apply Prod.ext
      · exact CNFVertex.clause.inj siteData.1
      · exact siteData.2
    refine
      ⟨routeEndpoint.occurrence,
        occurrenceMem,
        routeEndpoint.occurrence
          |>.mem_clauseRouteOccurrencesAt_of_mem_drawing
            formula occurrenceMem (clauseIndex, translate)
              occurrenceSiteEq,
        ?_⟩
    simpa [CarrierLinkIncidentToSourceTerminal,
      terminalEndpointEq, sourceData.2] using linkIncident
  · have targetPoint :=
      routeEndpoint.occurrence.targetTerminal_drawingPoint_eq_lifted
        formula wellFormed occurrenceMem
    have targetVertexMem :
        (CNFVertex.variable
          routeEndpoint.occurrence.variableOccurrence.1) ∈
            graph.vertices := by
      have rawTargetMem :=
        (wellFormed.2 routeEndpoint.occurrence.edge
          (List.fst_mem_of_mem_zipIdx occurrenceEdgeMem)).2
      simpa [graph, CNFRouteOccurrence.edge,
        CNFRouteOccurrence.variableOccurrence] using rawTargetMem
    have liftedEq :
        liftedIncidenceVertexPosition formula
            (.variable
              routeEndpoint.occurrence.variableOccurrence.1)
            routeEndpoint.occurrence.variableOccurrence.2 =
          liftedIncidenceVertexPosition formula
            (.clause clauseIndex) translate := by
      rw [← targetPoint, ← targetData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have impossible :=
      liftedDrawingVertexPosition_eq
        graph targetVertexMem clauseMem liftedEq
    cases impossible.1

end PeriodicOrthocrossing
end LeanTrominoes
