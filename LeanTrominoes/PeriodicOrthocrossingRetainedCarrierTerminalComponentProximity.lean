import LeanTrominoes.PeriodicOrthocrossingDrawingVertexAvoidance
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendProximity
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentSeparation

/-!
# Selected retained carriers near routed graph vertices

Macrocell overlap between a selected retained carrier and a lifted graph
vertex forces the carrier to end at one of the route terminals incident to
that vertex.  For incidence graphs, the endpoint can be lifted back to the
metadata-rich CNF route occurrence that generated it.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

/-- A neighboring segment terminal located at a lifted graph vertex is an
external route endpoint, rather than an internal bend terminal. -/
theorem drawingSegmentTerminal_routeEndpoint_of_drawingPoint_eq_liftedVertex
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph)
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices)
    (vertexTranslate : Cell)
    (pointEq :
      terminal.drawingPoint graph =
        Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation vertexTranslate)) :
    ∃ endpoint,
      endpoint ∈ drawingRouteEndpoints graph ∧
        terminal = endpoint.terminal := by
  rcases drawingSegmentTerminal_bend_or_routeEndpoint
      graph terminalMem with
    terminalBend | terminalEndpoint
  · rcases terminalBend with
      ⟨routeBend, routeBendMem, terminalEq⟩
    have bendPoint :
        routeBend.drawingPoint graph =
          Cell.add
            ((drawing graph).vertexPosition graph vertex)
            ((drawing graph).periodTranslation vertexTranslate) := by
      rw [← pointEq]
      rcases terminalEq with terminalEq | terminalEq <;>
        simp [terminalEq]
    exact
      ((drawingRouteBend_drawingPoint_ne_liftedVertexPosition
          wellFormed degree isLocal vertexMem vertexTranslate
          routeBendMem)
        bendPoint).elim
  · exact terminalEndpoint

/-- If a selected retained lens overlaps the macrocell of a lifted declared
vertex, one of its endpoints is a segment terminal at that vertex. -/
theorem
    retainedDrawingCompleteCarrierLink_incidentToTerminalAtLiftedVertex_of_macrocell_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices)
    (vertexTranslate : Cell)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower
          (Cell.add
            ((drawing graph).vertexPosition graph vertex)
            ((drawing graph).periodTranslation vertexTranslate)))
        (planarSATMacrocellRouteUpper
          (Cell.add
            ((drawing graph).vertexPosition graph vertex)
            ((drawing graph).periodTranslation vertexTranslate)))) :
    ∃ terminal,
      terminal ∈ drawingSegmentTerminals graph ∧
        terminal.drawingPoint graph =
          Cell.add
            ((drawing graph).vertexPosition graph vertex)
            ((drawing graph).periodTranslation vertexTranslate) ∧
        (link.first = .terminal terminal ∨
          link.second = .terminal terminal) := by
  let center :=
    Cell.add
      ((drawing graph).vertexPosition graph vertex)
      ((drawing graph).periodTranslation vertexTranslate)
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have firstIndexedMem :
      link.first.indexed ∈ (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph endpoints.1
  have firstTranslateNeighbor :
      IsNeighborTranslation link.first.translate :=
    retainedDrawingCompleteCarrierLink_first_translate_neighbor
      graph linkMem
  have centerContains :
      (link.first.supportingSegment graph).Contains center :=
    retainedDrawingCompleteCarrierLink_supportingSegment_contains_of_macrocell_overlap
      wellFormed degree isLocal linkMem center notSeparated
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        centerContains with
    centerInterior | centerEndpoint
  · exact
      (drawingSegment_not_interiorContains_liftedVertexPosition
          wellFormed degree isLocal firstIndexedMem
          link.first.translate vertexMem vertexTranslate
        (by simpa [center, CarrierNode.supportingSegment] using
          centerInterior)).elim
  · rcases centerEndpoint with centerStart | centerFinish
    · let terminal : SegmentTerminal :=
        ⟨link.first.indexed, link.first.translate, .start⟩
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        apply
          mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
            graph terminal firstIndexedMem firstTranslateNeighbor
      have terminalPoint :
          terminal.drawingPoint graph = center := by
        simpa [terminal, SegmentTerminal.drawingPoint,
          CarrierNode.supportingSegment, CarrierNode.indexed,
          CarrierNode.translate] using centerStart.symm
      have keyEqual :
          link.first.carrierKey = terminal.carrierKey := by
        simp [terminal,
          CarrierNode.carrierKey_eq_indexed_translate,
          SegmentTerminal.carrierKey]
      have incident :=
        retainedDrawingCompleteCarrierLink_incidentToTerminal_of_key_eq_of_overlap
          wellFormed degree isLocal linkMem terminalMem keyEqual
          (by simpa [terminalPoint] using notSeparated)
      exact ⟨terminal, terminalMem, terminalPoint, incident⟩
    · let terminal : SegmentTerminal :=
        ⟨link.first.indexed, link.first.translate, .finish⟩
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        apply
          mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
            graph terminal firstIndexedMem firstTranslateNeighbor
      have terminalPoint :
          terminal.drawingPoint graph = center := by
        simpa [terminal, SegmentTerminal.drawingPoint,
          CarrierNode.supportingSegment, CarrierNode.indexed,
          CarrierNode.translate] using centerFinish.symm
      have keyEqual :
          link.first.carrierKey = terminal.carrierKey := by
        simp [terminal,
          CarrierNode.carrierKey_eq_indexed_translate,
          SegmentTerminal.carrierKey]
      have incident :=
        retainedDrawingCompleteCarrierLink_incidentToTerminal_of_key_eq_of_overlap
          wellFormed degree isLocal linkMem terminalMem keyEqual
          (by simpa [terminalPoint] using notSeparated)
      exact ⟨terminal, terminalMem, terminalPoint, incident⟩

/-- Every generic incidence-graph route endpoint has the unique
metadata-rich CNF endpoint carrying the same geometric record. -/
theorem drawingRouteEndpoint_exists_CNFRouteEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {endpoint : RouteEndpoint (CNFVertex Variable)}
    (endpointMem :
      endpoint ∈ drawingRouteEndpoints
        (PeriodicCNF.incidenceGraph formula)) :
    ∃ routeEndpoint : CNFRouteEndpoint Variable,
      routeEndpoint.occurrence ∈
          drawingCNFRouteOccurrences formula ∧
        routeEndpoint ∈
          routeEndpoint.occurrence.endpoints formula ∧
        routeEndpoint.endpoint = endpoint := by
  rcases List.mem_flatMap.mp endpointMem with
    ⟨taggedEdge, taggedEdgeMem, translatedEndpointMem⟩
  rcases List.mem_flatMap.mp translatedEndpointMem with
    ⟨translate, translateMem, localEndpointMem⟩
  have metadataEdgeMem :
      taggedEdge ∈
        ((PeriodicCNF.incidencesWithMetadata formula).map
          CNFIncidence.edge).zipIdx := by
    rw [PeriodicCNF.incidencesWithMetadata_edges formula]
    exact taggedEdgeMem
  rw [List.zipIdx_map] at metadataEdgeMem
  rcases List.mem_map.mp metadataEdgeMem with
    ⟨taggedIncidence, taggedIncidenceMem, taggedEdgeEq⟩
  subst taggedEdge
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, translate⟩
  have occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula := by
    apply List.mem_flatMap.mpr
    refine ⟨taggedIncidence, taggedIncidenceMem, ?_⟩
    exact List.mem_map.mpr
      ⟨translate, translateMem, rfl⟩
  let routeEndpoint : CNFRouteEndpoint Variable :=
    ⟨occurrence, endpoint⟩
  have localCNFEndpointMem :
      routeEndpoint ∈ occurrence.endpoints formula := by
    unfold CNFRouteOccurrence.endpoints
    exact List.mem_map.mpr
      ⟨endpoint, localEndpointMem, rfl⟩
  exact
    ⟨routeEndpoint, occurrenceMem,
      localCNFEndpointMem, rfl⟩

/-- A metadata-rich endpoint is exactly the canonical source or target
terminal of its occurrence, according to its endpoint kind. -/
theorem CNFRouteEndpoint.terminal_eq_source_or_target
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {routeEndpoint : CNFRouteEndpoint Variable}
    (endpointMem :
      routeEndpoint ∈ routeEndpoint.occurrence.endpoints formula) :
    (routeEndpoint.endpoint.endKind = .source ∧
        routeEndpoint.endpoint.terminal =
          routeEndpoint.occurrence.sourceTerminal formula) ∨
      (routeEndpoint.endpoint.endKind = .target ∧
        routeEndpoint.endpoint.terminal =
          routeEndpoint.occurrence.targetTerminal formula) := by
  simp only [CNFRouteOccurrence.endpoints, List.mem_map] at endpointMem
  rcases endpointMem with
    ⟨endpoint, localEndpointMem, endpointEq⟩
  have endpointFieldEq :
      endpoint = routeEndpoint.endpoint :=
    congrArg CNFRouteEndpoint.endpoint endpointEq
  rw [← endpointFieldEq]
  unfold translatedEdgeRouteEndpoints at localEndpointMem
  generalize segmentsEq :
      (gridPolylineSegments
        (constructedEdgeRoute
          (PeriodicCNF.incidenceGraph formula)
          routeEndpoint.occurrence.edge
          routeEndpoint.occurrence.edgeIndex)).zipIdx = segments
    at localEndpointMem
  cases segments with
  | nil =>
      simp [routeEndpointsFromSegments] at localEndpointMem
  | cons first rest =>
      simp only [routeEndpointsFromSegments, List.mem_cons,
        List.not_mem_nil, or_false] at localEndpointMem
      rcases localEndpointMem with endpointEq | endpointEq
      · subst endpoint
        apply Or.inl
        constructor
        · exact congrArg RouteEndpoint.endKind endpointEq
        · rw [endpointEq]
          simp [CNFRouteOccurrence.sourceTerminal,
            CNFRouteOccurrence.taggedSegments, segmentsEq]
      · subst endpoint
        apply Or.inr
        constructor
        · exact congrArg RouteEndpoint.endKind endpointEq
        · rw [endpointEq]
          have defaultEq :
              (first :: rest).getLastD first =
                (first :: rest).getLastD
                  defaultTaggedGridSegment := by
            rw [List.getLastD_cons, List.getLastD_cons]
          simp only [CNFRouteOccurrence.targetTerminal,
            CNFRouteOccurrence.taggedSegments, segmentsEq]
          exact congrArg
            (fun last : GridSegment × Nat =>
              (⟨⟨routeEndpoint.occurrence.edgeIndex,
                    last.2, last.1⟩,
                  routeEndpoint.occurrence.translate,
                  .finish⟩ : SegmentTerminal))
            defaultEq

/-- A neighboring metadata occurrence whose lifted source is a given clause
site belongs to that site's routed occurrence list. -/
theorem CNFRouteOccurrence.mem_clauseRouteOccurrencesAt_of_mem_drawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula)
    (site : ClauseRouteSite)
    (siteEq : occurrence.clauseOccurrence = site) :
    occurrence ∈ clauseRouteOccurrencesAt formula site := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem,
      translatedOccurrenceMem⟩
  rcases List.mem_map.mp translatedOccurrenceMem with
    ⟨translate, translateMem, occurrenceEq⟩
  subst occurrence
  apply List.mem_map.mpr
  refine ⟨taggedIncidence, List.mem_filter.mpr
    ⟨taggedIncidenceMem, ?_⟩, ?_⟩
  · simpa [CNFRouteOccurrence.clauseOccurrence] using
      congrArg Prod.fst siteEq
  · have translateEq :
        translate = site.2 :=
      congrArg Prod.snd siteEq
    subst site
    rfl

/-- A neighboring metadata occurrence whose lifted target is a given
variable site belongs to that site's routed occurrence list. -/
theorem CNFRouteOccurrence.mem_variableRouteOccurrencesAt_of_mem_drawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula)
    (site : VariableRouteSite Variable)
    (siteEq : occurrence.variableOccurrence = site) :
    occurrence ∈ variableRouteOccurrencesAt formula site := by
  simp [variableRouteOccurrencesAt, occurrenceMem, siteEq]

/-- Overlap with a represented routed-variable macrocell forces incidence
to the target terminal of some route occurrence at that site. -/
theorem
    retainedDrawingCompleteCarrierLink_exists_targetOccurrence_of_variableMacrocell_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (site : VariableRouteSite Variable)
    {representedOccurrence : CNFRouteOccurrence Variable}
    (representedOccurrenceMem :
      representedOccurrence ∈
        variableRouteOccurrencesAt formula site)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) link)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) link)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2))) :
    ∃ occurrence,
      occurrence ∈ variableRouteOccurrencesAt formula site ∧
        CarrierLinkIncidentToTargetTerminal
          formula link occurrence := by
  let graph := PeriodicCNF.incidenceGraph formula
  have representedData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site representedOccurrenceMem
  have representedEdgeMem :=
    representedOccurrence.taggedEdge_mem
      formula representedData.1
  have representedTargetMem :
      representedOccurrence.edge.target ∈ graph.vertices :=
    (wellFormed.2 representedOccurrence.edge
      (List.fst_mem_of_mem_zipIdx representedEdgeMem)).2
  have siteVertexMem :
      (CNFVertex.variable site.1) ∈ graph.vertices := by
    have atomEq :
        representedOccurrence.variableOccurrence.1 = site.1 :=
      congrArg Prod.fst representedData.2
    rw [← atomEq]
    simpa [graph, CNFRouteOccurrence.edge,
      CNFRouteOccurrence.variableOccurrence] using
        representedTargetMem
  rcases
      retainedDrawingCompleteCarrierLink_incidentToTerminalAtLiftedVertex_of_macrocell_overlap
        wellFormed degree isLocal linkMem siteVertexMem site.2
        notSeparated with
    ⟨terminal, terminalMem, terminalPoint, linkIncident⟩
  rcases
      drawingSegmentTerminal_routeEndpoint_of_drawingPoint_eq_liftedVertex
        wellFormed degree isLocal terminalMem siteVertexMem site.2
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
    exact terminalEq.trans (congrArg RouteEndpoint.terminal endpointEq.symm)
  have occurrenceEdgeMem :=
    routeEndpoint.occurrence.taggedEdge_mem
      formula occurrenceMem
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
            (.variable site.1) site.2 := by
      rw [← sourcePoint, ← sourceData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have impossible :=
      liftedDrawingVertexPosition_eq
        graph sourceVertexMem siteVertexMem liftedEq
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
            (.variable site.1) site.2 := by
      rw [← targetPoint, ← targetData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have siteData :=
      liftedDrawingVertexPosition_eq
        graph targetVertexMem siteVertexMem liftedEq
    have occurrenceSiteEq :
        routeEndpoint.occurrence.variableOccurrence = site := by
      apply Prod.ext
      · exact CNFVertex.variable.inj siteData.1
      · exact siteData.2
    refine
      ⟨routeEndpoint.occurrence,
        routeEndpoint.occurrence
          |>.mem_variableRouteOccurrencesAt_of_mem_drawing
            formula occurrenceMem site occurrenceSiteEq,
        ?_⟩
    simpa [CarrierLinkIncidentToTargetTerminal,
      terminalEndpointEq, targetData.2] using linkIncident

/-- Overlap with a represented routed-clause macrocell forces incidence to
the source terminal of some route occurrence at that site. -/
theorem
    retainedDrawingCompleteCarrierLink_exists_sourceOccurrence_of_clauseMacrocell_overlap
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (site : ClauseRouteSite)
    {representedOccurrence : CNFRouteOccurrence Variable}
    (representedOccurrenceMem :
      representedOccurrence ∈
        clauseRouteOccurrencesAt formula site)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          (PeriodicCNF.incidenceGraph formula) link)
        (drawingCompleteCarrierLinkRectangleUpper
          (PeriodicCNF.incidenceGraph formula) link)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2))) :
    ∃ occurrence,
      occurrence ∈ clauseRouteOccurrencesAt formula site ∧
        CarrierLinkIncidentToSourceTerminal
          formula link occurrence := by
  let graph := PeriodicCNF.incidenceGraph formula
  have representedEdgeMem :
      (representedOccurrence.edge,
          representedOccurrence.edgeIndex) ∈ graph.edges.zipIdx := by
    rcases List.mem_map.mp representedOccurrenceMem with
      ⟨taggedIncidence, taggedIncidenceMem,
        occurrenceEq⟩
    subst representedOccurrence
    exact PeriodicCNF.tagged_incidence_edge_mem
      formula (List.mem_filter.mp taggedIncidenceMem).1
  have representedSourceMem :
      representedOccurrence.edge.source ∈ graph.vertices :=
    (wellFormed.2 representedOccurrence.edge
      (List.fst_mem_of_mem_zipIdx representedEdgeMem)).1
  have representedSiteEq :=
    clauseRouteOccurrencesAt_clauseOccurrence
      formula site representedOccurrenceMem
  have siteVertexMem :
      (CNFVertex.clause site.1) ∈ graph.vertices := by
    have clauseEq :
        representedOccurrence.clauseOccurrence.1 = site.1 :=
      congrArg Prod.fst representedSiteEq
    rw [← clauseEq]
    simpa [graph, CNFRouteOccurrence.edge,
      CNFRouteOccurrence.clauseOccurrence] using
        representedSourceMem
  rcases
      retainedDrawingCompleteCarrierLink_incidentToTerminalAtLiftedVertex_of_macrocell_overlap
        wellFormed degree isLocal linkMem siteVertexMem site.2
        notSeparated with
    ⟨terminal, terminalMem, terminalPoint, linkIncident⟩
  rcases
      drawingSegmentTerminal_routeEndpoint_of_drawingPoint_eq_liftedVertex
        wellFormed degree isLocal terminalMem siteVertexMem site.2
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
    exact terminalEq.trans (congrArg RouteEndpoint.terminal endpointEq.symm)
  have occurrenceEdgeMem :=
    routeEndpoint.occurrence.taggedEdge_mem
      formula occurrenceMem
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
            (.clause site.1) site.2 := by
      rw [← sourcePoint, ← sourceData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have siteData :=
      liftedDrawingVertexPosition_eq
        graph sourceVertexMem siteVertexMem liftedEq
    have occurrenceSiteEq :
        routeEndpoint.occurrence.clauseOccurrence = site := by
      apply Prod.ext
      · exact CNFVertex.clause.inj siteData.1
      · exact siteData.2
    refine
      ⟨routeEndpoint.occurrence,
        routeEndpoint.occurrence
          |>.mem_clauseRouteOccurrencesAt_of_mem_drawing
            formula occurrenceMem site occurrenceSiteEq,
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
            (.clause site.1) site.2 := by
      rw [← targetPoint, ← targetData.2,
        ← terminalEndpointEq]
      exact terminalPoint
    have impossible :=
      liftedDrawingVertexPosition_eq
        graph targetVertexMem siteVertexMem liftedEq
    cases impossible.1

end PeriodicOrthocrossing
end LeanTrominoes
