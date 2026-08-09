import LeanTrominoes.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Endpoint coverage in periodic CNF incidence drawings

Nonempty CNF clauses make every clause prototype incident, while variable
prototypes are listed only when they occur.  Exact compatible route
endpoints therefore cover every incidence-graph vertex by a genuine lifted
segment endpoint.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- In a compatible loopless drawing, every edge route has distinct
advertised endpoints and hence contains a genuine segment. -/
theorem edgeRoutesHaveSegments_of_compatible_of_loopless
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (loopless : EdgesAreLoopless graph) :
    EdgeRoutesHaveSegments graph drawing := by
  intro taggedEdge taggedEdgeMember
  have edgeMember : taggedEdge.1 ∈ graph.edges :=
    List.fst_mem_of_mem_zipIdx taggedEdgeMember
  have endpointMembers :=
    compatible.1.2 taggedEdge.1 edgeMember
  have sourcePositionMember :=
    compatible.vertexPosition_mem endpointMembers.1
  have targetPositionMember :=
    compatible.vertexPosition_mem endpointMembers.2
  have sourceBounds :=
    compatible.2.2.2.2.1
      (drawing.vertexPosition graph taggedEdge.1.source)
      sourcePositionMember
  have targetBounds :=
    compatible.2.2.2.2.1
      (drawing.vertexPosition graph taggedEdge.1.target)
      targetPositionMember
  have prototypePositionsDifferent :
      drawing.vertexPosition graph taggedEdge.1.source ≠
        drawing.vertexPosition graph taggedEdge.1.target := by
    intro equal
    exact
      loopless taggedEdge.1 edgeMember
        (compatible.vertexPosition_injective_on
          endpointMembers.1 endpointMembers.2 equal)
  have liftedEndpointsDifferent :
      drawing.vertexPosition graph taggedEdge.1.source ≠
        Cell.add
          (drawing.vertexPosition graph taggedEdge.1.target)
          (drawing.periodTranslation taggedEdge.1.offset) :=
    PositionedPeriodicCNF.fundamentalPosition_ne_translated
      drawing sourceBounds targetBounds prototypePositionsDifferent
  have endpoints :=
    compatible.2.2.2.2.2 taggedEdge taggedEdgeMember
  generalize
      drawing.edgeRoute taggedEdge.2 = route at endpoints ⊢
  cases route with
  | nil =>
      simp at endpoints
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [List.head?_singleton, List.getLast?_singleton,
            Option.some.injEq] at endpoints
          exact
            (liftedEndpointsDifferent
              (endpoints.1.symm.trans endpoints.2)).elim
      | cons second rest =>
          simp

/-- Every stored route of a compatible loopless drawing contains at least
one genuine segment.  This is the route-list form of
`edgeRoutesHaveSegments_of_compatible_of_loopless`, useful when downstream
geometry starts from a stored route rather than a graph edge. -/
theorem route_length_ge_two_of_compatible_of_loopless
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (loopless : EdgesAreLoopless graph)
    {route : List Cell}
    (routeMember : route ∈ drawing.edgeRoutes) :
    2 ≤ route.length := by
  rcases List.mem_iff_get.mp routeMember with
    ⟨routeIndex, routeLookup⟩
  have edgeIndexLt :
      routeIndex.val < graph.edges.length := by
    rw [← compatible.2.2.1]
    exact routeIndex.isLt
  let edgeIndex : Fin graph.edges.length :=
    ⟨routeIndex.val, edgeIndexLt⟩
  let edge := graph.edges.get edgeIndex
  have taggedEdgeMember :
      (edge, routeIndex.val) ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨edgeIndexLt, rfl⟩
  have routeLength :=
    edgeRoutesHaveSegments_of_compatible_of_loopless
      graph drawing compatible loopless
      (edge, routeIndex.val) taggedEdgeMember
  have selectedRouteEq :
      drawing.edgeRoute routeIndex.val = route := by
    unfold PeriodicGridDrawing.edgeRoute
    rw [List.getD_eq_getElem _ _ routeIndex.isLt]
    exact routeLookup
  simpa only [selectedRouteEq] using routeLength

/-- Global continuous-planarity and endpoint-contact certificates make every
stored route of a compatible loopless orthogonal drawing simple.  Compatibility
supplies the advertised route endpoints, while the open-fundamental-square
condition ensures that those endpoints remain distinct in the periodic lift. -/
theorem routesSimple_of_globalCertificates_of_compatible_of_loopless
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (loopless : EdgesAreLoopless graph)
    (continuous : drawing.IsContinuouslyPlanar)
    (endpointContacts : drawing.RoutePointsMeetOnlyAtEndpoints)
    (orthogonal : drawing.IsOrthogonal) :
    ∀ route ∈ drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro route routeMember
  rcases List.mem_iff_get.mp routeMember with
    ⟨routeIndex, routeLookup⟩
  have edgeIndexLt :
      routeIndex.val < graph.edges.length := by
    rw [← compatible.2.2.1]
    exact routeIndex.isLt
  let edgeIndex : Fin graph.edges.length :=
    ⟨routeIndex.val, edgeIndexLt⟩
  let edge := graph.edges.get edgeIndex
  have edgeMember : edge ∈ graph.edges :=
    List.get_mem graph.edges edgeIndex
  have taggedEdgeMember :
      (edge, routeIndex.val) ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨edgeIndexLt, rfl⟩
  have selectedRouteEq :
      drawing.edgeRoute routeIndex.val = route := by
    unfold PeriodicGridDrawing.edgeRoute
    rw [List.getD_eq_getElem _ _ routeIndex.isLt]
    exact routeLookup
  have endpoints :=
    compatible.2.2.2.2.2
      (edge, routeIndex.val) taggedEdgeMember
  rw [selectedRouteEq] at endpoints
  have endpointMembers := compatible.1.2 edge edgeMember
  have sourcePositionMember :=
    compatible.vertexPosition_mem endpointMembers.1
  have targetPositionMember :=
    compatible.vertexPosition_mem endpointMembers.2
  have sourceBounds :=
    compatible.2.2.2.2.1
      (drawing.vertexPosition graph edge.source)
      sourcePositionMember
  have targetBounds :=
    compatible.2.2.2.2.1
      (drawing.vertexPosition graph edge.target)
      targetPositionMember
  have prototypePositionsDifferent :
      drawing.vertexPosition graph edge.source ≠
        drawing.vertexPosition graph edge.target := by
    intro equal
    exact
      loopless edge edgeMember
        (compatible.vertexPosition_injective_on
          endpointMembers.1 endpointMembers.2 equal)
  have liftedEndpointsDifferent :
      drawing.vertexPosition graph edge.source ≠
        Cell.add
          (drawing.vertexPosition graph edge.target)
          (drawing.periodTranslation edge.offset) :=
    PositionedPeriodicCNF.fundamentalPosition_ne_translated
      drawing sourceBounds targetBounds prototypePositionsDifferent
  exact
    PeriodicGridDrawing.routeIsSimple_of_globalCertificates
      continuous endpointContacts routeMember
      (route_length_ge_two_of_compatible_of_loopless
        graph drawing compatible loopless routeMember)
      ((PeriodicGridDrawing.isOrthogonal_iff_routes drawing).1
        orthogonal route routeMember)
      endpoints.1 endpoints.2 liftedEndpointsDifferent

end PeriodicGridDrawing

namespace PeriodicCNF

/-- Incidence-graph protoedges always cross the variable/clause
bipartition, so they are loopless. -/
theorem incidenceGraph_edgesAreLoopless
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicGridDrawing.EdgesAreLoopless formula.incidenceGraph := by
  intro edge edgeMember
  simp only [incidenceGraph, List.mem_flatMap] at edgeMember
  rcases edgeMember with
    ⟨taggedClause, _, edgeMember⟩
  simp only [clauseIncidenceEdges, List.mem_map] at edgeMember
  rcases edgeMember with ⟨literal, _, rfl⟩
  intro equal
  cases equal

/-- If every clause contains a literal, every incidence-graph protovertex
is incident to a protoedge. -/
theorem incidenceGraph_everyVertexIncident
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PeriodicGridDrawing.EveryVertexIncident formula.incidenceGraph := by
  intro vertex vertexMember
  change
    vertex ∈
      incidenceVariableVertices formula ++
        incidenceClauseVertices formula at vertexMember
  rw [List.mem_append] at vertexMember
  rcases vertexMember with variableMember | clauseMember
  · simp only [incidenceVariableVertices, List.mem_map] at variableMember
    rcases variableMember with ⟨atom, atomMember, rfl⟩
    rw [List.mem_dedup] at atomMember
    unfold variableOccurrences at atomMember
    rcases List.mem_flatMap.mp atomMember with
      ⟨clause, clauseMember, atomMember⟩
    rcases List.mem_map.mp atomMember with
      ⟨literal, literalMember, atomEq⟩
    rcases List.mem_iff_get.mp clauseMember with
      ⟨clauseIndex, clauseAt⟩
    have taggedClauseMember :
        (clause, clauseIndex.val) ∈ formula.clauses.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨clauseIndex.isLt, clauseAt⟩
    let edge :=
      incidenceEdge clauseIndex.val (clauseAnchor clause) literal
    have edgeMember : edge ∈ formula.incidenceGraph.edges := by
      unfold incidenceGraph
      apply List.mem_flatMap.mpr
      refine ⟨(clause, clauseIndex.val), taggedClauseMember, ?_⟩
      exact List.mem_map.mpr
        ⟨literal, literalMember, rfl⟩
    rcases List.mem_iff_get.mp edgeMember with
      ⟨edgeIndex, edgeAt⟩
    have taggedEdgeMember :
        (edge, edgeIndex.val) ∈
          formula.incidenceGraph.edges.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨edgeIndex.isLt, edgeAt⟩
    refine ⟨(edge, edgeIndex.val), taggedEdgeMember, Or.inr ?_⟩
    simpa [edge, incidenceEdge] using atomEq
  · simp only [incidenceClauseVertices, List.mem_map] at clauseMember
    rcases clauseMember with
      ⟨clauseIndex, clauseIndexMember, rfl⟩
    have clauseIndexLt :
        clauseIndex < formula.clauses.length :=
      List.mem_range.mp clauseIndexMember
    have clauseMember :
        formula.clauses[clauseIndex] ∈ formula.clauses :=
      List.getElem_mem clauseIndexLt
    have nonempty : formula.clauses[clauseIndex] ≠ [] :=
      clausesNonempty formula.clauses[clauseIndex] clauseMember
    cases clauseEq : formula.clauses[clauseIndex] with
    | nil =>
        exact (nonempty clauseEq).elim
    | cons literal rest =>
      let edge :=
        incidenceEdge clauseIndex
          (clauseAnchor (literal :: rest)) literal
      have taggedClauseMember :
          (literal :: rest, clauseIndex) ∈
            formula.clauses.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨clauseIndexLt, clauseEq⟩
      have edgeMember : edge ∈ formula.incidenceGraph.edges := by
        unfold incidenceGraph
        apply List.mem_flatMap.mpr
        refine ⟨(literal :: rest, clauseIndex),
          taggedClauseMember, ?_⟩
        exact List.mem_map.mpr
          ⟨literal, by simp, rfl⟩
      rcases List.mem_iff_get.mp edgeMember with
        ⟨edgeIndex, edgeAt⟩
      have taggedEdgeMember :
          (edge, edgeIndex.val) ∈
            formula.incidenceGraph.edges.zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨edgeIndex.isLt, edgeAt⟩
      exact
        ⟨(edge, edgeIndex.val), taggedEdgeMember,
          Or.inl rfl⟩

/-- A compatible periodic CNF incidence drawing covers all of its stored
vertex positions by lifted segment endpoints when clauses are nonempty. -/
theorem incidenceDrawing_vertexPositionsCoveredBySegmentEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible formula.incidenceGraph)
    (clausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    drawing.VertexPositionsCoveredBySegmentEndpoints := by
  exact
    PeriodicGridDrawing.vertexPositionsCoveredBySegmentEndpoints_of_compatible
      formula.incidenceGraph drawing compatible
      (incidenceGraph_everyVertexIncident formula clausesNonempty)
      (PeriodicGridDrawing.edgeRoutesHaveSegments_of_compatible_of_loopless
        formula.incidenceGraph drawing compatible
        (incidenceGraph_edgesAreLoopless formula))

end PeriodicCNF
end LeanTrominoes
