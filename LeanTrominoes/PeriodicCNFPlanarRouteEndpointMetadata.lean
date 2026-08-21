/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarIncidences

/-! # Recovering CNF metadata from generic route endpoints -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Every generic incidence-graph route endpoint has a metadata-rich CNF
endpoint carrying the same geometric record. -/
theorem drawingRouteEndpoint_exists_metadataEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {endpoint : RouteEndpoint (CNFVertex Variable)}
    (endpointMem : endpoint ∈ drawingRouteEndpoints
      (PeriodicCNF.incidenceGraph formula)) :
    ∃ routeEndpoint : CNFRouteEndpoint Variable,
      routeEndpoint.occurrence ∈ drawingCNFRouteOccurrences formula ∧
        routeEndpoint ∈ routeEndpoint.occurrence.endpoints formula ∧
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
    exact List.mem_map.mpr ⟨translate, translateMem, rfl⟩
  let routeEndpoint : CNFRouteEndpoint Variable :=
    ⟨occurrence, endpoint⟩
  have localCNFEndpointMem :
      routeEndpoint ∈ occurrence.endpoints formula := by
    unfold CNFRouteOccurrence.endpoints
    exact List.mem_map.mpr ⟨endpoint, localEndpointMem, rfl⟩
  exact ⟨routeEndpoint, occurrenceMem, localCNFEndpointMem, rfl⟩

/-- A metadata-rich endpoint is the canonical source or target terminal of
its occurrence, according to its endpoint kind. -/
theorem CNFRouteEndpoint.terminal_eq_source_or_target_metadata
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
  have endpointFieldEq : endpoint = routeEndpoint.endpoint :=
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

end LeanTrominoes.PeriodicOrthocrossing
