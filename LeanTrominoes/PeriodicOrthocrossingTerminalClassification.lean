/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarBends
import LeanTrominoes.PeriodicOrthocrossingPlanarEndpoints
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteSoundness

/-! # Classifying finite route terminals -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The two endpoint terminals of every segment in a route tail, retaining
the route's segment indices. -/
private def routeSegmentTerminalsAuxClassify
    (routeIndex : Nat) (translate : Cell) :
    Nat → List Cell → List SegmentTerminal
  | startIndex, first :: second :: rest =>
      [⟨⟨routeIndex, startIndex, ⟨first, second⟩⟩,
          translate, .start⟩,
        ⟨⟨routeIndex, startIndex, ⟨first, second⟩⟩,
          translate, .finish⟩] ++
      routeSegmentTerminalsAuxClassify routeIndex translate
        (startIndex + 1) (second :: rest)
  | _, _ => []

/-- The recursive terminal enumeration agrees with flattening the indexed
polyline segments into their two occurrence terminals. -/
private theorem routeSegmentTerminalsAuxClassify_eq
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat),
      routeSegmentTerminalsAuxClassify
          routeIndex translate startIndex points =
        ((gridPolylineSegments points).zipIdx startIndex).flatMap
          (fun taggedSegment =>
            occurrenceTerminals
              (⟨routeIndex, taggedSegment.2, taggedSegment.1⟩,
                translate)) := by
  intro points
  induction points with
  | nil =>
      intro startIndex
      simp [routeSegmentTerminalsAuxClassify, gridPolylineSegments]
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex
          simp [routeSegmentTerminalsAuxClassify, gridPolylineSegments]
      | cons second rest =>
          intro startIndex
          simp only [routeSegmentTerminalsAuxClassify,
            gridPolylineSegments, List.zipIdx_cons,
            List.flatMap_cons, occurrenceTerminals]
          rw [induction (startIndex + 1)]
          simp only [occurrenceTerminals]

/-- Every terminal of a route tail is either attached to one of its
enumerated bends or is one of the two external endpoints of that tail. -/
private theorem routeSegmentTerminal_bend_or_endpoint_classify
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex)
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      {terminal : SegmentTerminal},
      terminal ∈ routeSegmentTerminalsAuxClassify
          routeIndex translate startIndex points →
        (∃ routeBend,
            routeBend ∈
                routeBendsAux
                  routeIndex translate startIndex points ∧
              (terminal = routeBend.incomingTerminal ∨
                terminal = routeBend.outgoingTerminal)) ∨
          ∃ endpoint,
            endpoint ∈
                routeEndpointsFromSegments edge routeIndex translate
                  ((gridPolylineSegments points).zipIdx startIndex) ∧
              terminal = endpoint.terminal := by
  intro points
  induction points with
  | nil =>
      intro startIndex terminal terminalMem
      simp [routeSegmentTerminalsAuxClassify] at terminalMem
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro startIndex terminal terminalMem
          simp [routeSegmentTerminalsAuxClassify] at terminalMem
      | cons second rest =>
          cases rest with
          | nil =>
              intro startIndex terminal terminalMem
              change
                terminal ∈
                  [⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .start⟩,
                    ⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .finish⟩] ++
                    routeSegmentTerminalsAuxClassify routeIndex translate
                      (startIndex + 1) [second] at terminalMem
              simp only [routeSegmentTerminalsAuxClassify,
                List.append_nil, List.mem_cons,
                List.not_mem_nil, or_false] at terminalMem
              rcases terminalMem with terminalEq | terminalEq <;>
                rw [terminalEq]
              · apply Or.inr
                refine
                  ⟨⟨edge, routeIndex, translate, .source,
                      ⟨⟨routeIndex, startIndex,
                          ⟨first, second⟩⟩,
                        translate, .start⟩⟩, ?_, rfl⟩
                simp [gridPolylineSegments,
                  routeEndpointsFromSegments]
              · apply Or.inr
                refine
                  ⟨⟨edge, routeIndex, translate, .target,
                      ⟨⟨routeIndex, startIndex,
                          ⟨first, second⟩⟩,
                        translate, .finish⟩⟩, ?_, rfl⟩
                simp [gridPolylineSegments,
                  routeEndpointsFromSegments]
          | cons third tail =>
              intro startIndex terminal terminalMem
              change
                terminal ∈
                  [⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .start⟩,
                    ⟨⟨routeIndex, startIndex,
                      ⟨first, second⟩⟩,
                    translate, .finish⟩] ++
                    routeSegmentTerminalsAuxClassify routeIndex translate
                      (startIndex + 1) (second :: third :: tail)
                  at terminalMem
              rw [List.mem_append] at terminalMem
              rcases terminalMem with firstMem | tailMem
              · simp only [List.mem_cons, List.not_mem_nil,
                  or_false] at firstMem
                rcases firstMem with terminalEq | terminalEq
                · rw [terminalEq]
                  apply Or.inr
                  refine
                    ⟨⟨edge, routeIndex, translate, .source,
                        ⟨⟨routeIndex, startIndex,
                            ⟨first, second⟩⟩,
                          translate, .start⟩⟩, ?_, rfl⟩
                  simp [gridPolylineSegments,
                    routeEndpointsFromSegments]
                · rw [terminalEq]
                  apply Or.inl
                  refine
                    ⟨⟨routeIndex, startIndex, translate,
                        first, second, third⟩, ?_, Or.inl rfl⟩
                  simp [routeBendsAux]
              · rcases induction (startIndex + 1) tailMem with
                  tailBend | tailEndpoint
                · rcases tailBend with
                    ⟨routeBend, routeBendMem, terminalEq⟩
                  apply Or.inl
                  refine
                    ⟨routeBend, List.mem_cons_of_mem _ routeBendMem,
                      terminalEq⟩
                · rcases tailEndpoint with
                    ⟨endpoint, endpointMem, terminalEq⟩
                  simp only [gridPolylineSegments,
                    List.zipIdx_cons,
                    routeEndpointsFromSegments,
                    List.mem_cons, List.not_mem_nil,
                    or_false] at endpointMem
                  rcases endpointMem with endpointEq | endpointEq
                  · subst endpoint
                    rw [terminalEq]
                    apply Or.inl
                    refine
                      ⟨⟨routeIndex, startIndex, translate,
                          first, second, third⟩,
                        by simp [routeBendsAux],
                        Or.inr ?_⟩
                    rfl
                  · subst endpoint
                    rw [terminalEq]
                    apply Or.inr
                    refine
                      ⟨⟨edge, routeIndex, translate, .target,
                          ((gridPolylineSegments
                              (first :: second :: third :: tail)).zipIdx
                            startIndex).getLastD
                              (⟨first, second⟩, startIndex)
                            |> fun taggedSegment =>
                              ⟨⟨routeIndex, taggedSegment.2,
                                  taggedSegment.1⟩,
                                translate, .finish⟩⟩,
                        ?_, ?_⟩
                    · simp [gridPolylineSegments,
                        routeEndpointsFromSegments]
                    · simp only [gridPolylineSegments,
                        List.zipIdx_cons, List.getLastD_cons]

/-- Globally, every enumerated segment terminal is either an internal bend
terminal or an external route endpoint. -/
theorem drawingSegmentTerminal_bend_or_routeEndpoint_classify
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals graph) :
    (∃ routeBend,
        routeBend ∈ drawingRouteBends graph ∧
          (terminal = routeBend.incomingTerminal ∨
            terminal = routeBend.outgoingTerminal)) ∨
      ∃ endpoint,
        endpoint ∈ drawingRouteEndpoints graph ∧
          terminal = endpoint.terminal := by
  rcases List.mem_flatMap.mp terminalMem with
    ⟨occurrence, occurrenceMem, terminalInOccurrence⟩
  have occurrenceData :=
    (mem_neighborOccurrences_iff graph occurrence).mp occurrenceMem
  rcases occurrence with ⟨indexed, translate⟩
  simp only [occurrenceTerminals, List.mem_cons,
    List.not_mem_nil, or_false] at terminalInOccurrence
  rcases terminalInOccurrence with terminalEq | terminalEq
  all_goals
    rcases List.mem_flatMap.mp occurrenceData.1 with
      ⟨taggedRoute, taggedRouteMem, indexedInRoute⟩
    rcases List.mem_map.mp indexedInRoute with
      ⟨taggedSegment, taggedSegmentMem, indexedEq⟩
    have edgeIndexLt : taggedRoute.2 < graph.edges.length := by
      have routeIndexLt :=
        List.snd_lt_of_mem_zipIdx taggedRouteMem
      simpa [drawing, constructedEdgeRoutes] using routeIndexLt
    let edge : PeriodicEdge Vertex :=
      graph.edges[taggedRoute.2]'edgeIndexLt
    have edgeMem :
        (edge, taggedRoute.2) ∈ graph.edges.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨edgeIndexLt, rfl⟩
    have constructedRouteMem :=
      constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
        graph edgeMem
    have taggedRouteEq :
        taggedRoute =
          (constructedEdgeRoute graph edge taggedRoute.2,
            taggedRoute.2) :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        taggedRouteMem constructedRouteMem rfl
    have taggedRouteFirstEq :
        taggedRoute.1 =
          constructedEdgeRoute graph edge taggedRoute.2 :=
      congrArg Prod.fst taggedRouteEq
    rw [taggedRouteFirstEq] at taggedSegmentMem
    have indexedEq' :
        (⟨taggedRoute.2, taggedSegment.2,
            taggedSegment.1⟩ : IndexedGridSegment) = indexed := by
      simpa using indexedEq
    have localTerminalMem :
        terminal ∈
          routeSegmentTerminalsAuxClassify
            taggedRoute.2 translate 0
            (constructedEdgeRoute graph edge taggedRoute.2) := by
      rw [terminalEq, ← indexedEq',
        routeSegmentTerminalsAuxClassify_eq]
      apply List.mem_flatMap.mpr
      refine ⟨taggedSegment, ?_, ?_⟩
      · exact taggedSegmentMem
      · simp [occurrenceTerminals]
    rcases routeSegmentTerminal_bend_or_endpoint_classify
        edge taggedRoute.2 translate
        (constructedEdgeRoute graph edge taggedRoute.2) 0
        localTerminalMem with
      localBend | localEndpoint
    · rcases localBend with
        ⟨routeBend, routeBendMem, terminalEq⟩
      apply Or.inl
      refine ⟨routeBend, ?_, terminalEq⟩
      apply List.mem_flatMap.mpr
      refine
        ⟨(constructedEdgeRoute graph edge taggedRoute.2,
            taggedRoute.2), constructedRouteMem, ?_⟩
      apply List.mem_flatMap.mpr
      exact
        ⟨translate,
          (mem_neighborTranslations_iff translate).mpr
            occurrenceData.2,
          routeBendMem⟩
    · rcases localEndpoint with
        ⟨endpoint, endpointMem, terminalEq⟩
      apply Or.inr
      refine ⟨endpoint, ?_, terminalEq⟩
      apply List.mem_flatMap.mpr
      refine ⟨(edge, taggedRoute.2), edgeMem, ?_⟩
      apply List.mem_flatMap.mpr
      exact
        ⟨translate,
          (mem_neighborTranslations_iff translate).mpr
            occurrenceData.2,
          endpointMem⟩

end LeanTrominoes.PeriodicOrthocrossing
