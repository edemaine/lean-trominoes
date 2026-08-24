/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeNeighbor

/-! # Neighboring segment occurrences of retained carrier representatives -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Period normalization preserves the indexed segment selected by a
crossing-boundary side. -/
private theorem CrossingBoundary.periodNormalize_indexed_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (boundary : CrossingBoundary) :
    (boundary.periodNormalize graph).indexed = boundary.indexed := by
  rcases boundary with ⟨crossing, side⟩
  cases side <;> rfl

/-- The carrier key of every selected retained link occurs in the exact
neighboring segment-occurrence key stream. -/
theorem retainedDrawingCompleteCarrierLink_key_mem_neighborOccurrences
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {link : EqualityLink CarrierNode}
    (linkMember : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    link.first.carrierKey ∈
      (neighborOccurrences graph).map fun occurrence =>
        PeriodicGridDrawing.SegmentOccurrenceKey
          occurrence.1 occurrence.2 := by
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMember
  have keyNeighbor :=
    retainedDrawingCompleteCarrierLink_key_translate_neighbor linkMember
  cases firstEq : link.first with
  | boundary boundary =>
      have boundaryMember :
          boundary ∈ retainedCrossingBoundaries graph := by
        rw [firstEq] at endpoints
        unfold retainedDrawingCarrierNodes at endpoints
        simpa using endpoints.1
      have normalizedMember :=
        retainedCrossingBoundary_periodNormalize_mem graph boundaryMember
      have indexedMember :=
        (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
          graph normalizedMember).1
      rw [CrossingBoundary.periodNormalize_indexed_eq] at indexedMember
      have translateNeighbor : IsNeighborTranslation boundary.translate := by
        simpa [firstEq, CarrierNode.carrierKey,
          CrossingBoundary.carrierKey_eq_indexed_translate,
          PeriodicGridDrawing.SegmentOccurrenceKey] using keyNeighbor
      have occurrenceMember :
          (boundary.indexed, boundary.translate) ∈
            neighborOccurrences graph :=
        (mem_neighborOccurrences_iff graph _).mpr
          ⟨indexedMember, translateNeighbor⟩
      apply List.mem_map.mpr
      refine ⟨(boundary.indexed, boundary.translate), occurrenceMember, ?_⟩
      simp [CarrierNode.carrierKey,
        CrossingBoundary.carrierKey_eq_indexed_translate]
  | terminal terminal =>
      have terminalMember : terminal ∈ drawingSegmentTerminals graph := by
        rw [firstEq] at endpoints
        unfold retainedDrawingCarrierNodes at endpoints
        simpa using endpoints.1
      have occurrenceMember :
          (terminal.indexed, terminal.translate) ∈
            neighborOccurrences graph := by
        unfold drawingSegmentTerminals at terminalMember
        rcases List.mem_flatMap.mp terminalMember with
          ⟨occurrence, occurrenceMember, terminalMember⟩
        simp only [occurrenceTerminals, List.mem_cons,
          List.not_mem_nil, or_false] at terminalMember
        rcases terminalMember with terminalEq | terminalEq <;>
          subst terminal <;> exact occurrenceMember
      apply List.mem_map.mpr
      refine ⟨(terminal.indexed, terminal.translate), occurrenceMember, ?_⟩
      simp [CarrierNode.carrierKey,
        SegmentTerminal.carrierKey]

end LeanTrominoes.PeriodicOrthocrossing
