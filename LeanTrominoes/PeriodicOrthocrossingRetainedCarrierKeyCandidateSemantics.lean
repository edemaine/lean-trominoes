/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierKeyCandidateData

/-! # Semantics of the retained carrier-key candidate stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Mapping the two endpoint terminals of every occurrence to carrier keys
gives exactly the duplicated neighboring-key prefix. -/
theorem drawingSegmentTerminal_carrierKeys_eq_candidates
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawingSegmentTerminals graph).map SegmentTerminal.carrierKey =
      retainedTerminalCarrierKeys graph := by
  unfold drawingSegmentTerminals retainedTerminalCarrierKeys
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro occurrence _occurrenceMember
  simp [occurrenceTerminals, occurrenceCarrierKey,
    SegmentTerminal.carrierKey]

/-- The retained node enumeration projects to the explicit terminal-then-
crossing candidate key stream. -/
theorem retainedDrawingCarrierNode_keys_eq_candidates
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (retainedDrawingCarrierNodes graph).map CarrierNode.carrierKey =
      retainedCarrierKeyCandidates graph := by
  unfold retainedDrawingCarrierNodes retainedCarrierKeyCandidates
    retainedCrossingCarrierKeys
  rw [List.map_append, List.map_map, List.map_map]
  change
    (drawingSegmentTerminals graph).map SegmentTerminal.carrierKey ++
        (retainedCrossingBoundaries graph).map
          CrossingBoundary.carrierKey =
      retainedTerminalCarrierKeys graph ++
        (retainedCrossingBoundaries graph).map
          CrossingBoundary.carrierKey
  rw [drawingSegmentTerminal_carrierKeys_eq_candidates]

/-- The opaque retained key list is exactly last-occurrence deduplication of
the explicit terminal and crossing candidate streams. -/
theorem retainedDrawingCompleteCarrierKeys_eq_candidate_dedup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedDrawingCompleteCarrierKeys graph =
      (retainedCarrierKeyCandidates graph).dedup := by
  unfold retainedDrawingCompleteCarrierKeys
  rw [retainedDrawingCarrierNode_keys_eq_candidates]

/-- Restricting to relevant neighboring keys is therefore exactly a final
membership filter after last-occurrence deduplication of the candidate
stream. -/
theorem retainedNeighboringCarrierKeys_eq_candidate_dedup_filter
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedNeighboringCarrierKeys graph =
      (retainedCarrierKeyCandidates graph).dedup.filter fun key =>
        key ∈ neighboringCarrierKeys graph := by
  unfold retainedNeighboringCarrierKeys
  rw [retainedDrawingCompleteCarrierKeys_eq_candidate_dedup]

end LeanTrominoes.PeriodicOrthocrossing
