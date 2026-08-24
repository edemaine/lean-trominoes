/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierKeyCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingCarrierKeyScanSemantics

/-! # Exact retained carrier-key scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The retained key candidates are the duplicated terminal-key prefix
followed by the explicit crossing-major retained key scan. -/
theorem retainedCarrierKeyCandidates_eq_scan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedCarrierKeyCandidates graph =
      retainedTerminalCarrierKeys graph ++
        retainedCrossingCarrierKeyScan graph := by
  unfold retainedCarrierKeyCandidates
  rw [retainedCrossingCarrierKeys_eq_scan]

/-- Exact last-occurrence presentation of the relevant retained carrier-key
order using only terminal and crossing scan blocks. -/
theorem retainedNeighboringCarrierKeys_eq_scan_dedup_filter
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedNeighboringCarrierKeys graph =
      (retainedTerminalCarrierKeys graph ++
          retainedCrossingCarrierKeyScan graph).dedup.filter fun key =>
        key ∈ neighboringCarrierKeys graph := by
  rw [retainedNeighboringCarrierKeys_eq_candidate_dedup_filter,
    retainedCarrierKeyCandidates_eq_scan]

end LeanTrominoes.PeriodicOrthocrossing
