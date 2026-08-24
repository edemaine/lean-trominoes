/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingCarrierKeyScanData
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairs

/-! # Retained carrier-key scan over canonical occurrence pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Retained crossing-key block reconstructed from one accepted neighboring
occurrence pair. -/
def occurrencePairRetainedCarrierKeyBlock
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : List (Nat × Nat × Cell) :=
  retainedCrossingCarrierKeyBlock graph
    (orientedCrossingCandidate graph pair.1 pair.2)

/-- Accepted-pair-major retained carrier-key stream. -/
def occurrencePairRetainedCarrierKeyScan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  (orientedCrossingOccurrencePairs graph).flatMap
    (occurrencePairRetainedCarrierKeyBlock graph)

end LeanTrominoes.PeriodicOrthocrossing
