/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPointBlockScanSemantics
import LeanTrominoes.ListFlatMapSingletonIf

/-! # Semantics of the canonical occurrence-pair singleton scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The singleton-block occurrence-pair scan is exactly the existing
dedup-free canonical oriented crossing filter, including its order. -/
theorem canonicalOrientedOccurrencePairSingletonScan_eq_pairFilter
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    canonicalOrientedOccurrencePairSingletonScan graph =
      orientedCrossingPairFilter graph := by
  unfold canonicalOrientedOccurrencePairSingletonScan
    canonicalOrientedOccurrencePairSingletonBlock
  rw [flatMap_singleton_if_eq_filter_map]
  exact (orientedCrossingPairFilter_eq_map_occurrencePairs graph).symm

end LeanTrominoes.PeriodicOrthocrossing
