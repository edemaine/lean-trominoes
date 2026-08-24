/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairSingletonScanSemantics

/-! # Exact occurrence-pair order of canonical oriented crossings -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The direct filtered occurrence-pair crossing scan has no duplicates. -/
theorem orientedCrossingPairFilter_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (orientedCrossingPairFilter graph).Nodup := by
  unfold orientedCrossingPairFilter
  exact ((crossingHaloCandidates_nodup graph).filter _).filter _

/-- The original fundamental-point enumeration and the direct unique-
intersection occurrence-pair enumeration have exactly the same order. -/
theorem orientedCrossings_eq_orientedCrossingPairFilter
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    orientedCrossings graph = orientedCrossingPairFilter graph := by
  rw [orientedCrossings_eq_pointBlock_dedup,
    canonicalPointBlockNestedScan_eq_singletonScan,
    canonicalOrientedOccurrencePairSingletonScan_eq_pairFilter]
  exact List.dedup_eq_self.mpr
    (orientedCrossingPairFilter_nodup graph)

end LeanTrominoes.PeriodicOrthocrossing
