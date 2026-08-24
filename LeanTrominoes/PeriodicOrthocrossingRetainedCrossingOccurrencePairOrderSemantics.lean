/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCrossingRecordSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingPairOrder

/-! # Exact occurrence-pair order of retained crossings -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The semantic retained crossing list is exactly the graph-free record scan
over canonical occurrence pairs at the graph's drawing period. -/
theorem retainedCrossings_eq_occurrencePairRecordScan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedCrossings graph =
      occurrencePairRetainedCrossingRecordScanAtPeriod
        (drawingGridSize graph)
        (orientedCrossingOccurrencePairs graph) := by
  rw [occurrencePairRetainedCrossingRecordScanAtPeriod_drawingGridSize]
  unfold retainedCrossings
  rw [orientedCrossings_eq_orientedCrossingPairFilter,
    orientedCrossingPairFilter_eq_map_occurrencePairs,
    List.flatMap_map]

end LeanTrominoes.PeriodicOrthocrossing
