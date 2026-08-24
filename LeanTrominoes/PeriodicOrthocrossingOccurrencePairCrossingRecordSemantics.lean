/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingRecordData

/-! # Semantics of occurrence-pair crossing records -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- At a graph's exact drawing period, graph-free reconstruction is the
semantic crossing candidate allocated from the same occurrence pair. -/
theorem occurrencePairCrossingRecordAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    occurrencePairCrossingRecordAtPeriod
        (drawingGridSize graph) pair =
      orientedCrossingCandidate graph pair.1 pair.2 := by
  simp [occurrencePairCrossingRecordAtPeriod,
    orientedCrossingCandidate, occurrenceSegmentAtPeriod,
    PeriodicGridDrawing.periodTranslation, drawing_gridSize]

end LeanTrominoes.PeriodicOrthocrossing
