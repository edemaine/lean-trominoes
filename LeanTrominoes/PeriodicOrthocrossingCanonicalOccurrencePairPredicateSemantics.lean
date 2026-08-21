/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateData

/-! # Correctness of the graph-free occurrence-pair predicate -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The semantic graph predicate depends on the graph only through its numeric
drawing period. -/
theorem canonicalOrientedOccurrencePair_eq_atPeriod
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    canonicalOrientedOccurrencePair graph pair =
      canonicalOrientedOccurrencePairAtPeriod
        (drawingGridSize graph) pair := by
  simp only [canonicalOrientedOccurrencePair,
    canonicalOrientedOccurrencePairAtPeriod,
    orientedCrossingCandidate, occurrenceSegmentAtPeriod,
    CrossingRecord.IsCanonical, CrossingRecord.firstSegment,
    CrossingRecord.secondSegment, InFundamentalDrawingSquare,
    PeriodicGridDrawing.periodTranslation, drawing_gridSize]
  rfl

end PeriodicOrthocrossing
end LeanTrominoes
