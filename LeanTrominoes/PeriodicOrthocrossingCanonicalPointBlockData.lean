/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairs

/-! # Point blocks of the canonical oriented crossing scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Crossing record obtained from an occurrence pair and an explicit point. -/
def occurrencePairCrossingAtPoint
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (point : Cell) : CrossingRecord :=
  ⟨pair.1.1, pair.1.2, pair.2.1, pair.2.2, point⟩

/-- The original point-grid candidates of one occurrence pair, after both
canonical and horizontal-first filters. -/
def canonicalOrientedPointBlock
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : List CrossingRecord :=
  (((fundamentalPoints graph).map
      (occurrencePairCrossingAtPoint pair)).filter fun record =>
        record.IsCanonical graph).filter fun record =>
          (record.firstSegment graph).IsHorizontal

end LeanTrominoes.PeriodicOrthocrossing
