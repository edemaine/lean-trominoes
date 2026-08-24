/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPointBlockFactorization

/-! # Singleton scan for canonical occurrence pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The singleton-or-empty crossing block selected by one occurrence pair. -/
def canonicalOrientedOccurrencePairSingletonBlock
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) : List CrossingRecord :=
  if canonicalOrientedOccurrencePair graph pair then
    [orientedCrossingCandidate graph pair.1 pair.2]
  else []

/-- Product-order singleton scan of every neighboring occurrence pair. -/
def canonicalOrientedOccurrencePairSingletonScan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  (neighborOccurrences graph ×ˢ neighborOccurrences graph).flatMap
    (canonicalOrientedOccurrencePairSingletonBlock graph)

end LeanTrominoes.PeriodicOrthocrossing
