/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairLinearCrossing

/-! # Linearized crossing-pair lists for route-descriptor pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Pair-local canonical crossing occurrences expressed through the oriented
linear predicate, preserving the row-major occurrence-pair order. -/
def routeDescriptorPairLinearCrossingOccurrencePairsAtPeriod
    (period : Nat) (pair : RouteDescriptor × RouteDescriptor) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  (pair.1.selfIndexedNeighborOccurrences ×ˢ
      pair.2.selfIndexedNeighborOccurrences).filter
    (canonicalOrientedOccurrencePairLinearAtPeriod period)

end LeanTrominoes.PeriodicOrthocrossing
