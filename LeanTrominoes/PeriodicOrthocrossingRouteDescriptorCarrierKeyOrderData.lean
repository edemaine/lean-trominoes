/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyOrderData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Exact retained carrier-key order over route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Stable retained carrier-key order reconstructed only from a route-
descriptor stream and an explicit drawing period. -/
def routeDescriptorRetainedCarrierKeysAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List (Nat × Nat × Cell) :=
  retainedCarrierKeysOfOccurrencesAndPairs
    (routeDescriptorNeighborOccurrences descriptors)
    (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
      period descriptors)

end LeanTrominoes.PeriodicOrthocrossing
