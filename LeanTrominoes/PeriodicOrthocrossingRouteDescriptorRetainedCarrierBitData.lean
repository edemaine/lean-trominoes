/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierBitData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Retained carrier-link bits reconstructed from route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Exact retained terminal-and-crossing carrier-node stream reconstructed
solely from a numeric period and route descriptors. -/
def routeDescriptorRetainedCarrierNodesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List CarrierNode :=
  retainedCarrierNodesOfOccurrencesAndPairsAtPeriod period
    (routeDescriptorNeighborOccurrences descriptors)
    (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
      period descriptors)

/-- Ordered representative carrier-link axis and next-slice bits for one key,
computed solely from a numeric period and route descriptors. -/
def routeDescriptorRetainedCarrierPairBitsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  retainedRepresentativeCarrierPairBitsAtPeriod period
    (routeDescriptorRetainedCarrierNodesAtPeriod period descriptors) key

end LeanTrominoes.PeriodicOrthocrossing
