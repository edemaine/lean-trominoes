/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Retained carrier-key scan over route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Fixed retained-key expansion of the accepted route-descriptor crossing
pairs at an explicit drawing period. -/
def routeDescriptorRetainedCarrierKeyScanAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List (Nat × Nat × Cell) :=
  occurrencePairCarrierKeyScan
    (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
      period descriptors)

end LeanTrominoes.PeriodicOrthocrossing
