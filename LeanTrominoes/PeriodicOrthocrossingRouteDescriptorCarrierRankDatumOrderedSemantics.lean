/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumInjectiveSemantics

/-! # Exact route-descriptor carrier bits from strict order alone -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Because the numeric datum retains exact finite node identity, strict
per-key coordinate order is the only remaining semantic invariant needed to
identify the datum-only target with the exact carrier bit block. -/
theorem routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod_eq_of_ordered
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period
        (routeDescriptorRetainedCarrierNodesAtPeriod
          period descriptors) key).Pairwise fun first second =>
            carrierNodeOrderCoordinateAtPeriod period first <
              carrierNodeOrderCoordinateAtPeriod period second) :
    routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod
        period descriptors key =
      routeDescriptorRetainedCarrierPairBitsAtPeriod
        period descriptors key := by
  apply
    routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod_eq_of_injectiveOn
  · intro first firstMember second secondMember equal
    exact carrierNodeRankDatumAtPeriod_injective period equal
  · exact ordered

end LeanTrominoes.PeriodicOrthocrossing
