/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumTargetSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumData

/-! # Exact route-descriptor semantics of datum-only carrier scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Once duplicate-freedom and strict coordinate order are supplied for the
route-descriptor node stream, its datum-only scan is the exact established
route-descriptor carrier bit target. -/
theorem routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod_eq
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell)
    (nodesNodup :
      (routeDescriptorRetainedCarrierNodesAtPeriod
        period descriptors).Nodup)
    (datumsNodup :
      (routeDescriptorCarrierRankDatumsAtPeriod
        period descriptors).Nodup)
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
  unfold routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod
    routeDescriptorCarrierRankDatumsAtPeriod
    routeDescriptorRetainedCarrierPairBitsAtPeriod
  exact retainedCarrierRankDatumBits_map_eq_target
    period
    (routeDescriptorRetainedCarrierNodesAtPeriod period descriptors)
    key nodesNodup datumsNodup ordered

end LeanTrominoes.PeriodicOrthocrossing
