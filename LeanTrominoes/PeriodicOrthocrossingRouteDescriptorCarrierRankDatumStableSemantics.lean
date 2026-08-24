/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumStableScanSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumData

/-! # Unconditional route-descriptor semantics of stable datum scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The datum-only stable-rank target is exactly the established
route-descriptor carrier bit block, with no ordering or duplicate-freedom
hypotheses. -/
theorem routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod_eq_unconditionally
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell) :
    routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod
        period descriptors key =
      routeDescriptorRetainedCarrierPairBitsAtPeriod
        period descriptors key := by
  unfold routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod
    routeDescriptorCarrierRankDatumsAtPeriod
    routeDescriptorRetainedCarrierPairBitsAtPeriod
  exact retainedCarrierRankDatumBits_map_eq_complete
    period
    (routeDescriptorRetainedCarrierNodesAtPeriod period descriptors)
    key

end LeanTrominoes.PeriodicOrthocrossing
