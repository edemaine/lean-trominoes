/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumBitScanSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumScanInjectiveSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierPairRankBitSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumData

/-! # Exact route-descriptor carrier bits from datum injectivity -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The route-descriptor datum-only target equals the exact carrier bit block
under finite-list projection injectivity and strict per-key coordinate order. -/
theorem routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod_eq_of_injectiveOn
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell)
    (injectiveOn :
      ∀ first ∈ routeDescriptorRetainedCarrierNodesAtPeriod
          period descriptors,
        ∀ second ∈ routeDescriptorRetainedCarrierNodesAtPeriod
          period descriptors,
          carrierNodeRankDatumAtPeriod period first =
            carrierNodeRankDatumAtPeriod period second → first = second)
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
  let nodes := routeDescriptorRetainedCarrierNodesAtPeriod
    period descriptors
  unfold routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod
    routeDescriptorCarrierRankDatumsAtPeriod
    routeDescriptorRetainedCarrierPairBitsAtPeriod
  rw [retainedCarrierRankDatumBits_map_eq_of_injectiveOn
    period nodes key injectiveOn ordered]
  rw [retainedCarrierRankDatumBitsAtPeriod_eq]
  exact retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod_eq
    period nodes key ordered

end LeanTrominoes.PeriodicOrthocrossing
