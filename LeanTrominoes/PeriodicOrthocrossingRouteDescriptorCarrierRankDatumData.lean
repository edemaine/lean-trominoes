/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData

/-! # Carrier rank data reconstructed from route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Compiler-facing rank data of the complete retained route-descriptor node
stream at an explicit drawing period. -/
def routeDescriptorCarrierRankDatumsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List CarrierNodeRankDatum :=
  (routeDescriptorRetainedCarrierNodesAtPeriod period descriptors).map
    (carrierNodeRankDatumAtPeriod period)

/-- Datum-only rank-major axis/next-slice bit target for one retained
route-descriptor carrier key. -/
def routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  retainedCarrierRankDatumBits
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors) key

end LeanTrominoes.PeriodicOrthocrossing
