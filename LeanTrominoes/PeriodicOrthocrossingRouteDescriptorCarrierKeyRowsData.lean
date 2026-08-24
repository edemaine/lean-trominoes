/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyOrderData
import LeanTrominoes.SupportedLastRepresentativeEqualityRows

/-! # Retained carrier-key equality rows over route descriptors -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Duplicated neighboring terminal-key prefix reconstructed from route
descriptors. -/
def routeDescriptorTerminalCarrierKeys
    (descriptors : List RouteDescriptor) : List (Nat × Nat × Cell) :=
  occurrenceTerminalCarrierKeys
    (routeDescriptorNeighborOccurrences descriptors)

/-- Complete pre-deduplication carrier-key candidate stream reconstructed
from route descriptors. -/
def routeDescriptorCarrierKeyCandidatesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List (Nat × Nat × Cell) :=
  routeDescriptorTerminalCarrierKeys descriptors ++
    occurrencePairCarrierKeyScan
      (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
        period descriptors)

/-- Guarded last-representative carrier-key equality rows, restricted to
classes that occur among the neighboring terminal keys. -/
def routeDescriptorRetainedCarrierKeyRowsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  SupportedLastRepresentativeEqualityRows.selectedRows
    (routeDescriptorTerminalCarrierKeys descriptors)
    (routeDescriptorCarrierKeyCandidatesAtPeriod period descriptors)

end LeanTrominoes.PeriodicOrthocrossing
