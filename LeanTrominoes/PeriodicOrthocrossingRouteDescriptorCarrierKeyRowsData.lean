/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyOrderData
import LeanTrominoes.LastRepresentativeEqualityRowsPrefixFilterSemantics

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

/-- Last-representative carrier-key equality rows, restricted to classes
that occur in the neighboring terminal-key prefix. -/
def routeDescriptorRetainedCarrierKeyRowsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.prefixSupportedRows
    (routeDescriptorTerminalCarrierKeys descriptors).length
    ⟨LastRepresentativeEqualityRows.equalityRows
      (routeDescriptorCarrierKeyCandidatesAtPeriod period descriptors)⟩

end LeanTrominoes.PeriodicOrthocrossing
