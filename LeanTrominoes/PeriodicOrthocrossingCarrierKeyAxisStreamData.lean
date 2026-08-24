/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyAxisValueData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueData

/-! # Complete padded carrier-key axis-value streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisStream

open RouteDescriptorOccurrenceSlotBinaryWords

def terminalValues (descriptors : List RouteDescriptor) : List Nat :=
  (descriptors ×ˢ descriptors).flatMap fun pair =>
    RouteDescriptorPairAffine.terminalCarrierKeyAxisValues
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

def crossingValues (descriptors : List RouteDescriptor) : List Nat :=
  (taggedDescriptors descriptors ×ˢ
      taggedDescriptors descriptors).flatMap fun pair =>
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyAxisValues
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
        pair)

/-- Terminal-prefix/crossing-suffix zero-or-one values aligned with the
complete padded carrier-key candidate stream. -/
def values (descriptors : List RouteDescriptor) : List Nat :=
  terminalValues descriptors ++ crossingValues descriptors

/-- Sentinel-completed axis values aligned with the rejection-guard column
of every selected last-representative row. -/
def valuesWithSentinel (descriptors : List RouteDescriptor) : List Nat :=
  values descriptors ++ [0]

end CarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing
