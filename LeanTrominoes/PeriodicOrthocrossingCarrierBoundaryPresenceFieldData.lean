/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Selected boundary-presence field of carrier rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

open PaddedSupportedLastRepresentativeEqualityRows

def terminalKeys (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values
    (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
      descriptors)).map (Option.map CarrierNode.carrierKey)

def crossingKeys (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
      descriptors)).map (Option.map CarrierNode.carrierKey)

/-- Terminal slots contribute zero; active crossing slots contribute one;
inactive slots and the final rejection sentinel contribute zero. -/
def alignedValuesWithSentinel
    (descriptors : List RouteDescriptor) : List Nat :=
  (terminalKeys descriptors).map
      (GuardedPresenceFieldProjector.value false) ++
    (crossingKeys descriptors).map
      (GuardedPresenceFieldProjector.value true) ++
    [0]

def values (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    alignedValuesWithSentinel descriptors

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end
