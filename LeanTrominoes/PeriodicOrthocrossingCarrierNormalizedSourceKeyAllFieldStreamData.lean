/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeNormalizedSourceKeyData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # All fields of normalized padded carrier source-key pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyAllFieldStream

open PaddedSupportedLastRepresentativeEqualityRows

def componentKeysOfCandidatesAtPeriod
    (period : Nat) (candidates : List (Candidate CarrierNode)) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values candidates).flatMap fun node =>
    [node.map fun value =>
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod period value).1,
      node.map fun value =>
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod period value).2]

def componentKeysAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  componentKeysOfCandidatesAtPeriod period
    (paddedCarrierNodeCandidateStream descriptors)

def fieldValuesWithSentinelAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierKeyAllFieldProjector.valuesWithSentinel
    (componentKeysAtPeriod period descriptors)

end CarrierNormalizedSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
