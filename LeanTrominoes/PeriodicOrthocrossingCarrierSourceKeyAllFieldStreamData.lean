/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # All fields of padded carrier-node source-key pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyAllFieldStream

open PaddedSupportedLastRepresentativeEqualityRows

/-- Both optional source-key components of a padded carrier-node candidate
list, in candidate-major and first-then-second order. -/
def componentKeysOfCandidates
    (candidates : List (Candidate CarrierNode)) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values candidates).flatMap fun node =>
    [node.map fun value => (CarrierNodeSourceKeys.pair value).1,
      node.map fun value => (CarrierNodeSourceKeys.pair value).2]

/-- Source-key components of the complete padded descriptor candidate
stream. -/
def componentKeys (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  componentKeysOfCandidates (paddedCarrierNodeCandidateStream descriptors)

/-- Twelve unary fields per padded carrier-node candidate, followed by one
twelve-zero rejection-sentinel block. -/
def fieldValuesWithSentinel
    (descriptors : List RouteDescriptor) : List Nat :=
  CarrierKeyAllFieldProjector.valuesWithSentinel
    (componentKeys descriptors)

end CarrierSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
