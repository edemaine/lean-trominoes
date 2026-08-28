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

/-- Both optional source-key components of every padded carrier-node
candidate, in candidate-major and first-then-second order. -/
def componentKeys (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values (paddedCarrierNodeCandidateStream descriptors)).flatMap fun node =>
    [node.map fun value => (CarrierNodeSourceKeys.pair value).1,
      node.map fun value => (CarrierNodeSourceKeys.pair value).2]

/-- Twelve unary fields per padded carrier-node candidate, followed by one
twelve-zero rejection-sentinel block. -/
def fieldValuesWithSentinel
    (descriptors : List RouteDescriptor) : List Nat :=
  CarrierKeyAllFieldProjector.valuesWithSentinel
    (componentKeys descriptors)

end CarrierSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
