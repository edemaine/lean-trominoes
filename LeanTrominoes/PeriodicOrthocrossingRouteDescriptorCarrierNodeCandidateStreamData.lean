/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Complete padded carrier-node candidate streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Complete padded carrier-node stream: terminal prefix followed by the
exact `descriptor₁, slot₁, descriptor₂, slot₂` crossing stream. -/
def paddedCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    List (Candidate CarrierNode) :=
  RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
      descriptors ++
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
      descriptors

end LeanTrominoes.PeriodicOrthocrossing

end
