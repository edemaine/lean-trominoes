/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceCrossingValueSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Boundary-presence values of the complete carrier-node stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

open PaddedSupportedLastRepresentativeEqualityRows

/-- The joined terminal/crossing presence stream is the pointwise
boundary-presence projection of the complete padded carrier-node stream. -/
theorem componentValuesWithSentinel_eq_optionalNodeValues
    (descriptors : List RouteDescriptor) :
    (((values
        (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
          descriptors)).map (Option.map CarrierNode.carrierKey)).map
        (GuardedPresenceFieldProjector.value false) ++
      ((values
        (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
          descriptors)).map
          (Option.map CarrierNode.carrierKey)).map
        (GuardedPresenceFieldProjector.value true)) ++ [0] =
      (values (paddedCarrierNodeCandidateStream descriptors)).map
        optionalNodeValue ++ [0] := by
  rw [RouteDescriptorPairAffine.terminalPresenceValues_eq_optionalNodeValues]
  rw [RouteDescriptorOccurrenceSlotCrossing.crossingPresenceValues_eq_optionalNodeValues]
  simp [paddedCarrierNodeCandidateStream, values]

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end
