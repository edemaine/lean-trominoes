/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceCrossingCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData

/-! # Boundary-presence values of crossing carrier-node candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Constant-one active crossing-key projection agrees pointwise with the
boundary-presence value of every padded crossing node. -/
theorem crossingPresenceValues_eq_optionalNodeValues
    (descriptors : List RouteDescriptor) :
    ((values (paddedCrossingCarrierNodeCandidateStream descriptors)).map
        (Option.map CarrierNode.carrierKey)).map
          (GuardedPresenceFieldProjector.value true) =
      (values (paddedCrossingCarrierNodeCandidateStream descriptors)).map
        CarrierBoundaryPresenceField.optionalNodeValue := by
  calc
    _ = (values
          ((paddedCrossingCarrierNodeCandidateStream descriptors).map
            (Candidate.mapValue fun _ : CarrierNode => 1))).map
          fun value => value.getD 0 := by
        rw [values_map_mapValue]
        simp only [List.map_map]
        apply List.map_congr_left
        intro value _valueMember
        cases value <;> rfl
    _ = (values
          ((paddedCrossingCarrierNodeCandidateStream descriptors).map
            (Candidate.mapValue
              CarrierBoundaryPresenceField.nodeValue))).map
          fun value => value.getD 0 := by
        exact congrArg
          (fun candidates =>
            (values candidates).map fun value => value.getD 0)
          (map_boundaryPresence_paddedCrossingCarrierNodeCandidateStream
            descriptors).symm
    _ = _ := by
      rw [values_map_mapValue]
      rw [List.map_map]
      apply List.map_congr_left
      intro value _valueMember
      cases value <;> rfl

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
