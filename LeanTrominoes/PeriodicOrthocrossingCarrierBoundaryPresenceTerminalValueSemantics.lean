/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData

/-! # Boundary-presence values of terminal carrier-node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedLastRepresentativeEqualityRows

/-- Constant-zero terminal-key projection agrees pointwise with the
boundary-presence value of every padded terminal node. -/
theorem terminalPresenceValues_eq_optionalNodeValues
    (descriptors : List RouteDescriptor) :
    ((values (paddedTerminalCarrierNodeCandidateStream descriptors)).map
        (Option.map CarrierNode.carrierKey)).map
          (GuardedPresenceFieldProjector.value false) =
      (values (paddedTerminalCarrierNodeCandidateStream descriptors)).map
        CarrierBoundaryPresenceField.optionalNodeValue := by
  calc
    _ = (values
          ((paddedTerminalCarrierNodeCandidateStream descriptors).map
            (Candidate.mapValue fun _ : CarrierNode => 0))).map
          fun value => value.getD 0 := by
        rw [values_map_mapValue]
        simp only [List.map_map]
        apply List.map_congr_left
        intro value _valueMember
        cases value <;> rfl
    _ = (values
          ((paddedTerminalCarrierNodeCandidateStream descriptors).map
            (Candidate.mapValue
              CarrierBoundaryPresenceField.nodeValue))).map
          fun value => value.getD 0 := by
        exact congrArg
          (fun candidates =>
            (values candidates).map fun value => value.getD 0)
          (map_boundaryPresence_paddedTerminalCarrierNodeCandidateStream
            descriptors).symm
    _ = _ := by
      rw [values_map_mapValue]
      rw [List.map_map]
      apply List.map_congr_left
      intro value _valueMember
      cases value <;> rfl

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
