/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointTerminalCandidateSemantics

/-! # Crossing-point values of terminal carrier-node candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointCandidateFieldStream

open CarrierCrossingPointField
open PaddedSupportedLastRepresentativeEqualityRows

theorem terminalValues_eq_optionalNodeValues
    (field : Field) (descriptors : List RouteDescriptor) :
    terminalValues descriptors =
      (PaddedSupportedLastRepresentativeEqualityRows.values
        (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
          descriptors)).map (optionalNodeValue field) := by
  calc
    _ = (PaddedSupportedLastRepresentativeEqualityRows.values
          ((RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
              descriptors).map
            (Candidate.mapValue fun _ : CarrierNode => 0))).map
          fun value => value.getD 0 := by
        unfold terminalValues CarrierBoundaryPresenceField.terminalKeys
        rw [values_map_mapValue]
        simp only [List.map_map]
        apply List.map_congr_left
        intro value _valueMember
        cases value <;> rfl
    _ = (PaddedSupportedLastRepresentativeEqualityRows.values
          ((RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
              descriptors).map
            (Candidate.mapValue (nodeValue field)))).map
          fun value => value.getD 0 := by
        exact congrArg
          (fun candidates =>
            (PaddedSupportedLastRepresentativeEqualityRows.values
              candidates).map fun value => value.getD 0)
          (RouteDescriptorPairAffine.map_crossingPointField_paddedTerminalCarrierNodeCandidateStream
            field descriptors).symm
    _ = _ := by
      rw [values_map_mapValue]
      rw [List.map_map]
      apply List.map_congr_left
      intro value _valueMember
      cases value <;> rfl

end CarrierCrossingPointCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
