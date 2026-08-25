/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceRankValueData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeTemplateData

/-! # Boundary-presence projection of terminal carrier-node templates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

@[simp] theorem Segment.map_boundaryPresence_terminalCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.mapValue fun _ => 0) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro translate _translateMember
  simp [Template.mapValue, CarrierBoundaryPresenceField.nodeValue]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
