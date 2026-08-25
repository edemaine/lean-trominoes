/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Boundary-presence projection of terminal carrier-node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem Segment.map_boundaryPresence_terminalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map
          (Template.mapValue CarrierBoundaryPresenceField.nodeValue)) =
      (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue fun _ => 0)) := by
  simp [Segment.terminalCarrierNodeTemplateBlocks]

@[simp] theorem RouteShape.map_boundaryPresence_terminalCarrierNodeTemplateBlocks
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map
          (Template.mapValue CarrierBoundaryPresenceField.nodeValue)) =
      (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold RouteShape.terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro tagged _taggedMember
  exact Segment.map_boundaryPresence_terminalCarrierNodeTemplateBlocks
    pair tagged.2 tagged.1

@[simp] theorem map_boundaryPresence_terminalCarrierNodeTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    (terminalCarrierNodeTemplateBlocks pair).map
        (List.map
          (Template.mapValue CarrierBoundaryPresenceField.nodeValue)) =
      (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.map_boundaryPresence_terminalCarrierNodeTemplateBlocks pair

@[simp] theorem map_boundaryPresence_paddedTerminalCarrierNodeCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidates
  rw [candidates_mapValue, candidates_mapValue]
  rw [map_boundaryPresence_terminalCarrierNodeTemplateBlocks]

@[simp] theorem map_boundaryPresence_paddedTerminalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue CarrierBoundaryPresenceField.nodeValue) =
      (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidateStream
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_boundaryPresence_paddedTerminalCarrierNodeCandidates pair

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
