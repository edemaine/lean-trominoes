/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Crossing-point fields on terminal candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierCrossingPointField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem Segment.map_crossingPointField_terminalCarrierNodeTemplateBlock
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.mapValue (nodeValue field)) =
      (segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.mapValue fun _ => 0) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro translate _translateMember
  simp [Template.mapValue, nodeValue]

@[simp] theorem Segment.map_crossingPointField_terminalCarrierNodeTemplateBlocks
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue (nodeValue field))) =
      (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue fun _ => 0)) := by
  simp [Segment.terminalCarrierNodeTemplateBlocks]

@[simp] theorem RouteShape.map_crossingPointField_terminalCarrierNodeTemplateBlocks
    (field : Field) (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor) :
    (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue (nodeValue field))) =
      (shape.terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold RouteShape.terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro tagged _taggedMember
  exact tagged.1.map_crossingPointField_terminalCarrierNodeTemplateBlocks
    field pair tagged.2

@[simp] theorem map_crossingPointField_terminalCarrierNodeTemplateBlocks
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue (nodeValue field))) =
      (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.map_crossingPointField_terminalCarrierNodeTemplateBlocks
    field pair

@[simp] theorem map_crossingPointField_paddedTerminalCarrierNodeCandidates
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue (nodeValue field)) =
      (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidates
  rw [candidates_mapValue, candidates_mapValue]
  rw [map_crossingPointField_terminalCarrierNodeTemplateBlocks]

@[simp] theorem map_crossingPointField_paddedTerminalCarrierNodeCandidateStream
    (field : Field) (descriptors : List RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue (nodeValue field)) =
      (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidateStream
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_crossingPointField_paddedTerminalCarrierNodeCandidates
    field pair

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
