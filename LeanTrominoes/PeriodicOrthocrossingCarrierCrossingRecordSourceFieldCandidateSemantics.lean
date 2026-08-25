/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMap
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData

/-! # Source-key crossing fields on terminal and crossing candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

namespace RouteDescriptorPairAffine

open CarrierCrossingRecordSourceField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem Segment.map_crossingRecordSourceField_terminalCarrierNodeTemplateBlock
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

@[simp] theorem Segment.map_crossingRecordSourceField_terminalCarrierNodeTemplateBlocks
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue (nodeValue field))) =
      (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex).map
        (List.map (Template.mapValue fun _ => 0)) := by
  simp [Segment.terminalCarrierNodeTemplateBlocks]

@[simp] theorem RouteShape.map_crossingRecordSourceField_terminalCarrierNodeTemplateBlocks
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
  exact tagged.1.map_crossingRecordSourceField_terminalCarrierNodeTemplateBlocks
    field pair tagged.2

@[simp] theorem map_crossingRecordSourceField_terminalCarrierNodeTemplateBlocks
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue (nodeValue field))) =
      (terminalCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue fun _ => 0)) := by
  unfold terminalCarrierNodeTemplateBlocks
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.map_crossingRecordSourceField_terminalCarrierNodeTemplateBlocks
    field pair

@[simp] theorem map_crossingRecordSourceField_paddedTerminalCarrierNodeCandidates
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue (nodeValue field)) =
      (paddedTerminalCarrierNodeCandidates pair).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidates
  rw [candidates_mapValue, candidates_mapValue]
  rw [map_crossingRecordSourceField_terminalCarrierNodeTemplateBlocks]

@[simp] theorem map_crossingRecordSourceField_paddedTerminalCarrierNodeCandidateStream
    (field : Field) (descriptors : List RouteDescriptor) :
    (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue (nodeValue field)) =
      (paddedTerminalCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue fun _ => 0) := by
  unfold paddedTerminalCarrierNodeCandidateStream
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_crossingRecordSourceField_paddedTerminalCarrierNodeCandidates
    field pair

@[simp] theorem map_crossingRecordSourceField_occurrencePairCrossingCarrierNodeShiftTemplateBlock
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map
        (Template.mapValue (nodeValue field)) =
      (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map
        (Template.mapValue (sourceNodeValue field)) := by
  simp [occurrencePairCrossingCarrierNodeShiftTemplateBlock,
    Template.mapValue, nodeValue]

@[simp] theorem map_crossingRecordSourceField_occurrencePairCrossingCarrierNodeTemplateBlock
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingCarrierNodeTemplateBlock pair occurrences).map
        (Template.mapValue (nodeValue field)) =
      (occurrencePairCrossingCarrierNodeTemplateBlock pair occurrences).map
        (Template.mapValue (sourceNodeValue field)) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact
    map_crossingRecordSourceField_occurrencePairCrossingCarrierNodeShiftTemplateBlock
      field pair occurrences shift

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierCrossingRecordSourceField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorPairAffine

@[simp] theorem Slot.map_crossingRecordSourceField_carrierNodeTemplateBlock
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (slot : Slot) :
    (slot.carrierNodeTemplateBlock pair).map
        (Template.mapValue (nodeValue field)) =
      (slot.carrierNodeTemplateBlock pair).map
        (Template.mapValue (sourceNodeValue field)) := by
  unfold Slot.carrierNodeTemplateBlock
  exact
    map_crossingRecordSourceField_occurrencePairCrossingCarrierNodeTemplateBlock
      field pair slot.occurrences

@[simp] theorem map_crossingRecordSourceField_crossingCarrierNodeTemplateBlocks
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    (crossingCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue (nodeValue field))) =
      (crossingCarrierNodeTemplateBlocks pair).map
        (List.map (Template.mapValue (sourceNodeValue field))) := by
  simp [crossingCarrierNodeTemplateBlocks]

@[simp] theorem map_crossingRecordSourceField_paddedCrossingCarrierNodeCandidates
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    (paddedCrossingCarrierNodeCandidates pair).map
        (Candidate.mapValue (nodeValue field)) =
      (paddedCrossingCarrierNodeCandidates pair).map
        (Candidate.mapValue (sourceNodeValue field)) := by
  unfold paddedCrossingCarrierNodeCandidates
  rw [candidates_mapValue, candidates_mapValue]
  rw [map_crossingRecordSourceField_crossingCarrierNodeTemplateBlocks]

@[simp] theorem map_crossingRecordSourceField_paddedCrossingCarrierNodeCandidateStream
    (field : Field) (descriptors : List RouteDescriptor) :
    (paddedCrossingCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue (nodeValue field)) =
      (paddedCrossingCarrierNodeCandidateStream descriptors).map
        (Candidate.mapValue (sourceNodeValue field)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  rw [List.map_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro pair _pairMember
  exact map_crossingRecordSourceField_paddedCrossingCarrierNodeCandidates
    field pair

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
