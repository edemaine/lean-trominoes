/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetCandidateAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRecipeWordLength
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Alignment length of normalization-offset candidate fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetCandidateFieldStream

open CarrierNormalizationOffsetField

private theorem gaugedTerminalBlock_length
    (field : Field) (gauged : RouteDescriptorPairAffine.GaugedSegment) :
    (gauged.terminalNormalizationOffsetExpressionBlock field).length =
      (gauged.segment.terminalOwnershipShiftExpressionBlock
        .horizontalPositive).length := by
  unfold RouteDescriptorPairAffine.GaugedSegment.terminalNormalizationOffsetExpressionBlock
    RouteDescriptorPairAffine.Segment.terminalOwnershipShiftExpressionBlock
  induction neighborTranslations with
  | nil => rfl
  | cons translate translations induction =>
      simpa only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, List.length_replicate] using
        congrArg (fun length => 2 + length) induction

private theorem shapeTerminalExpressions_length
    (field : Field) (shape : RouteDescriptorPairAffine.RouteShape) :
    ((shape.terminalNormalizationOffsetExpressionBlocks field).flatten).length =
      ((shape.terminalOwnershipShiftExpressionBlocks
        .horizontalPositive).flatten).length := by
  unfold RouteDescriptorPairAffine.RouteShape.terminalNormalizationOffsetExpressionBlocks
    RouteDescriptorPairAffine.RouteShape.terminalOwnershipShiftExpressionBlocks
  rw [← shape.gaugedSegments_map_segment]
  simp only [List.flatMap_map]
  induction shape.gaugedSegments .first with
  | nil => rfl
  | cons gauged gaugedSegments induction =>
      simp only [List.flatMap_cons, List.flatten_append, List.length_append]
      rw [induction]
      unfold RouteDescriptorPairAffine.GaugedSegment.terminalNormalizationOffsetExpressionBlocks
        RouteDescriptorPairAffine.Segment.terminalOwnershipShiftExpressionBlocks
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append]
      rw [gaugedTerminalBlock_length]

private theorem terminalNormalizationOffsetExpressions_length
    (field : Field) :
    (RouteDescriptorPairAffine.terminalNormalizationOffsetExpressions
      field).length =
      (RouteDescriptorPairAffine.terminalOwnershipShiftExpressions
        .horizontalPositive).length := by
  unfold RouteDescriptorPairAffine.terminalNormalizationOffsetExpressions
    RouteDescriptorPairAffine.terminalNormalizationOffsetExpressionBlocks
    RouteDescriptorPairAffine.terminalOwnershipShiftExpressions
    RouteDescriptorPairAffine.terminalOwnershipShiftExpressionBlocks
  induction RouteDescriptorPairAffine.allRouteShapes with
  | nil => rfl
  | cons shape shapes induction =>
      simp only [List.flatMap_cons, List.flatten_append, List.length_append]
      rw [shapeTerminalExpressions_length, induction]

private theorem crossingBlock_length
    (field : Field)
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence) :
    (RouteDescriptorPairAffine.occurrencePairCrossingNormalizationOffsetExpressionBlock
      field occurrences).length =
      (RouteDescriptorPairAffine.occurrencePairCrossingOwnershipShiftExpressionBlock
        .horizontalPositive occurrences).length := by
  unfold RouteDescriptorPairAffine.occurrencePairCrossingNormalizationOffsetExpressionBlock
    RouteDescriptorPairAffine.occurrencePairCrossingOwnershipShiftExpressionBlock
  induction carrierCrossingRetentionShifts with
  | nil => rfl
  | cons shift shifts induction =>
      simpa only [List.flatMap_cons, List.length_append,
        RouteDescriptorPairAffine.occurrencePairCrossingNormalizationOffsetExpressionShiftBlock,
        RouteDescriptorPairAffine.occurrencePairCrossingOwnershipShiftExpressionShiftBlock,
        List.length_replicate] using
        congrArg (fun length => 4 + length) induction

private theorem crossingNormalizationOffsetExpressions_length
    (field : Field) :
    (RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetExpressions
      field).length =
      (RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftExpressions
        .horizontalPositive).length := by
  unfold RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetExpressions
    RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetExpressionBlocks
    RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftExpressions
    RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftExpressionBlocks
  induction RouteDescriptorOccurrenceSlotCrossing.crossingSlots with
  | nil => rfl
  | cons slot slots induction =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [crossingBlock_length, induction]

private theorem terminalNormalizationOffsetFields_length
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    (RouteDescriptorPairAffine.terminalNormalizationOffsetFields field
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).length =
      (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates pair).length := by
  have ownershipAligned :=
    RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates_ownershipShift_forall₂
      CarrierOwnershipShiftField.Field.horizontalPositive 0 pair
  rw [RouteDescriptorPairAffine.terminalNormalizationOffsetFields,
    RouteDescriptorPairAffine.normalizedFields_length,
    terminalNormalizationOffsetExpressions_length]
  rw [ownershipAligned.length_eq]
  unfold RouteDescriptorPairAffine.terminalOwnershipShiftFields
  rw [RouteDescriptorPairAffine.normalizedFields_length]

private theorem crossingNormalizationOffsetFields_length
    (field : Field)
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    (RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetFields
      field
      (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
        pair)).length =
      (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates
        pair).length := by
  have ownershipAligned :=
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates_ownershipShift_forall₂
      CarrierOwnershipShiftField.Field.horizontalPositive pair
  rw [RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetFields,
    RouteDescriptorPairAffine.normalizedFields_length,
    crossingNormalizationOffsetExpressions_length]
  rw [ownershipAligned.length_eq]
  unfold RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftFields
  rw [RouteDescriptorPairAffine.normalizedFields_length]

theorem terminalValues_length
    (field : Field) (descriptors : List RouteDescriptor) :
    (terminalValues field descriptors).length =
      (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
        descriptors).length := by
  unfold terminalValues
    RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
  induction (descriptors ×ˢ descriptors) with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [induction]
      exact congrArg
        (fun length => length +
          (pairs.flatMap
            RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidates).length)
        (terminalNormalizationOffsetFields_length field pair)

theorem crossingValues_length
    (field : Field) (descriptors : List RouteDescriptor) :
    (crossingValues field descriptors).length =
      (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
        descriptors).length := by
  unfold crossingValues
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
  induction (RouteDescriptorOccurrenceSlotBinaryWords.taggedDescriptors
      descriptors ×ˢ
      RouteDescriptorOccurrenceSlotBinaryWords.taggedDescriptors
        descriptors) with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [induction]
      exact congrArg
        (fun length => length +
          (pairs.flatMap
            RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidates).length)
        (crossingNormalizationOffsetFields_length field pair)

theorem valuesWithSentinel_length_sourceKeyCandidates
    (field : Field) (descriptors : List RouteDescriptor) :
    (valuesWithSentinel field descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  unfold valuesWithSentinel
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [show (values field descriptors).length =
      (paddedCarrierNodeCandidateStream descriptors).length by
    simp [values, paddedCarrierNodeCandidateStream,
      terminalValues_length, crossingValues_length]]
  simp [paddedCarrierSourceKeyCandidateStream]

end CarrierNormalizationOffsetCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
