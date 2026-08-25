/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics

/-! # Alignment of indexed crossing-segment fields with candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierCrossingIndexedSegmentField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

theorem normalizedCrossingIndexedSegmentExpression_eq_nodeValue
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) (side : CrossingSide)
    (pair : RouteDescriptor × RouteDescriptor) :
    normalizedExpressionField (keepPositive field)
        (occurrencePairCrossingIndexedSegmentExpression field occurrences)
        pair =
      nodeValue field
        (.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair)) shift,
            side⟩) := by
  cases field with
  | firstSegmentIndex =>
      simp [normalizedExpressionField,
        occurrencePairCrossingIndexedSegmentExpression,
        CarrierCrossingIndexedSegmentField.keepPositive,
        nodeValue, recordValue, crossingRecordPeriodTranslateAtPeriod,
        occurrencePairCrossingRecordAtPeriod, Occurrence.evalPair,
        CrossingRecord.code, indexedGridSegmentCode,
        Expression.evalPair, Expression.eval]
  | coordinate segmentSide endpoint horizontal keep =>
      cases segmentSide <;> cases endpoint <;>
        cases horizontal <;> cases keep <;>
          simp [normalizedExpressionField,
            occurrencePairCrossingIndexedSegmentExpression,
            crossingIndexedSegmentOccurrence,
            crossingIndexedSegmentEndpoint, Point.axisExpression,
            CarrierCrossingIndexedSegmentField.keepPositive,
            nodeValue, recordValue, recordSegment, segmentEndpoint,
            coordinateValue, crossingRecordPeriodTranslateAtPeriod,
            occurrencePairCrossingRecordAtPeriod, Occurrence.evalPair,
            CrossingRecord.code, indexedGridSegmentCode,
            Segment.evalPair, Segment.eval, Point.eval,
            Expression.evalPair]

theorem occurrencePairCrossingIndexedSegmentExpressionShiftBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map (Template.activate active))
      ((occurrencePairCrossingIndexedSegmentExpressionShiftBlock
        field occurrences shift).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeShiftTemplateBlock
    occurrencePairCrossingIndexedSegmentExpressionShiftBlock
  simp only [List.replicate_succ, List.replicate_zero,
    List.map_cons, List.map_nil]
  apply List.Forall₂.cons
  · intro node valueEq
    cases active with
    | false => simp [Template.activate] at valueEq
    | true =>
        simp only [Template.activate, Bool.true_and, if_true,
          Option.some.injEq] at valueEq
        subst node
        exact normalizedCrossingIndexedSegmentExpression_eq_nodeValue
          field occurrences shift .left pair
  · apply List.Forall₂.cons
    · intro node valueEq
      cases active with
      | false => simp [Template.activate] at valueEq
      | true =>
          simp only [Template.activate, Bool.true_and, if_true,
            Option.some.injEq] at valueEq
          subst node
          exact normalizedCrossingIndexedSegmentExpression_eq_nodeValue
            field occurrences shift .right pair
    · apply List.Forall₂.cons
      · intro node valueEq
        cases active with
        | false => simp [Template.activate] at valueEq
        | true =>
            simp only [Template.activate, Bool.true_and, if_true,
              Option.some.injEq] at valueEq
            subst node
            exact normalizedCrossingIndexedSegmentExpression_eq_nodeValue
              field occurrences shift .top pair
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              exact normalizedCrossingIndexedSegmentExpression_eq_nodeValue
                field occurrences shift .bottom pair
        · exact List.Forall₂.nil

theorem occurrencePairCrossingIndexedSegmentExpressionBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (active : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      ((occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map (Template.activate active))
      ((occurrencePairCrossingIndexedSegmentExpressionBlock
        field occurrences).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairCrossingIndexedSegmentExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  induction carrierCrossingRetentionShifts with
  | nil => exact List.Forall₂.nil
  | cons shift shifts induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append
        (occurrencePairCrossingIndexedSegmentExpressionShiftBlock_forall₂
          field occurrences shift active pair)
        induction

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierCrossingIndexedSegmentField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem crossingIndexedSegmentFields_descriptorSlotPairTokens
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingIndexedSegmentFields field (descriptorSlotPairTokens pair) =
      (crossingIndexedSegmentExpressions field).map fun expression =>
        RouteDescriptorPairAffine.normalizedExpressionField
          (keepPositive field) expression (pair.1.1, pair.2.1) := by
  unfold crossingIndexedSegmentFields
  rw [descriptorTokens_descriptorSlotPairTokens]
  have evalEq : ∀ expression : RouteDescriptorPairAffine.Expression,
      expression.eval
          (RouteDescriptorPairFieldTags.tokenFieldValue
            (RouteDescriptorPairFieldTags.descriptorPairTokens
              (pair.1.1, pair.2.1))) =
        expression.evalPair (pair.1.1, pair.2.1) := by
    intro expression
    simpa [RouteDescriptorPairAffine.Expression.evalTokens] using
      expression.evalTokens_descriptorPairTokens (pair.1.1, pair.2.1)
  cases field with
  | firstSegmentIndex =>
      simp [RouteDescriptorPairAffine.normalizedExpressionField,
        CarrierCrossingIndexedSegmentField.keepPositive, evalEq]
  | coordinate side endpoint horizontal keep =>
      cases keep <;>
        simp [RouteDescriptorPairAffine.normalizedExpressionField,
          CarrierCrossingIndexedSegmentField.keepPositive, evalEq]

theorem paddedCrossingCarrierNodeCandidates_indexedSegment_forall₂
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (paddedCrossingCarrierNodeCandidates pair)
      (crossingIndexedSegmentFields field (descriptorSlotPairTokens pair)) := by
  rw [crossingIndexedSegmentFields_descriptorSlotPairTokens]
  unfold paddedCrossingCarrierNodeCandidates crossingActivations
    crossingCarrierNodeTemplateBlocks crossingIndexedSegmentExpressions
    crossingIndexedSegmentExpressionBlocks
  induction crossingSlots with
  | nil => exact List.Forall₂.nil
  | cons slot slots induction =>
      simp only [List.map_cons, List.flatten_cons, candidates,
        List.map_append]
      exact List.Forall₂.append
        (RouteDescriptorPairAffine.occurrencePairCrossingIndexedSegmentExpressionBlock_forall₂
          field slot.occurrences
          (slot.evalTokens (descriptorSlotPairTokens pair))
          (pair.1.1, pair.2.1))
        induction

theorem paddedCrossingCarrierNodeCandidateStream_indexedSegment_forall₂
    (field : Field) (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (paddedCrossingCarrierNodeCandidateStream descriptors)
      ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          crossingIndexedSegmentFields field
            (descriptorSlotPairTokens pair)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  induction (taggedDescriptors descriptors ×ˢ
      taggedDescriptors descriptors) with
  | nil => exact List.Forall₂.nil
  | cons pair pairs induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append
        (paddedCrossingCarrierNodeCandidates_indexedSegment_forall₂
          field pair)
        induction

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
