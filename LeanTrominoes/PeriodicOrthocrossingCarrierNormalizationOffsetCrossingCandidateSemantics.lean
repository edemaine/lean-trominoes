/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPrototypeGaugeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetTerminalCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics

/-! # Crossing normalization-offset fields aligned with carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierNormalizationOffsetField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

theorem occurrencePairCrossingNormalizationOffsetExpressionShiftBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (normalizationEq : active = true → ∀ side,
      carrierNodeNormalizationOffsetAtPeriod pair.1.gridSize
          (.boundary
            ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
                (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                  (occurrences.1.evalPair .first pair,
                    occurrences.2.evalPair .second pair)) shift,
              side⟩) = shift) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map (Template.activate active))
      ((occurrencePairCrossingNormalizationOffsetExpressionShiftBlock
        field occurrences shift).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeShiftTemplateBlock
    occurrencePairCrossingNormalizationOffsetExpressionShiftBlock
  simp only [List.replicate_succ, List.replicate_zero,
    List.map_cons, List.map_nil]
  have outputEq (activeEq : active = true) : ∀ side,
      normalizedExpressionField (keepPositive field)
          (normalizationOffsetExpression field shift (0, 0)) pair =
        nodeValueAtPeriod field pair.1.gridSize
          (.boundary
            ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
                (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                  (occurrences.1.evalPair .first pair,
                    occurrences.2.evalPair .second pair)) shift,
              side⟩) := by
    intro side
    change _ = offsetValue field
      (carrierNodeNormalizationOffsetAtPeriod pair.1.gridSize _)
    rw [normalizationEq activeEq side]
    simpa [Cell.add] using
      normalizedNormalizationOffsetExpression_eq_offsetValue
        field shift (0, 0) pair
  apply List.Forall₂.cons
  · intro node valueEq
    cases active with
    | false => simp [Template.activate] at valueEq
    | true =>
        simp only [Template.activate, Bool.true_and, if_true,
          Option.some.injEq] at valueEq
        subst node
        exact outputEq rfl .left
  · apply List.Forall₂.cons
    · intro node valueEq
      cases active with
      | false => simp [Template.activate] at valueEq
      | true =>
          simp only [Template.activate, Bool.true_and, if_true,
            Option.some.injEq] at valueEq
          subst node
          exact outputEq rfl .right
    · apply List.Forall₂.cons
      · intro node valueEq
        cases active with
        | false => simp [Template.activate] at valueEq
        | true =>
            simp only [Template.activate, Bool.true_and, if_true,
              Option.some.injEq] at valueEq
            subst node
            exact outputEq rfl .top
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              exact outputEq rfl .bottom
        · exact List.Forall₂.nil

theorem occurrencePairCrossingNormalizationOffsetExpressionBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (active : Bool) (pair : RouteDescriptor × RouteDescriptor)
    (normalizationEq : ∀ shift ∈ carrierCrossingRetentionShifts,
      active = true → ∀ side,
        carrierNodeNormalizationOffsetAtPeriod pair.1.gridSize
            (.boundary
              ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
                  (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                    (occurrences.1.evalPair .first pair,
                      occurrences.2.evalPair .second pair)) shift,
                side⟩) = shift) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map (Template.activate active))
      ((occurrencePairCrossingNormalizationOffsetExpressionBlock
        field occurrences).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairCrossingNormalizationOffsetExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  have aligned : ∀ shifts : List Cell,
      (∀ shift ∈ shifts, active = true → ∀ side,
        carrierNodeNormalizationOffsetAtPeriod pair.1.gridSize
            (.boundary
              ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
                  (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                    (occurrences.1.evalPair .first pair,
                      occurrences.2.evalPair .second pair)) shift,
                side⟩) = shift) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field pair.1.gridSize node)
        (shifts.flatMap fun shift =>
          (occurrencePairCrossingCarrierNodeShiftTemplateBlock
            pair occurrences shift).map (Template.activate active))
        (shifts.flatMap fun shift =>
          (occurrencePairCrossingNormalizationOffsetExpressionShiftBlock
            field occurrences shift).map fun expression =>
              normalizedExpressionField
                (keepPositive field) expression pair) := by
    intro shifts shiftNormalization
    induction shifts with
    | nil => exact List.Forall₂.nil
    | cons shift shifts induction =>
        simp only [List.flatMap_cons]
        exact List.Forall₂.append
          (occurrencePairCrossingNormalizationOffsetExpressionShiftBlock_forall₂
            field occurrences shift active pair
            (shiftNormalization shift (List.mem_cons_self)))
          (induction fun remaining remainingMember =>
            shiftNormalization remaining
              (List.mem_cons_of_mem shift remainingMember))
  exact aligned carrierCrossingRetentionShifts normalizationEq

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierNormalizationOffsetField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem crossingNormalizationOffsetFields_descriptorSlotPairTokens
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingNormalizationOffsetFields field (descriptorSlotPairTokens pair) =
      (crossingNormalizationOffsetExpressions field).map fun expression =>
        RouteDescriptorPairAffine.normalizedExpressionField
          (keepPositive field) expression (pair.1.1, pair.2.1) := by
  unfold crossingNormalizationOffsetFields
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
  cases field <;>
    simp [RouteDescriptorPairAffine.normalizedExpressionField,
      CarrierNormalizationOffsetField.keepPositive, evalEq]

theorem paddedCrossingCarrierNodeCandidates_normalizationOffset_forall₂
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.1.gridSize node)
      (paddedCrossingCarrierNodeCandidates pair)
      (crossingNormalizationOffsetFields field
        (descriptorSlotPairTokens pair)) := by
  rw [crossingNormalizationOffsetFields_descriptorSlotPairTokens]
  unfold paddedCrossingCarrierNodeCandidates crossingActivations
    crossingCarrierNodeTemplateBlocks crossingNormalizationOffsetExpressions
    crossingNormalizationOffsetExpressionBlocks
  have aligned : ∀ slots : List Slot,
      (∀ slot ∈ slots, slot ∈ crossingSlots) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field pair.1.1.gridSize node)
        (candidates
          (slots.map fun slot =>
            slot.evalTokens (descriptorSlotPairTokens pair))
          (slots.map fun slot => slot.carrierNodeTemplateBlock
            (pair.1.1, pair.2.1)))
        ((slots.map fun slot =>
          RouteDescriptorPairAffine.occurrencePairCrossingNormalizationOffsetExpressionBlock
            field slot.occurrences).flatten.map fun expression =>
              RouteDescriptorPairAffine.normalizedExpressionField
                (keepPositive field) expression (pair.1.1, pair.2.1)) := by
    intro slots slotsMember
    induction slots with
    | nil => exact List.Forall₂.nil
    | cons slot slots induction =>
        simp only [List.map_cons, List.flatten_cons, candidates,
          List.map_append]
        apply List.Forall₂.append
        · unfold Slot.carrierNodeTemplateBlock
          apply
            RouteDescriptorPairAffine.occurrencePairCrossingNormalizationOffsetExpressionBlock_forall₂
              (field := field) (occurrences := slot.occurrences)
              (active := slot.evalTokens (descriptorSlotPairTokens pair))
              (pair := (pair.1.1, pair.2.1))
          intro shift _shiftMember active side
          have bounds :=
            slot.crossingPointBounds_of_mem_crossingSlots_of_active
              (slotsMember slot (List.mem_cons_self)) pair active
          exact carrierNodeNormalizationOffsetAtPeriod_periodTranslatedBoundary
            pair.1.1.gridSize_positive _ shift bounds side
        · exact induction fun remaining remainingMember =>
            slotsMember remaining
              (List.mem_cons_of_mem slot remainingMember)
  exact aligned crossingSlots (fun _ member => member)

theorem paddedCrossingCarrierNodeCandidateStream_normalizationOffset_forall₂
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (paddedCrossingCarrierNodeCandidateStream descriptors)
      ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          crossingNormalizationOffsetFields field
            (descriptorSlotPairTokens pair)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  have aligned : ∀ pairs : List (TaggedDescriptor × TaggedDescriptor),
      (∀ pair ∈ pairs, pair.1.1.gridSize = period) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field period node)
        (pairs.flatMap paddedCrossingCarrierNodeCandidates)
        (pairs.flatMap fun pair =>
          crossingNormalizationOffsetFields field
            (descriptorSlotPairTokens pair)) := by
    intro pairs pairPeriodEq
    induction pairs with
    | nil => exact List.Forall₂.nil
    | cons pair pairs induction =>
        simp only [List.flatMap_cons]
        apply List.Forall₂.append
        · have pairAligned :=
            paddedCrossingCarrierNodeCandidates_normalizationOffset_forall₂
              field pair
          rw [pairPeriodEq pair (List.mem_cons_self)] at pairAligned
          exact pairAligned
        · exact induction fun remaining remainingMember =>
            pairPeriodEq remaining
              (List.mem_cons_of_mem pair remainingMember)
  apply aligned
  intro pair pairMember
  have firstTaggedMember : pair.1 ∈ taggedDescriptors descriptors :=
    (List.mem_product.mp pairMember).1
  have firstMember : pair.1.1 ∈ descriptors := by
    unfold taggedDescriptors at firstTaggedMember
    rcases List.mem_flatMap.mp firstTaggedMember with
      ⟨descriptor, descriptorMember, taggedMember⟩
    rcases List.mem_map.mp taggedMember with
      ⟨slot, _slotMember, taggedEq⟩
    exact taggedEq ▸ descriptorMember
  exact periodEq pair.1.1 firstMember

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
