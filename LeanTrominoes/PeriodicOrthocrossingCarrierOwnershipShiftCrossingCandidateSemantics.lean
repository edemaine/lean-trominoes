/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCrossingQuotientSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftTerminalCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics

/-! # Crossing ownership-shift fields aligned with carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierOwnershipShiftField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

theorem occurrencePairCrossingOwnershipShiftExpressionShiftBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (ownershipEq : active = true →
      crossingRecordPeriodShiftAtPeriod pair.1.gridSize
          (crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
            (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
              (occurrences.1.evalPair .first pair,
                occurrences.2.evalPair .second pair)) shift) = shift) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map (Template.activate active))
      ((occurrencePairCrossingOwnershipShiftExpressionShiftBlock
        field occurrences shift).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeShiftTemplateBlock
    occurrencePairCrossingOwnershipShiftExpressionShiftBlock
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
        change _ = shiftValue field
          (crossingRecordPeriodShiftAtPeriod pair.1.gridSize _)
        rw [ownershipEq rfl]
        exact normalizedOwnershipShiftExpression_eq_shiftValue
          field shift pair
  · apply List.Forall₂.cons
    · intro node valueEq
      cases active with
      | false => simp [Template.activate] at valueEq
      | true =>
          simp only [Template.activate, Bool.true_and, if_true,
            Option.some.injEq] at valueEq
          subst node
          change _ = shiftValue field
            (crossingRecordPeriodShiftAtPeriod pair.1.gridSize _)
          rw [ownershipEq rfl]
          exact normalizedOwnershipShiftExpression_eq_shiftValue
            field shift pair
    · apply List.Forall₂.cons
      · intro node valueEq
        cases active with
        | false => simp [Template.activate] at valueEq
        | true =>
            simp only [Template.activate, Bool.true_and, if_true,
              Option.some.injEq] at valueEq
            subst node
            change _ = shiftValue field
              (crossingRecordPeriodShiftAtPeriod pair.1.gridSize _)
            rw [ownershipEq rfl]
            exact normalizedOwnershipShiftExpression_eq_shiftValue
              field shift pair
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              change _ = shiftValue field
                (crossingRecordPeriodShiftAtPeriod pair.1.gridSize _)
              rw [ownershipEq rfl]
              exact normalizedOwnershipShiftExpression_eq_shiftValue
                field shift pair
        · exact List.Forall₂.nil

theorem occurrencePairCrossingOwnershipShiftExpressionBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (active : Bool) (pair : RouteDescriptor × RouteDescriptor)
    (ownershipEq : ∀ shift ∈ carrierCrossingRetentionShifts,
      active = true →
        crossingRecordPeriodShiftAtPeriod pair.1.gridSize
            (crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair)) shift) = shift) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map (Template.activate active))
      ((occurrencePairCrossingOwnershipShiftExpressionBlock
        field occurrences).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairCrossingOwnershipShiftExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  have aligned : ∀ shifts : List Cell,
      (∀ shift ∈ shifts, active = true →
        crossingRecordPeriodShiftAtPeriod pair.1.gridSize
            (crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair)) shift) = shift) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field pair.1.gridSize node)
        (shifts.flatMap fun shift =>
          (occurrencePairCrossingCarrierNodeShiftTemplateBlock
            pair occurrences shift).map (Template.activate active))
        (shifts.flatMap fun shift =>
          (occurrencePairCrossingOwnershipShiftExpressionShiftBlock
            field occurrences shift).map fun expression =>
              normalizedExpressionField
                (keepPositive field) expression pair) := by
    intro shifts shiftOwnership
    induction shifts with
    | nil => exact List.Forall₂.nil
    | cons shift shifts induction =>
        simp only [List.flatMap_cons]
        exact List.Forall₂.append
          (occurrencePairCrossingOwnershipShiftExpressionShiftBlock_forall₂
            field occurrences shift active pair
            (shiftOwnership shift (List.mem_cons_self)))
          (induction fun remaining remainingMember =>
            shiftOwnership remaining
              (List.mem_cons_of_mem shift remainingMember))
  exact aligned carrierCrossingRetentionShifts ownershipEq

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierOwnershipShiftField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem crossingOwnershipShiftFields_descriptorSlotPairTokens
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingOwnershipShiftFields field (descriptorSlotPairTokens pair) =
      (crossingOwnershipShiftExpressions field).map fun expression =>
        RouteDescriptorPairAffine.normalizedExpressionField
          (keepPositive field) expression (pair.1.1, pair.2.1) := by
  unfold crossingOwnershipShiftFields
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
      CarrierOwnershipShiftField.keepPositive, evalEq]

theorem paddedCrossingCarrierNodeCandidates_ownershipShift_forall₂
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.1.gridSize node)
      (paddedCrossingCarrierNodeCandidates pair)
      (crossingOwnershipShiftFields field
        (descriptorSlotPairTokens pair)) := by
  rw [crossingOwnershipShiftFields_descriptorSlotPairTokens]
  unfold paddedCrossingCarrierNodeCandidates crossingActivations
    crossingCarrierNodeTemplateBlocks crossingOwnershipShiftExpressions
    crossingOwnershipShiftExpressionBlocks
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
          RouteDescriptorPairAffine.occurrencePairCrossingOwnershipShiftExpressionBlock
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
            RouteDescriptorPairAffine.occurrencePairCrossingOwnershipShiftExpressionBlock_forall₂
              (field := field) (occurrences := slot.occurrences)
              (active := slot.evalTokens (descriptorSlotPairTokens pair))
              (pair := (pair.1.1, pair.2.1))
          intro shift _shiftMember active
          have bounds :=
            slot.crossingPointBounds_of_mem_crossingSlots_of_active
              (slotsMember slot (List.mem_cons_self)) pair active
          have periodPositive : 0 < pair.1.1.gridSize := by omega
          exact crossingRecordPeriodShiftAtPeriod_periodTranslate
            periodPositive _ shift bounds
        · exact induction fun remaining remainingMember =>
            slotsMember remaining
              (List.mem_cons_of_mem slot remainingMember)
  exact aligned crossingSlots (fun _ member => member)

theorem paddedCrossingCarrierNodeCandidateStream_ownershipShift_forall₂
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
          crossingOwnershipShiftFields field
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
          crossingOwnershipShiftFields field
            (descriptorSlotPairTokens pair)) := by
    intro pairs pairPeriodEq
    induction pairs with
    | nil => exact List.Forall₂.nil
    | cons pair pairs induction =>
        simp only [List.flatMap_cons]
        apply List.Forall₂.append
        · have pairAligned :=
            paddedCrossingCarrierNodeCandidates_ownershipShift_forall₂
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
