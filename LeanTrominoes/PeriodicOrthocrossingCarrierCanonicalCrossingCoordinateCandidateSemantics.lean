/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalCrossingCoordinateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCrossingCandidateSemantics

/-! # Canonical affine fields agree with every active crossing candidate -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
open RouteDescriptorPairAffine CarrierCrossingPointField
open RouteDescriptorOccurrenceSlotCrossing RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open PaddedSupportedCandidateBlocks PaddedSupportedLastRepresentativeEqualityRows

theorem shiftBlock_forall₂ (offset : CrossingSide → Cell) (field : Field)
    (occurrences : Occurrence × Occurrence) (shift : Cell) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (bounds : active = true →
      let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
        (occurrences.1.evalPair .first pair, occurrences.2.evalPair .second pair)
      0 ≤ record.point.1 ∧ record.point.1 < pair.1.gridSize ∧
        0 ≤ record.point.2 ∧ record.point.2 < pair.1.gridSize) :
    List.Forall₂
      (fun candidate value => ∀ node, candidate.value = some node →
        value = nodeValue offset field pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock pair occurrences shift).map
        (Template.activate active))
      ((shiftBlock offset field occurrences shift).map fun expression =>
        normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeShiftTemplateBlock shiftBlock
  simp only [List.map_cons, List.map_nil]
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ List.Forall₂.nil)))
  all_goals
    intro node valueEq
    cases active with
    | false => simp [Template.activate] at valueEq
    | true =>
        simp only [Template.activate, Bool.true_and, if_true, Option.some.injEq] at valueEq
        subst node
        exact expression_eq_nodeValue offset field occurrences shift _ pair (bounds rfl)

theorem occurrenceBlock_forall₂ (offset : CrossingSide → Cell) (field : Field)
    (occurrences : Occurrence × Occurrence) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (bounds : active = true →
      let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
        (occurrences.1.evalPair .first pair, occurrences.2.evalPair .second pair)
      0 ≤ record.point.1 ∧ record.point.1 < pair.1.gridSize ∧
        0 ≤ record.point.2 ∧ record.point.2 < pair.1.gridSize) :
    List.Forall₂
      (fun candidate value => ∀ node, candidate.value = some node →
        value = nodeValue offset field pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeTemplateBlock pair occurrences).map (Template.activate active))
      ((occurrenceBlock offset field occurrences).map fun expression =>
        normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock occurrenceBlock
  rw [List.map_flatMap, List.map_flatMap]
  induction carrierCrossingRetentionShifts with
  | nil => exact List.Forall₂.nil
  | cons shift shifts induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append (shiftBlock_forall₂ offset field occurrences shift active pair bounds) induction

theorem candidates_forall₂ (offset : CrossingSide → Cell) (field : Field)
    (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node, candidate.value = some node →
        value = nodeValue offset field pair.1.1.gridSize node)
      (paddedCrossingCarrierNodeCandidates pair)
      (fields offset field (descriptorSlotPairTokens pair)) := by
  rw [fields_descriptorSlotPairTokens]
  unfold paddedCrossingCarrierNodeCandidates crossingActivations
    crossingCarrierNodeTemplateBlocks expressions
  have aligned : ∀ slots : List Slot,
      (∀ slot ∈ slots, slot ∈ crossingSlots) →
      List.Forall₂
        (fun candidate value => ∀ node, candidate.value = some node →
          value = nodeValue offset field pair.1.1.gridSize node)
        (candidates (slots.map fun slot => slot.evalTokens (descriptorSlotPairTokens pair))
          (slots.map fun slot => slot.carrierNodeTemplateBlock (pair.1.1, pair.2.1)))
        ((slots.map fun slot => occurrenceBlock offset field slot.occurrences).flatten.map
          fun expression => normalizedExpressionField (keepPositive field) expression (pair.1.1, pair.2.1)) := by
    intro slots slotsMember
    induction slots with
    | nil => exact List.Forall₂.nil
    | cons slot slots induction =>
        simp only [List.map_cons, List.flatten_cons, candidates, List.map_append]
        apply List.Forall₂.append
        · unfold Slot.carrierNodeTemplateBlock
          apply occurrenceBlock_forall₂ (offset := offset) (field := field)
            (occurrences := slot.occurrences)
            (active := slot.evalTokens (descriptorSlotPairTokens pair))
            (pair := (pair.1.1, pair.2.1))
          intro active
          exact slot.crossingPointBounds_of_mem_crossingSlots_of_active
            (slotsMember slot List.mem_cons_self) pair active
        · exact induction fun remaining member => slotsMember remaining (List.mem_cons_of_mem slot member)
  exact aligned crossingSlots (fun _ member => member)

theorem stream_forall₂
    (offset : CrossingSide → Cell) (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValue offset field period node)
      (paddedCrossingCarrierNodeCandidateStream descriptors)
      ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          fields offset field
            (descriptorSlotPairTokens pair)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  have aligned : ∀ pairs : List (TaggedDescriptor × TaggedDescriptor),
      (∀ pair ∈ pairs, pair.1.1.gridSize = period) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValue offset field period node)
        (pairs.flatMap paddedCrossingCarrierNodeCandidates)
        (pairs.flatMap fun pair =>
          fields offset field
            (descriptorSlotPairTokens pair)) := by
    intro pairs pairPeriodEq
    induction pairs with
    | nil => exact List.Forall₂.nil
    | cons pair pairs induction =>
        simp only [List.flatMap_cons]
        apply List.Forall₂.append
        · have pairAligned :=
            candidates_forall₂ offset field pair
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


end LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
end
