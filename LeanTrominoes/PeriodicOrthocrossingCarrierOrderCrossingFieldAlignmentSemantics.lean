/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics

/-! # Crossing order fields aligned with active semantic nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

theorem occurrencePairCrossingOrderExpressionShiftBlock_forall₂
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (active keepPositive : Bool)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeOrderFieldAtPeriod
            keepPositive pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map (Template.activate active))
      ((occurrencePairCrossingOrderExpressionShiftBlock
        occurrences shift).map fun expression =>
          normalizedExpressionField keepPositive expression pair) := by
  unfold occurrencePairCrossingCarrierNodeShiftTemplateBlock
    occurrencePairCrossingOrderExpressionShiftBlock
  simp only [List.map_cons, List.map_nil]
  apply List.Forall₂.cons
  · intro node valueEq
    cases active with
    | false => simp [Template.activate] at valueEq
    | true =>
        simp only [Template.activate, Bool.true_and, if_true,
          Option.some.injEq] at valueEq
        subst node
        have coordinateEq := occurrencePairCrossingOrderExpression_evalPair
          occurrences shift .left pair
        cases keepPositive <;>
          simp [normalizedExpressionField, carrierNodeOrderFieldAtPeriod,
            coordinateEq]
  · apply List.Forall₂.cons
    · intro node valueEq
      cases active with
      | false => simp [Template.activate] at valueEq
      | true =>
          simp only [Template.activate, Bool.true_and, if_true,
            Option.some.injEq] at valueEq
          subst node
          have coordinateEq := occurrencePairCrossingOrderExpression_evalPair
            occurrences shift .right pair
          cases keepPositive <;>
            simp [normalizedExpressionField, carrierNodeOrderFieldAtPeriod,
              coordinateEq]
    · apply List.Forall₂.cons
      · intro node valueEq
        cases active with
        | false => simp [Template.activate] at valueEq
        | true =>
            simp only [Template.activate, Bool.true_and, if_true,
              Option.some.injEq] at valueEq
            subst node
            have coordinateEq :=
              occurrencePairCrossingOrderExpression_evalPair
                occurrences shift .top pair
            cases keepPositive <;>
              simp [normalizedExpressionField, carrierNodeOrderFieldAtPeriod,
                coordinateEq]
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              have coordinateEq :=
                occurrencePairCrossingOrderExpression_evalPair
                  occurrences shift .bottom pair
              cases keepPositive <;>
                simp [normalizedExpressionField,
                  carrierNodeOrderFieldAtPeriod, coordinateEq]
        · exact List.Forall₂.nil

theorem occurrencePairCrossingOrderExpressionBlock_forall₂
    (occurrences : Occurrence × Occurrence) (active keepPositive : Bool)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeOrderFieldAtPeriod
            keepPositive pair.1.gridSize node)
      ((occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map (Template.activate active))
      ((occurrencePairCrossingOrderExpressionBlock occurrences).map
        fun expression =>
          normalizedExpressionField keepPositive expression pair) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairCrossingOrderExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  induction carrierCrossingRetentionShifts with
  | nil => exact List.Forall₂.nil
  | cons shift shifts induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append
        (occurrencePairCrossingOrderExpressionShiftBlock_forall₂
          occurrences shift active keepPositive pair)
        induction

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem crossingOrderFields_descriptorSlotPairTokens
    (keepPositive : Bool) (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingOrderFields keepPositive (descriptorSlotPairTokens pair) =
      crossingOrderExpressions.map fun expression =>
        RouteDescriptorPairAffine.normalizedExpressionField keepPositive
          expression (pair.1.1, pair.2.1) := by
  unfold crossingOrderFields
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
  cases keepPositive <;>
    simp [RouteDescriptorPairAffine.normalizedExpressionField,
      evalEq]

theorem paddedCrossingCarrierNodeCandidates_forall₂
    (keepPositive : Bool) (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeOrderFieldAtPeriod
            keepPositive pair.1.1.gridSize node)
      (paddedCrossingCarrierNodeCandidates pair)
      (crossingOrderFields keepPositive
        (descriptorSlotPairTokens pair)) := by
  rw [crossingOrderFields_descriptorSlotPairTokens]
  unfold paddedCrossingCarrierNodeCandidates crossingActivations
    crossingCarrierNodeTemplateBlocks crossingOrderExpressions
    crossingOrderExpressionBlocks
  induction crossingSlots with
  | nil => exact List.Forall₂.nil
  | cons slot slots induction =>
      simp only [List.map_cons, List.flatten_cons, candidates,
        List.map_append]
      exact List.Forall₂.append
        (RouteDescriptorPairAffine.occurrencePairCrossingOrderExpressionBlock_forall₂
          slot.occurrences (slot.evalTokens (descriptorSlotPairTokens pair))
          keepPositive (pair.1.1, pair.2.1))
        induction

theorem paddedCrossingCarrierNodeCandidateStream_forall₂
    (keepPositive : Bool) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeOrderFieldAtPeriod keepPositive period node)
      (paddedCrossingCarrierNodeCandidateStream descriptors)
      ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          crossingOrderFields keepPositive
            (descriptorSlotPairTokens pair)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  have aligned : ∀ pairs : List (TaggedDescriptor × TaggedDescriptor),
      (∀ pair ∈ pairs, pair.1.1.gridSize = period) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = carrierNodeOrderFieldAtPeriod
              keepPositive period node)
        (pairs.flatMap paddedCrossingCarrierNodeCandidates)
        (pairs.flatMap fun pair =>
          crossingOrderFields keepPositive
            (descriptorSlotPairTokens pair)) := by
    intro pairs pairPeriodEq
    induction pairs with
    | nil => exact List.Forall₂.nil
    | cons pair pairs induction =>
        simp only [List.flatMap_cons]
        apply List.Forall₂.append
        · have pairAligned :=
            paddedCrossingCarrierNodeCandidates_forall₂ keepPositive pair
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
    have descriptorEq : descriptor = pair.1.1 :=
      congrArg Prod.fst taggedEq
    exact descriptorEq ▸ descriptorMember
  exact periodEq pair.1.1 firstMember

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
