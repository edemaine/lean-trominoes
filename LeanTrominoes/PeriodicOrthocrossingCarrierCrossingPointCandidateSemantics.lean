/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics

/-! # Alignment of crossing-point fields with crossing candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierCrossingPointField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

theorem normalizedCrossingPointExpression_eq_nodeValue
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) (side : CrossingSide)
    (pair : RouteDescriptor × RouteDescriptor) :
    normalizedExpressionField (keepPositive field)
        ((occurrencePairCrossingPointAtShift occurrences shift).axisExpression
          (horizontal field)) pair =
      nodeValue field
        (.boundary
          ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
              (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
                (occurrences.1.evalPair .first pair,
                  occurrences.2.evalPair .second pair)) shift,
            side⟩) := by
  have pointEq := occurrencePairCrossingPointAtShift_evalPair
    occurrences shift pair
  have horizontalEq := congrArg Prod.fst pointEq
  have verticalEq := congrArg Prod.snd pointEq
  change
    (occurrencePairCrossingPointAtShift occurrences shift).horizontal.evalPair
        pair = _ at horizontalEq
  change
    (occurrencePairCrossingPointAtShift occurrences shift).vertical.evalPair
        pair = _ at verticalEq
  cases field <;>
    simp [normalizedExpressionField, Point.axisExpression,
      nodeValue, pointValue, horizontal, keepPositive,
      horizontalEq, verticalEq]

theorem occurrencePairCrossingPointExpressionShiftBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      ((occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift).map (Template.activate active))
      ((occurrencePairCrossingPointExpressionShiftBlock
        field occurrences shift).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeShiftTemplateBlock
    occurrencePairCrossingPointExpressionShiftBlock
  simp only [List.map_cons, List.map_nil]
  apply List.Forall₂.cons
  · intro node valueEq
    cases active with
    | false => simp [Template.activate] at valueEq
    | true =>
        simp only [Template.activate, Bool.true_and, if_true,
          Option.some.injEq] at valueEq
        subst node
        exact normalizedCrossingPointExpression_eq_nodeValue
          field occurrences shift .left pair
  · apply List.Forall₂.cons
    · intro node valueEq
      cases active with
      | false => simp [Template.activate] at valueEq
      | true =>
          simp only [Template.activate, Bool.true_and, if_true,
            Option.some.injEq] at valueEq
          subst node
          exact normalizedCrossingPointExpression_eq_nodeValue
            field occurrences shift .right pair
    · apply List.Forall₂.cons
      · intro node valueEq
        cases active with
        | false => simp [Template.activate] at valueEq
        | true =>
            simp only [Template.activate, Bool.true_and, if_true,
              Option.some.injEq] at valueEq
            subst node
            exact normalizedCrossingPointExpression_eq_nodeValue
              field occurrences shift .top pair
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              exact normalizedCrossingPointExpression_eq_nodeValue
                field occurrences shift .bottom pair
        · exact List.Forall₂.nil

theorem occurrencePairCrossingPointExpressionBlock_forall₂
    (field : Field) (occurrences : Occurrence × Occurrence)
    (active : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      ((occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map (Template.activate active))
      ((occurrencePairCrossingPointExpressionBlock
        field occurrences).map fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairCrossingPointExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  induction carrierCrossingRetentionShifts with
  | nil => exact List.Forall₂.nil
  | cons shift shifts induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append
        (occurrencePairCrossingPointExpressionShiftBlock_forall₂
          field occurrences shift active pair)
        induction

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierCrossingPointField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

@[simp] theorem crossingPointFields_descriptorSlotPairTokens
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingPointFields field (descriptorSlotPairTokens pair) =
      (crossingPointExpressions field).map fun expression =>
        RouteDescriptorPairAffine.normalizedExpressionField
          (keepPositive field) expression (pair.1.1, pair.2.1) := by
  unfold crossingPointFields
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
      keepPositive, evalEq]

theorem paddedCrossingCarrierNodeCandidates_point_forall₂
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (paddedCrossingCarrierNodeCandidates pair)
      (crossingPointFields field (descriptorSlotPairTokens pair)) := by
  rw [crossingPointFields_descriptorSlotPairTokens]
  unfold paddedCrossingCarrierNodeCandidates crossingActivations
    crossingCarrierNodeTemplateBlocks crossingPointExpressions
    crossingPointExpressionBlocks
  induction crossingSlots with
  | nil => exact List.Forall₂.nil
  | cons slot slots induction =>
      simp only [List.map_cons, List.flatten_cons, candidates,
        List.map_append]
      exact List.Forall₂.append
        (RouteDescriptorPairAffine.occurrencePairCrossingPointExpressionBlock_forall₂
            field slot.occurrences
            (slot.evalTokens (descriptorSlotPairTokens pair))
            (pair.1.1, pair.2.1))
        induction

theorem paddedCrossingCarrierNodeCandidateStream_point_forall₂
    (field : Field) (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node → value = nodeValue field node)
      (paddedCrossingCarrierNodeCandidateStream descriptors)
      ((taggedDescriptors descriptors ×ˢ
        taggedDescriptors descriptors).flatMap fun pair =>
          crossingPointFields field (descriptorSlotPairTokens pair)) := by
  unfold paddedCrossingCarrierNodeCandidateStream
  induction (taggedDescriptors descriptors ×ˢ
      taggedDescriptors descriptors) with
  | nil => exact List.Forall₂.nil
  | cons pair pairs induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append
        (paddedCrossingCarrierNodeCandidates_point_forall₂ field pair)
        induction

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
