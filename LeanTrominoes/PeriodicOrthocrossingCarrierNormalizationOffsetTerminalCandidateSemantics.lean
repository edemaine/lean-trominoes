/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalPrototypeGaugeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Terminal normalization-offset fields aligned with carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierNormalizationOffsetField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

theorem normalizedNormalizationOffsetExpression_eq_offsetValue
    (field : Field) (translate gauge : Cell)
    (pair : RouteDescriptor × RouteDescriptor) :
    normalizedExpressionField (keepPositive field)
        (normalizationOffsetExpression field translate gauge) pair =
      offsetValue field (Cell.add translate gauge) := by
  cases field <;>
    simp [normalizedExpressionField, normalizationOffsetExpression,
      offsetValue, CarrierNormalizationOffsetField.horizontal,
      CarrierNormalizationOffsetField.keepPositive,
      Expression.evalPair, Expression.eval, Cell.add]

@[simp] theorem terminalNormalizationOffsetFields_descriptorPairTokens
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    terminalNormalizationOffsetFields field (descriptorPairTokens pair) =
      (terminalNormalizationOffsetExpressions field).map fun expression =>
        normalizedExpressionField (keepPositive field) expression pair := by
  have evalEq : ∀ expression : Expression,
      expression.eval (tokenFieldValue (descriptorPairTokens pair)) =
        expression.evalPair pair := by
    intro expression
    simpa [Expression.evalTokens] using
      expression.evalTokens_descriptorPairTokens pair
  cases field <;>
    simp [terminalNormalizationOffsetFields, normalizedExpressionField,
      CarrierNormalizationOffsetField.keepPositive, evalEq]

theorem GaugedSegment.terminalNormalizationOffsetExpressionBlock_forall₂
    (gauged : GaugedSegment) (segmentIndex : Nat)
    (field : Field) (active : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (correct : gauged.HasPeriodGauges pair) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      ((gauged.segment.terminalCarrierNodeTemplateBlock
        pair segmentIndex).map (Template.activate active))
      ((gauged.terminalNormalizationOffsetExpressionBlock field).map
        fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
    GaugedSegment.terminalNormalizationOffsetExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  induction neighborTranslations with
  | nil => exact List.Forall₂.nil
  | cons translate translations induction =>
      simp only [List.flatMap_cons, List.map_cons, List.map_nil]
      apply List.Forall₂.append
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              change _ = offsetValue field
                (Cell.add translate
                  (carrierPositionGaugeAtPeriod pair.1.gridSize
                    (segmentTerminalPositionAtPeriod pair.1.gridSize
                      ⟨⟨pair.1.edgeIndex, segmentIndex,
                          gauged.segment.evalPair pair⟩,
                        (0, 0), .start⟩)))
              rw [gauged.terminalPrototypeGauge_eq pair correct
                segmentIndex .start]
              exact normalizedNormalizationOffsetExpression_eq_offsetValue
                field translate gauged.startGauge pair
        · apply List.Forall₂.cons
          · intro node valueEq
            cases active with
            | false => simp [Template.activate] at valueEq
            | true =>
                simp only [Template.activate, Bool.true_and, if_true,
                  Option.some.injEq] at valueEq
                subst node
                change _ = offsetValue field
                  (Cell.add translate
                    (carrierPositionGaugeAtPeriod pair.1.gridSize
                      (segmentTerminalPositionAtPeriod pair.1.gridSize
                        ⟨⟨pair.1.edgeIndex, segmentIndex,
                            gauged.segment.evalPair pair⟩,
                          (0, 0), .finish⟩)))
                rw [gauged.terminalPrototypeGauge_eq pair correct
                  segmentIndex .finish]
                exact normalizedNormalizationOffsetExpression_eq_offsetValue
                  field translate gauged.finishGauge pair
          · exact List.Forall₂.nil
      · exact induction

theorem GaugedSegment.terminalNormalizationOffsetCandidates_forall₂
    (gauged : GaugedSegment) (shape : RouteShape) (segmentIndex : Nat)
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (correct : gauged.HasPeriodGauges pair) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      (candidates
        ((gauged.segment.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (gauged.segment.terminalCarrierNodeTemplateBlocks pair segmentIndex))
      ((gauged.terminalNormalizationOffsetExpressionBlocks field).flatten.map
        fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold Segment.carrierAxisPredicates
    Segment.terminalCarrierNodeTemplateBlocks
    GaugedSegment.terminalNormalizationOffsetExpressionBlocks
  simp only [List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, candidates, List.map_append]
  exact List.Forall₂.append
    (gauged.terminalNormalizationOffsetExpressionBlock_forall₂
      segmentIndex field _ pair correct)
    (gauged.terminalNormalizationOffsetExpressionBlock_forall₂
      segmentIndex field _ pair correct)

theorem RouteShape.terminalNormalizationOffsetCandidates_forall₂
    (shape : RouteShape) (field : Field)
    (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      (candidates
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierNodeTemplateBlocks pair))
      ((shape.terminalNormalizationOffsetExpressionBlocks field).flatten.map
        fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold RouteShape.carrierSegmentPredicates
    RouteShape.terminalCarrierNodeTemplateBlocks
    RouteShape.terminalNormalizationOffsetExpressionBlocks
  rw [← shape.gaugedSegments_map_segment]
  simp only [List.flatMap_map, List.zipIdx_map]
  have aligned : ∀ (gaugedSegments : List GaugedSegment) (start : Nat),
      (∀ gauged ∈ gaugedSegments, gauged.HasPeriodGauges pair) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field pair.1.gridSize node)
        (candidates
          (gaugedSegments.flatMap fun gauged =>
            (gauged.segment.carrierAxisPredicates shape).map fun predicate =>
              predicate.evalTokens (descriptorPairTokens pair))
          ((gaugedSegments.zipIdx start).flatMap fun tagged =>
            tagged.1.segment.terminalCarrierNodeTemplateBlocks pair tagged.2))
        ((gaugedSegments.flatMap fun gauged =>
          gauged.terminalNormalizationOffsetExpressionBlocks field).flatten.map
            fun expression =>
              normalizedExpressionField
                (keepPositive field) expression pair) := by
    intro gaugedSegments start correct
    induction gaugedSegments generalizing start with
    | nil => exact List.Forall₂.nil
    | cons gauged remaining induction =>
        simp only [List.flatMap_cons, List.zipIdx_cons,
          List.flatten_append, List.map_append]
        rw [candidates_append]
        · exact List.Forall₂.append
            (gauged.terminalNormalizationOffsetCandidates_forall₂
              shape start field pair
              (correct gauged (List.mem_cons_self)))
            (induction (start + 1) fun remainingGauged member =>
              correct remainingGauged
                (List.mem_cons_of_mem gauged member))
        · rfl
  simpa [List.map_flatMap, Function.comp_def] using
    aligned (shape.gaugedSegments .first) 0
      (shape.gaugedSegments_forall_hasPeriodGauges pair bounds)

theorem paddedTerminalCarrierNodeCandidates_normalizationOffset_forall₂
    (field : Field) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field pair.1.gridSize node)
      (paddedTerminalCarrierNodeCandidates pair)
      (terminalNormalizationOffsetFields field
        (descriptorPairTokens pair)) := by
  rw [terminalNormalizationOffsetFields_descriptorPairTokens]
  unfold paddedTerminalCarrierNodeCandidates terminalCarrierKeyActivations
    carrierSegmentPredicates terminalCarrierNodeTemplateBlocks
    terminalNormalizationOffsetExpressions
    terminalNormalizationOffsetExpressionBlocks
  have flattened :
      (allRouteShapes.flatMap fun shape =>
          shape.terminalNormalizationOffsetExpressionBlocks field).flatten =
        allRouteShapes.flatMap fun shape =>
          (shape.terminalNormalizationOffsetExpressionBlocks field).flatten := by
    induction allRouteShapes with
    | nil => rfl
    | cons shape shapes induction =>
        simp only [List.flatMap_cons, List.flatten_append]
        rw [induction]
  rw [List.map_flatMap, flattened, List.map_flatMap]
  rw [candidates_flatMap]
  · induction allRouteShapes with
    | nil => exact List.Forall₂.nil
    | cons shape shapes induction =>
        simp only [List.flatMap_cons]
        exact List.Forall₂.append
          (shape.terminalNormalizationOffsetCandidates_forall₂
            field pair bounds)
          induction
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierNodeTemplateBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks]

theorem paddedTerminalCarrierNodeCandidateStream_normalizationOffset_forall₂
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period)
    (descriptorBounds : ∀ descriptor ∈ descriptors,
      descriptor.CoordinateBounds) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (paddedTerminalCarrierNodeCandidateStream descriptors)
      ((descriptors ×ˢ descriptors).flatMap fun pair =>
        terminalNormalizationOffsetFields field
          (descriptorPairTokens pair)) := by
  unfold paddedTerminalCarrierNodeCandidateStream
  have aligned : ∀ pairs : List (RouteDescriptor × RouteDescriptor),
      (∀ pair ∈ pairs, pair.1 ∈ descriptors) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field period node)
        (pairs.flatMap paddedTerminalCarrierNodeCandidates)
        (pairs.flatMap fun pair =>
          terminalNormalizationOffsetFields field
            (descriptorPairTokens pair)) := by
    intro pairs firstMember
    induction pairs with
    | nil => exact List.Forall₂.nil
    | cons pair remaining induction =>
        simp only [List.flatMap_cons]
        have pairAligned :=
          paddedTerminalCarrierNodeCandidates_normalizationOffset_forall₂
            field pair
            (descriptorBounds pair.1
              (firstMember pair (List.mem_cons_self)))
        have pairPeriod := periodEq pair.1
          (firstMember pair (List.mem_cons_self))
        exact List.Forall₂.append
          (by simpa [pairPeriod] using pairAligned)
          (induction fun remainingPair remainingMember =>
            firstMember remainingPair
              (List.mem_cons_of_mem pair remainingMember))
  exact aligned (descriptors ×ˢ descriptors) fun pair pairMember =>
    (List.mem_product.mp pairMember).1

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
