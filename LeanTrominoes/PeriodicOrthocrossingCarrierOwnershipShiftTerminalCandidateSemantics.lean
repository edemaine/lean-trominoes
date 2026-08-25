/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData

/-! # Terminal ownership-shift fields aligned with carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierOwnershipShiftField
open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

theorem normalizedOwnershipShiftExpression_eq_shiftValue
    (field : Field) (shift : Cell)
    (pair : RouteDescriptor × RouteDescriptor) :
    normalizedExpressionField (keepPositive field)
        (ownershipShiftExpression field shift) pair =
      shiftValue field shift := by
  cases field <;>
    simp [normalizedExpressionField, ownershipShiftExpression,
      shiftValue, CarrierOwnershipShiftField.horizontal,
      CarrierOwnershipShiftField.keepPositive,
      Expression.evalPair, Expression.eval]

@[simp] theorem terminalOwnershipShiftFields_descriptorPairTokens
    (field : Field) (pair : RouteDescriptor × RouteDescriptor) :
    terminalOwnershipShiftFields field (descriptorPairTokens pair) =
      (terminalOwnershipShiftExpressions field).map fun expression =>
        normalizedExpressionField (keepPositive field) expression pair := by
  have evalEq : ∀ expression : Expression,
      expression.eval (tokenFieldValue (descriptorPairTokens pair)) =
        expression.evalPair pair := by
    intro expression
    simpa [Expression.evalTokens] using
      expression.evalTokens_descriptorPairTokens pair
  cases field <;>
    simp [terminalOwnershipShiftFields, normalizedExpressionField,
      CarrierOwnershipShiftField.keepPositive, evalEq]

theorem Segment.terminalOwnershipShiftExpressionBlock_forall₂
    (segment : Segment) (segmentIndex : Nat)
    (field : Field) (active : Bool) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      ((segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.activate active))
      ((segment.terminalOwnershipShiftExpressionBlock field).map
        fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
    Segment.terminalOwnershipShiftExpressionBlock
  rw [List.map_flatMap, List.map_flatMap]
  induction neighborTranslations with
  | nil => exact List.Forall₂.nil
  | cons translate translations induction =>
      simp only [List.flatMap_cons, List.replicate_succ,
        List.replicate_zero, List.map_cons, List.map_nil]
      apply List.Forall₂.append
      · apply List.Forall₂.cons
        · intro node valueEq
          cases active with
          | false => simp [Template.activate] at valueEq
          | true =>
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              exact normalizedOwnershipShiftExpression_eq_shiftValue
                field translate pair
        · apply List.Forall₂.cons
          · intro node valueEq
            cases active with
            | false => simp [Template.activate] at valueEq
            | true =>
                simp only [Template.activate, Bool.true_and, if_true,
                  Option.some.injEq] at valueEq
                subst node
                exact normalizedOwnershipShiftExpression_eq_shiftValue
                  field translate pair
          · exact List.Forall₂.nil
      · exact induction

theorem Segment.terminalOwnershipShiftCandidates_forall₂
    (segment : Segment) (shape : RouteShape) (segmentIndex : Nat)
    (field : Field) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (candidates
        ((segment.carrierAxisPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex))
      ((segment.terminalOwnershipShiftExpressionBlocks field).flatten.map
        fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold Segment.carrierAxisPredicates
    Segment.terminalCarrierNodeTemplateBlocks
    Segment.terminalOwnershipShiftExpressionBlocks
  simp only [List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, candidates, List.map_append]
  exact List.Forall₂.append
    (segment.terminalOwnershipShiftExpressionBlock_forall₂
      segmentIndex field _ period pair)
    (segment.terminalOwnershipShiftExpressionBlock_forall₂
      segmentIndex field _ period pair)

theorem RouteShape.terminalOwnershipShiftCandidates_forall₂
    (shape : RouteShape) (field : Field) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (candidates
        (shape.carrierSegmentPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalCarrierNodeTemplateBlocks pair))
      ((shape.terminalOwnershipShiftExpressionBlocks field).flatten.map
        fun expression =>
          normalizedExpressionField (keepPositive field) expression pair) := by
  unfold RouteShape.carrierSegmentPredicates
    RouteShape.terminalCarrierNodeTemplateBlocks
    RouteShape.terminalOwnershipShiftExpressionBlocks
  rw [List.map_flatMap]
  have aligned : ∀ (segments : List Segment) (start : Nat),
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = nodeValueAtPeriod field period node)
        (candidates
          (segments.flatMap fun segment =>
            (segment.carrierAxisPredicates shape).map fun predicate =>
              predicate.evalTokens (descriptorPairTokens pair))
          ((segments.zipIdx start).flatMap fun tagged =>
            tagged.1.terminalCarrierNodeTemplateBlocks pair tagged.2))
        ((segments.flatMap fun segment =>
          segment.terminalOwnershipShiftExpressionBlocks field).flatten.map
            fun expression =>
              normalizedExpressionField
                (keepPositive field) expression pair) := by
    intro segments start
    induction segments generalizing start with
    | nil => exact List.Forall₂.nil
    | cons segment segments induction =>
        simp only [List.flatMap_cons, List.zipIdx_cons,
          List.flatten_append, List.map_append]
        rw [candidates_append]
        · exact List.Forall₂.append
            (segment.terminalOwnershipShiftCandidates_forall₂
              shape start field period pair)
            (induction (start + 1))
        · rfl
  exact aligned (shape.segments .first) 0

theorem paddedTerminalCarrierNodeCandidates_ownershipShift_forall₂
    (field : Field) (period : Nat)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (paddedTerminalCarrierNodeCandidates pair)
      (terminalOwnershipShiftFields field (descriptorPairTokens pair)) := by
  rw [terminalOwnershipShiftFields_descriptorPairTokens]
  unfold paddedTerminalCarrierNodeCandidates terminalCarrierKeyActivations
    carrierSegmentPredicates terminalCarrierNodeTemplateBlocks
    terminalOwnershipShiftExpressions terminalOwnershipShiftExpressionBlocks
  have flattened :
      (allRouteShapes.flatMap fun shape =>
          shape.terminalOwnershipShiftExpressionBlocks field).flatten =
        allRouteShapes.flatMap fun shape =>
          (shape.terminalOwnershipShiftExpressionBlocks field).flatten := by
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
          (shape.terminalOwnershipShiftCandidates_forall₂
            field period pair)
          induction
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierNodeTemplateBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierNodeTemplateBlocks]

theorem paddedTerminalCarrierNodeCandidateStream_ownershipShift_forall₂
    (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = nodeValueAtPeriod field period node)
      (paddedTerminalCarrierNodeCandidateStream descriptors)
      ((descriptors ×ˢ descriptors).flatMap fun pair =>
        terminalOwnershipShiftFields field (descriptorPairTokens pair)) := by
  unfold paddedTerminalCarrierNodeCandidateStream
  induction (descriptors ×ˢ descriptors) with
  | nil => exact List.Forall₂.nil
  | cons pair pairs induction =>
      simp only [List.flatMap_cons]
      exact List.Forall₂.append
        (paddedTerminalCarrierNodeCandidates_ownershipShift_forall₂
          field period pair)
        induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
