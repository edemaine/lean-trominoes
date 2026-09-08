/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionTerminalCandidateAlignment

/-! # Both terminal coordinate streams aligned with physical nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

theorem RouteShape.terminalCoordinateCandidates_forall₂
    (shape : RouteShape) (coordinateHorizontal keepPositive : Bool)
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCoordinateFieldAtPeriod
            coordinateHorizontal keepPositive pair.1.gridSize node)
      (candidates
        (shape.terminalDirectionalPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalDirectionalCarrierNodeTemplateBlocks pair))
      (((shape.terminalCoordinateExpressionBlocks coordinateHorizontal).flatten).map
        fun expression =>
          normalizedExpressionField keepPositive expression pair) := by
  unfold RouteShape.terminalDirectionalPredicates
    RouteShape.terminalDirectionalCarrierNodeTemplateBlocks
    RouteShape.terminalCoordinateExpressionBlocks
  rw [List.map_flatMap]
  have aligned : ∀ (segments : List Segment) (start : Nat),
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = carrierNodeCoordinateFieldAtPeriod
              coordinateHorizontal keepPositive pair.1.gridSize node)
        (candidates
          (segments.flatMap fun segment =>
            (segment.terminalDirectionalPredicates shape).map
              fun predicate =>
                predicate.evalTokens (descriptorPairTokens pair))
          ((segments.zipIdx start).flatMap fun tagged =>
            tagged.1.terminalDirectionalCarrierNodeTemplateBlocks
              pair tagged.2))
        ((segments.flatMap
          (fun segment => segment.terminalCoordinateExpressionBlocks coordinateHorizontal)).flatten.map
            fun expression =>
              normalizedExpressionField keepPositive expression pair) := by
    intro segments start
    induction segments generalizing start with
    | nil => exact List.Forall₂.nil
    | cons segment segments induction =>
        simp only [List.flatMap_cons, List.zipIdx_cons,
          List.flatten_append, List.map_append]
        rw [candidates_append]
        · exact List.Forall₂.append
            (segment.terminalCoordinateCandidates_forall₂
              shape start coordinateHorizontal keepPositive pair)
            (induction (start + 1))
        · rfl
  exact aligned (shape.segments .first) 0

theorem terminalCoordinateCarrierNodeCandidates_forall₂
    (coordinateHorizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCoordinateFieldAtPeriod
            coordinateHorizontal keepPositive pair.1.gridSize node)
      (terminalDirectionalCarrierNodeCandidates pair)
      (terminalCoordinateFields coordinateHorizontal keepPositive
        (descriptorPairTokens pair)) := by
  rw [terminalCoordinateFields_descriptorPairTokens]
  unfold terminalDirectionalCarrierNodeCandidates
    terminalDirectionalPredicates
    terminalDirectionalCarrierNodeTemplateBlocks
    terminalCoordinateExpressions

  have flattened :
      (allRouteShapes.flatMap
          (fun shape => shape.terminalCoordinateExpressionBlocks coordinateHorizontal)).flatten =
        allRouteShapes.flatMap fun shape =>
          (shape.terminalCoordinateExpressionBlocks coordinateHorizontal).flatten := by
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
          (shape.terminalCoordinateCandidates_forall₂ coordinateHorizontal keepPositive pair)
          induction
  · intro shape _shapeMember
    simp [RouteShape.terminalDirectionalPredicates,
      RouteShape.terminalDirectionalCarrierNodeTemplateBlocks,
      Segment.terminalDirectionalCarrierNodeTemplateBlocks]

theorem terminalCoordinateCarrierNodeCandidateStream_forall₂
    (coordinateHorizontal keepPositive : Bool) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors,
      descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCoordinateFieldAtPeriod
            coordinateHorizontal keepPositive period node)
      (terminalDirectionalCarrierNodeCandidateStream descriptors)
      ((descriptors ×ˢ descriptors).flatMap fun pair =>
        terminalCoordinateFields coordinateHorizontal keepPositive
          (descriptorPairTokens pair)) := by
  unfold terminalDirectionalCarrierNodeCandidateStream
  have aligned : ∀ pairs : List (RouteDescriptor × RouteDescriptor),
      (∀ pair ∈ pairs, pair.1.gridSize = period) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = carrierNodeCoordinateFieldAtPeriod
              coordinateHorizontal keepPositive period node)
        (pairs.flatMap terminalDirectionalCarrierNodeCandidates)
        (pairs.flatMap fun pair =>
          terminalCoordinateFields coordinateHorizontal keepPositive
            (descriptorPairTokens pair)) := by
    intro pairs pairPeriodEq
    induction pairs with
    | nil => exact List.Forall₂.nil
    | cons pair pairs induction =>
        simp only [List.flatMap_cons]
        apply List.Forall₂.append
        · have pairAligned :=
            terminalCoordinateCarrierNodeCandidates_forall₂
              coordinateHorizontal keepPositive pair
          rw [pairPeriodEq pair (List.mem_cons_self)] at pairAligned
          exact pairAligned
        · exact induction fun remaining remainingMember =>
            pairPeriodEq remaining
              (List.mem_cons_of_mem pair remainingMember)
  apply aligned
  intro pair pairMember
  have firstMember : pair.1 ∈ descriptors := by
    simpa using (List.mem_product.mp pairMember).1
  exact periodEq pair.1 firstMember

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
