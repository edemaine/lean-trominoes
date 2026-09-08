/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateCandidateAlignment
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment

/-! # Canonical terminal fields in the exact activated node order -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
open PaddedSupportedCandidateBlocks PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

theorem RouteShape.canonicalTerminalCoordinateCandidates_forall₂
    (shape : RouteShape) (coordinateHorizontal keepPositive : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCanonicalCoordinateFieldAtPeriod coordinateHorizontal keepPositive pair.1.gridSize node)
      (candidates
        (shape.terminalDirectionalPredicates.map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (shape.terminalDirectionalCarrierNodeTemplateBlocks pair))
      ((shape.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal).flatten.map
        fun expression =>
          normalizedExpressionField keepPositive expression pair) := by
  unfold RouteShape.terminalDirectionalPredicates
    RouteShape.terminalDirectionalCarrierNodeTemplateBlocks
    RouteShape.canonicalTerminalCoordinateExpressionBlocks
  rw [← shape.gaugedSegments_map_segment]
  simp only [List.flatMap_map, List.zipIdx_map]
  have aligned : ∀ (gaugedSegments : List GaugedSegment) (start : Nat),
      (∀ gauged ∈ gaugedSegments, gauged.HasPeriodGauges pair) →
      List.Forall₂
        (fun candidate value => ∀ node,
          candidate.value = some node →
            value = carrierNodeCanonicalCoordinateFieldAtPeriod coordinateHorizontal keepPositive pair.1.gridSize node)
        (candidates
          (gaugedSegments.flatMap fun gauged =>
            (gauged.segment.terminalDirectionalPredicates shape).map fun predicate =>
              predicate.evalTokens (descriptorPairTokens pair))
          ((gaugedSegments.zipIdx start).flatMap fun tagged =>
            tagged.1.segment.terminalDirectionalCarrierNodeTemplateBlocks pair tagged.2))
        ((gaugedSegments.flatMap fun gauged =>
          gauged.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal).flatten.map
            fun expression =>
              normalizedExpressionField
                keepPositive expression pair) := by
    intro gaugedSegments start correct
    induction gaugedSegments generalizing start with
    | nil => exact List.Forall₂.nil
    | cons gauged remaining induction =>
        simp only [List.flatMap_cons, List.zipIdx_cons,
          List.flatten_append, List.map_append]
        rw [candidates_append]
        · exact List.Forall₂.append
            (gauged.canonicalTerminalCoordinateCandidates_forall₂
              shape start coordinateHorizontal keepPositive pair
              (correct gauged (List.mem_cons_self)))
            (induction (start + 1) fun remainingGauged member =>
              correct remainingGauged
                (List.mem_cons_of_mem gauged member))
        · rfl
  simpa [List.map_flatMap, Function.comp_def] using
    aligned (shape.gaugedSegments .first) 0
      (shape.gaugedSegments_forall_hasPeriodGauges pair bounds)

theorem canonicalTerminalCoordinateCarrierNodeCandidates_forall₂
    (coordinateHorizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor)
    (bounds : pair.1.CoordinateBounds) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCanonicalCoordinateFieldAtPeriod
            coordinateHorizontal keepPositive pair.1.gridSize node)
      (terminalDirectionalCarrierNodeCandidates pair)
      (canonicalTerminalCoordinateFields coordinateHorizontal keepPositive
        (descriptorPairTokens pair)) := by
  rw [canonicalTerminalCoordinateFields_descriptorPairTokens]
  unfold terminalDirectionalCarrierNodeCandidates
    terminalDirectionalPredicates
    terminalDirectionalCarrierNodeTemplateBlocks
    canonicalTerminalCoordinateExpressions

  have flattened :
      (allRouteShapes.flatMap
          (fun shape => shape.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal)).flatten =
        allRouteShapes.flatMap fun shape =>
          (shape.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal).flatten := by
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
          (shape.canonicalTerminalCoordinateCandidates_forall₂ coordinateHorizontal keepPositive pair bounds)
          induction
  · intro shape _shapeMember
    simp [RouteShape.terminalDirectionalPredicates,
      RouteShape.terminalDirectionalCarrierNodeTemplateBlocks,
      Segment.terminalDirectionalCarrierNodeTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
