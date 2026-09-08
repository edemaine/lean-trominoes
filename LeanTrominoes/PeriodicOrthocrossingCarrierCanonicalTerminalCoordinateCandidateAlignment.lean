/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateBlockAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalCandidateFieldAlignmentSemantics

/-! # Canonical terminal position fields in the exact activated candidate order -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

theorem GaugedSegment.canonicalTerminalCoordinateCandidates_forall₂
    (gauged : GaugedSegment) (shape : RouteShape) (segmentIndex : Nat)
    (coordinateHorizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor)
    (correct : gauged.HasPeriodGauges pair) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCanonicalCoordinateFieldAtPeriod
            coordinateHorizontal keepPositive pair.1.gridSize node)
      (candidates
        ((gauged.segment.terminalDirectionalPredicates shape).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (gauged.segment.terminalDirectionalCarrierNodeTemplateBlocks
          pair segmentIndex))
      (((gauged.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal).flatten).map
        fun expression =>
          normalizedExpressionField keepPositive expression pair) := by
  let horizontalActive :=
    (all [carrierSegmentSameEdgeIndex, shape.guard .first,
      gauged.segment.carrierIsHorizontal]).evalPair pair
  let verticalActive :=
    (all [carrierSegmentSameEdgeIndex, shape.guard .first,
      gauged.segment.carrierIsVertical]).evalPair pair
  let horizontalIncreasing :=
    (gauged.segment.increasingPredicate true).evalPair pair
  let verticalIncreasing :=
    (gauged.segment.increasingPredicate false).evalPair pair
  have horizontalGeometry (active : horizontalActive = true) :
      (gauged.segment.evalPair pair).IsHorizontal := by
    apply gauged.segment.horizontal_of_terminalHorizontalActive shape pair
    change horizontalActive = true
    exact active
  have verticalGeometry (active : verticalActive = true) :
      (gauged.segment.evalPair pair).IsVertical := by
    apply gauged.segment.vertical_of_terminalVerticalActive shape pair
    change verticalActive = true
    exact active
  simp only [Segment.terminalDirectionalPredicates,
    Segment.terminalDirectionalCarrierNodeTemplateBlocks,
    GaugedSegment.canonicalTerminalCoordinateExpressionBlocks,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Predicate.evalTokens_descriptorPairTokens,
    Predicate.evalPair_conjunction, Predicate.evalPair_negation,
    candidates]
  change List.Forall₂ _
      ((gauged.segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
          (Template.activate (horizontalActive && !horizontalIncreasing)) ++
        (gauged.segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
          (Template.activate (horizontalActive && horizontalIncreasing)) ++
        (gauged.segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
          (Template.activate (verticalActive && !verticalIncreasing)) ++
        (gauged.segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
          (Template.activate (verticalActive && verticalIncreasing))) _
  simp only [List.map_append, List.append_assoc]
  apply List.Forall₂.append
  · apply gauged.canonicalTerminalCoordinateExpressionBlock_forall₂ (correct := correct)
    · intro active
      simp only [Bool.and_eq_true] at active
      have geometry := horizontalGeometry active.1
      simp [geometry]
    · intro active
      simp only [Bool.and_eq_true] at active
      change false = horizontalIncreasing
      cases increasingValue : horizontalIncreasing with
      | false => rfl
      | true => simp [increasingValue] at active
    · intro active
      simp only [Bool.and_eq_true] at active
      exact Or.inl (horizontalGeometry active.1)
  · apply List.Forall₂.append
    · apply gauged.canonicalTerminalCoordinateExpressionBlock_forall₂ (correct := correct)
      · intro active
        simp only [Bool.and_eq_true] at active
        have geometry := horizontalGeometry active.1
        simp [geometry]
      · intro active
        simp only [Bool.and_eq_true] at active
        change true = horizontalIncreasing
        exact active.2.symm
      · intro active
        simp only [Bool.and_eq_true] at active
        exact Or.inl (horizontalGeometry active.1)
    · apply List.Forall₂.append
      · apply gauged.canonicalTerminalCoordinateExpressionBlock_forall₂ (correct := correct)
        · intro active
          simp only [Bool.and_eq_true] at active
          have vertical := verticalGeometry active.1
          have notHorizontal : ¬(gauged.segment.evalPair pair).IsHorizontal := by
            intro horizontal
            exact vertical.2 horizontal.1
          simp [notHorizontal]
        · intro active
          simp only [Bool.and_eq_true] at active
          change false = verticalIncreasing
          cases increasingValue : verticalIncreasing with
          | false => rfl
          | true => simp [increasingValue] at active
        · intro active
          simp only [Bool.and_eq_true] at active
          exact Or.inr (verticalGeometry active.1)
      · apply gauged.canonicalTerminalCoordinateExpressionBlock_forall₂ (correct := correct)
        · intro active
          simp only [Bool.and_eq_true] at active
          have vertical := verticalGeometry active.1
          have notHorizontal : ¬(gauged.segment.evalPair pair).IsHorizontal := by
            intro horizontal
            exact vertical.2 horizontal.1
          simp [notHorizontal]
        · intro active
          simp only [Bool.and_eq_true] at active
          change true = verticalIncreasing
          exact active.2.symm
        · intro active
          simp only [Bool.and_eq_true] at active
          exact Or.inr (verticalGeometry active.1)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
