/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalTerminalCoordinateCompiler

/-! # Canonical terminal-coordinate blocks aligned with candidate nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

/-- One fixed axis/direction expression block is aligned with its duplicated
terminal-node templates whenever activation certifies that choice. -/
theorem GaugedSegment.canonicalTerminalCoordinateExpressionBlock_forall₂
    (gauged : GaugedSegment) (segmentIndex : Nat)
    (coordinateHorizontal horizontal increasing active keepPositive : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (correct : gauged.HasPeriodGauges pair)
    (horizontalEq : active = true →
      horizontal = decide (gauged.segment.evalPair pair).IsHorizontal)
    (increasingEq : active = true →
      increasing =
        (gauged.segment.increasingPredicate horizontal).evalPair pair)
    (axisAligned : active = true →
      (gauged.segment.evalPair pair).IsAxisAligned) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeCanonicalCoordinateFieldAtPeriod
            coordinateHorizontal keepPositive pair.1.gridSize node)
      ((gauged.segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.activate active))
      ((gauged.canonicalTerminalCoordinateExpressionBlock
          coordinateHorizontal horizontal increasing).map fun expression =>
        normalizedExpressionField keepPositive expression pair) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
    GaugedSegment.canonicalTerminalCoordinateExpressionBlock
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
              have horizontalEq' := horizontalEq rfl
              have increasingEq' := increasingEq rfl
              have axisAligned' := axisAligned rfl
              simp only [Template.activate, Bool.true_and, if_true,
                Option.some.injEq] at valueEq
              subst node
              have coordinateEq :=
                gauged.canonicalTerminalCoordinateExpression_evalPair
                  segmentIndex translate .start pair coordinateHorizontal axisAligned' correct
              rw [← horizontalEq', ← increasingEq'] at coordinateEq
              cases keepPositive <;>
                simp [normalizedExpressionField,
                  carrierNodeCanonicalCoordinateFieldAtPeriod, coordinateEq]
        · apply List.Forall₂.cons
          · intro node valueEq
            cases active with
            | false => simp [Template.activate] at valueEq
            | true =>
                have horizontalEq' := horizontalEq rfl
                have increasingEq' := increasingEq rfl
                have axisAligned' := axisAligned rfl
                simp only [Template.activate, Bool.true_and, if_true,
                  Option.some.injEq] at valueEq
                subst node
                have coordinateEq :=
                  gauged.canonicalTerminalCoordinateExpression_evalPair
                    segmentIndex translate .finish pair coordinateHorizontal axisAligned' correct
                rw [← horizontalEq', ← increasingEq'] at coordinateEq
                cases keepPositive <;>
                  simp [normalizedExpressionField,
                    carrierNodeCanonicalCoordinateFieldAtPeriod, coordinateEq]
          · exact List.Forall₂.nil
      · exact induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
