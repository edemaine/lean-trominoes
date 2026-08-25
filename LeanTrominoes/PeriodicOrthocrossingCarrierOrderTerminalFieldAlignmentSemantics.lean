/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateSemantics

/-! # Terminal order fields aligned with active semantic nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairFieldTags

/-- Positive or negative normalization of one evaluated affine expression. -/
def normalizedExpressionField (keepPositive : Bool)
    (expression : Expression) (pair : RouteDescriptor × RouteDescriptor) :
    Nat :=
  if keepPositive then (expression.evalPair pair).toNat
  else (-expression.evalPair pair).toNat

@[simp] theorem terminalDirectionalOrderFields_descriptorPairTokens
    (keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    terminalDirectionalOrderFields keepPositive
        (descriptorPairTokens pair) =
      terminalDirectionalOrderExpressions.map fun expression =>
        normalizedExpressionField keepPositive expression pair := by
  have evalEq : ∀ expression : Expression,
      expression.eval (tokenFieldValue (descriptorPairTokens pair)) =
        expression.evalPair pair := by
    intro expression
    simpa [Expression.evalTokens] using
      expression.evalTokens_descriptorPairTokens pair
  cases keepPositive <;>
    simp [terminalDirectionalOrderFields, normalizedExpressionField,
      evalEq]

/-- One fixed axis/direction expression block is aligned with its duplicated
terminal-node templates whenever activation certifies that choice. -/
theorem Segment.terminalDirectionalOrderExpressionBlock_forall₂
    (segment : Segment) (segmentIndex : Nat)
    (horizontal increasing active keepPositive : Bool)
    (pair : RouteDescriptor × RouteDescriptor)
    (horizontalEq : active = true →
      horizontal = decide (segment.evalPair pair).IsHorizontal)
    (increasingEq : active = true →
      increasing =
        (segment.increasingPredicate horizontal).evalPair pair)
    (axisAligned : active = true →
      (segment.evalPair pair).IsAxisAligned) :
    List.Forall₂
      (fun candidate value => ∀ node,
        candidate.value = some node →
          value = carrierNodeOrderFieldAtPeriod
            keepPositive pair.1.gridSize node)
      ((segment.terminalCarrierNodeTemplateBlock pair segmentIndex).map
        (Template.activate active))
      ((segment.terminalDirectionalOrderExpressionBlock
          horizontal increasing).map fun expression =>
        normalizedExpressionField keepPositive expression pair) := by
  unfold Segment.terminalCarrierNodeTemplateBlock
    Segment.terminalDirectionalOrderExpressionBlock
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
                segment.terminalOrderExpressionForDirection_evalPair
                  segmentIndex translate .start pair axisAligned'
              rw [← horizontalEq', ← increasingEq'] at coordinateEq
              cases keepPositive <;>
                simp [normalizedExpressionField,
                  carrierNodeOrderFieldAtPeriod, coordinateEq]
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
                  segment.terminalOrderExpressionForDirection_evalPair
                    segmentIndex translate .finish pair axisAligned'
                rw [← horizontalEq', ← increasingEq'] at coordinateEq
                cases keepPositive <;>
                  simp [normalizedExpressionField,
                    carrierNodeOrderFieldAtPeriod, coordinateEq]
          · exact List.Forall₂.nil
      · exact induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
