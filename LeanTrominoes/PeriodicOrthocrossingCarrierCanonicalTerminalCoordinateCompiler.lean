/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionAffineTerminalSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalPrototypeGaugeSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionSemantics

/-! # Canonical terminal coordinates from finite endpoint gauges -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing

/-- Canonical physical representative at the refined drawing period. -/
def carrierNodeCanonicalPositionAtPeriod (period : Nat) (node : CarrierNode) : Cell :=
  let position := carrierNodePositionAtPeriod period node
  (position.1 % carrierMacroPeriodAtPeriod period, position.2 % carrierMacroPeriodAtPeriod period)

def carrierNodeCanonicalCoordinateAtPeriod (horizontal : Bool) (period : Nat) (node : CarrierNode) : Int :=
  let position := carrierNodeCanonicalPositionAtPeriod period node
  if horizontal then position.1 else position.2

def carrierNodeCanonicalCoordinateFieldAtPeriod (horizontal keepPositive : Bool)
    (period : Nat) (node : CarrierNode) : Nat :=
  let coordinate := carrierNodeCanonicalCoordinateAtPeriod horizontal period node
  if keepPositive then coordinate.toNat else (-coordinate).toNat

theorem segmentTerminalPositionAtPeriod_translate (period : Nat) (indexed : IndexedGridSegment)
    (translate : Cell) (endpoint : SegmentEnd) :
    segmentTerminalPositionAtPeriod period ⟨indexed, translate, endpoint⟩ =
      Cell.add (segmentTerminalPositionAtPeriod period ⟨indexed, (0, 0), endpoint⟩)
        (Cell.scale (carrierMacroPeriodAtPeriod period) translate) := by
  cases endpoint <;> apply Prod.ext <;>
    simp [segmentTerminalPositionAtPeriod, segmentTerminalDrawingPointAtPeriod,
      occurrenceSegmentAtPeriod, GridSegment.translate, Cell.add, Cell.scale,
      carrierMacroPeriodAtPeriod] <;> ring

private theorem coordinate_wrap_eq_shift (point period translate gauge : Int)
    (gaugeEq : point / period = gauge) :
    (point + period * translate) % period = point + period * (-gauge) := by
  rw [Int.add_mul_emod_self_left, mul_neg]
  have decomposition := Int.emod_add_mul_ediv point period
  rw [gaugeEq] at decomposition
  omega

/-- Subtracting the exact prototype gauge also removes every retained period translate. -/
theorem carrierNodeCanonicalPositionAtPeriod_terminal_eq_negativeGauge
    (period : Nat) (indexed : IndexedGridSegment) (translate : Cell) (endpoint : SegmentEnd)
    (gauge : Cell)
    (gaugeEq : carrierPositionGaugeAtPeriod period
      (segmentTerminalPositionAtPeriod period ⟨indexed, (0, 0), endpoint⟩) = gauge) :
    carrierNodeCanonicalPositionAtPeriod period (.terminal ⟨indexed, translate, endpoint⟩) =
      segmentTerminalPositionAtPeriod period ⟨indexed, (-gauge.1, -gauge.2), endpoint⟩ := by
  dsimp only [carrierNodeCanonicalPositionAtPeriod, carrierNodePositionAtPeriod]
  rw [segmentTerminalPositionAtPeriod_translate period indexed translate endpoint,
    segmentTerminalPositionAtPeriod_translate period indexed (-gauge.1, -gauge.2) endpoint]
  apply Prod.ext
  · exact coordinate_wrap_eq_shift _ _ _ _ (congrArg Prod.fst gaugeEq)
  · exact coordinate_wrap_eq_shift _ _ _ _ (congrArg Prod.snd gaugeEq)

namespace RouteDescriptorPairAffine
open Computability Turing

def GaugedSegment.endpointGauge (gauged : GaugedSegment) : SegmentEnd → Cell
  | .start => gauged.startGauge
  | .finish => gauged.finishGauge

/-- The candidate's retention translate is removed by canonical wrapping. -/
def GaugedSegment.canonicalTerminalCoordinateExpression (gauged : GaugedSegment)
    (coordinateHorizontal horizontal : Bool) (endpoint : SegmentEnd) (increasing : Bool) : Expression :=
  let gauge := gauged.endpointGauge endpoint
  gauged.segment.terminalCoordinateExpression coordinateHorizontal horizontal
    (-gauge.1, -gauge.2) endpoint increasing

def GaugedSegment.canonicalTerminalCoordinateExpressionBlock (gauged : GaugedSegment)
    (coordinateHorizontal horizontal increasing : Bool) : List Expression :=
  neighborTranslations.flatMap fun _ =>
    [gauged.canonicalTerminalCoordinateExpression coordinateHorizontal horizontal .start increasing,
      gauged.canonicalTerminalCoordinateExpression coordinateHorizontal horizontal .finish increasing]

def GaugedSegment.canonicalTerminalCoordinateExpressionBlocks (gauged : GaugedSegment)
    (coordinateHorizontal : Bool) : List (List Expression) :=
  [gauged.canonicalTerminalCoordinateExpressionBlock coordinateHorizontal true false,
    gauged.canonicalTerminalCoordinateExpressionBlock coordinateHorizontal true true,
    gauged.canonicalTerminalCoordinateExpressionBlock coordinateHorizontal false false,
    gauged.canonicalTerminalCoordinateExpressionBlock coordinateHorizontal false true]

def RouteShape.canonicalTerminalCoordinateExpressionBlocks (shape : RouteShape)
    (coordinateHorizontal : Bool) : List (List Expression) :=
  (shape.gaugedSegments .first).flatMap fun gauged =>
    gauged.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal

def canonicalTerminalCoordinateExpressions (coordinateHorizontal : Bool) : List Expression :=
  (allRouteShapes.flatMap fun shape => shape.canonicalTerminalCoordinateExpressionBlocks coordinateHorizontal).flatten

def canonicalTerminalCoordinateFields (horizontal keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields keepPositive (canonicalTerminalCoordinateExpressions horizontal) tokens

noncomputable def canonicalTerminalCoordinateFieldsComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (canonicalTerminalCoordinateFields horizontal keepPositive) :=
  normalizedFieldsComputableInPolyTime keepPositive (canonicalTerminalCoordinateExpressions horizontal)

/-- Finite gauge subtraction gives the exact canonically wrapped terminal coordinate. -/
theorem GaugedSegment.canonicalTerminalCoordinateExpression_evalPair
    (gauged : GaugedSegment) (segmentIndex : Nat) (translate : Cell) (endpoint : SegmentEnd)
    (pair : RouteDescriptor × RouteDescriptor) (coordinateHorizontal : Bool)
    (axisAligned : (gauged.segment.evalPair pair).IsAxisAligned)
    (correct : gauged.HasPeriodGauges pair) :
    (gauged.canonicalTerminalCoordinateExpression coordinateHorizontal
      (decide (gauged.segment.evalPair pair).IsHorizontal) endpoint
      ((gauged.segment.increasingPredicate (decide (gauged.segment.evalPair pair).IsHorizontal)).evalPair pair)).evalPair pair =
      carrierNodeCanonicalCoordinateAtPeriod coordinateHorizontal pair.1.gridSize
        (.terminal ⟨⟨pair.1.edgeIndex, segmentIndex, gauged.segment.evalPair pair⟩, translate, endpoint⟩) := by
  unfold GaugedSegment.canonicalTerminalCoordinateExpression
  rw [Segment.terminalCoordinateExpression_evalPair _ _ _ _ _ _ axisAligned]
  have gaugeEq := gauged.terminalPrototypeGauge_eq pair correct segmentIndex endpoint
  change carrierPositionGaugeAtPeriod pair.1.gridSize _ = gauged.endpointGauge endpoint at gaugeEq
  unfold carrierNodeCanonicalCoordinateAtPeriod
  rw [carrierNodeCanonicalPositionAtPeriod_terminal_eq_negativeGauge _ _ _ _ _ gaugeEq]
  rfl

@[simp] theorem canonicalTerminalCoordinateFields_descriptorPairTokens
    (horizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    canonicalTerminalCoordinateFields horizontal keepPositive (RouteDescriptorPairFieldTags.descriptorPairTokens pair) =
      (canonicalTerminalCoordinateExpressions horizontal).map fun expression =>
        normalizedExpressionField keepPositive expression pair := by
  have evalEq : ∀ expression : Expression,
      expression.eval (RouteDescriptorPairFieldTags.tokenFieldValue
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) = expression.evalPair pair := by
    intro expression
    simpa [Expression.evalTokens] using expression.evalTokens_descriptorPairTokens pair
  cases keepPositive <;> simp [canonicalTerminalCoordinateFields, normalizedExpressionField, evalEq]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
end
