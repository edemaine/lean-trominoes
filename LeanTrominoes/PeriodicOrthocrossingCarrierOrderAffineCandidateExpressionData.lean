/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalRecipeData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler

/-! # Affine order-coordinate expressions aligned with carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Offset-one affine terminal expressions for every neighboring translation
and both segment endpoints. -/
def Segment.terminalOrderBaseExpressionBlock
    (segment : Segment) (horizontal : Bool) : List Expression :=
  neighborTranslations.flatMap fun translate =>
    [segment.terminalOrderExpression horizontal translate .start 1,
      segment.terminalOrderExpression horizontal translate .finish 1]

/-- A terminal receives the remaining ten local units precisely at a start
of an increasing segment or a finish of a decreasing segment. -/
def Segment.terminalOrderAdjustmentPredicateBlock
    (segment : Segment) (horizontal : Bool) : List Predicate :=
  let increasing := segment.increasingPredicate horizontal
  neighborTranslations.flatMap fun _ =>
    [increasing, .negation increasing]

/-- Horizontal and vertical expression blocks aligned with the two carrier
classification copies of one segment. -/
def Segment.terminalOrderBaseExpressionBlocks
    (segment : Segment) : List (List Expression) :=
  [segment.terminalOrderBaseExpressionBlock true,
    segment.terminalOrderBaseExpressionBlock false]

/-- Horizontal and vertical adjustment blocks aligned with the two carrier
classification copies of one segment. -/
def Segment.terminalOrderAdjustmentPredicateBlocks
    (segment : Segment) : List (List Predicate) :=
  [segment.terminalOrderAdjustmentPredicateBlock true,
    segment.terminalOrderAdjustmentPredicateBlock false]

/-- Terminal expression blocks aligned with one route shape's carrier-node
candidate blocks. -/
def RouteShape.terminalOrderBaseExpressionBlocks
    (shape : RouteShape) : List (List Expression) :=
  (shape.segments .first).flatMap
    Segment.terminalOrderBaseExpressionBlocks

/-- Terminal adjustment blocks aligned with one route shape's carrier-node
candidate blocks. -/
def RouteShape.terminalOrderAdjustmentPredicateBlocks
    (shape : RouteShape) : List (List Predicate) :=
  (shape.segments .first).flatMap
    Segment.terminalOrderAdjustmentPredicateBlocks

/-- Complete fixed terminal expression family in padded-candidate order. -/
def terminalOrderBaseExpressionBlocks : List (List Expression) :=
  allRouteShapes.flatMap RouteShape.terminalOrderBaseExpressionBlocks

/-- Complete fixed terminal adjustment family in padded-candidate order. -/
def terminalOrderAdjustmentPredicateBlocks : List (List Predicate) :=
  allRouteShapes.flatMap
    RouteShape.terminalOrderAdjustmentPredicateBlocks

def terminalOrderBaseExpressions : List Expression :=
  terminalOrderBaseExpressionBlocks.flatten

def terminalOrderAdjustmentPredicates : List Predicate :=
  terminalOrderAdjustmentPredicateBlocks.flatten

/-- Four affine crossing-boundary coordinates for one retention shift. -/
def occurrencePairCrossingOrderExpressionShiftBlock
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    List Expression :=
  [occurrencePairCrossingOrderExpression occurrences shift .left,
    occurrencePairCrossingOrderExpression occurrences shift .right,
    occurrencePairCrossingOrderExpression occurrences shift .top,
    occurrencePairCrossingOrderExpression occurrences shift .bottom]

/-- All retained crossing-boundary coordinates for one occurrence pair. -/
def occurrencePairCrossingOrderExpressionBlock
    (occurrences : Occurrence × Occurrence) : List Expression :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingOrderExpressionShiftBlock occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

/-- Crossing expression blocks aligned with the fixed occurrence slots. -/
def crossingOrderExpressionBlocks : List (List RouteDescriptorPairAffine.Expression) :=
  crossingSlots.map fun slot =>
    RouteDescriptorPairAffine.occurrencePairCrossingOrderExpressionBlock
      slot.occurrences

def crossingOrderExpressions : List RouteDescriptorPairAffine.Expression :=
  crossingOrderExpressionBlocks.flatten

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
