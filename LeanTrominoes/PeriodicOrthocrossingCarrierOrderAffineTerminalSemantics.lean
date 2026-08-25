/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineExpressionData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebraSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSegmentSemantics

/-! # Terminal carrier order-coordinate affine semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

@[simp] theorem carrierNode_isHorizontal_terminal
    (terminal : SegmentTerminal) :
    (CarrierNode.terminal terminal).isHorizontal =
      decide terminal.indexed.segment.IsHorizontal :=
  rfl

@[simp] theorem Point.axisExpression_evalPair
    (horizontal : Bool) (affinePoint : Point)
    (pair : RouteDescriptor × RouteDescriptor) :
    (affinePoint.axisExpression horizontal).evalPair pair =
      if horizontal then (affinePoint.evalPair pair).1
      else (affinePoint.evalPair pair).2 := by
  cases horizontal <;> rfl

@[simp] theorem Point.evalPair_translateByFirstPeriod
    (affinePoint : Point) (translate : Cell)
    (pair : RouteDescriptor × RouteDescriptor) :
    (affinePoint.translateByPeriod
        (gridSize .first) translate).evalPair pair =
      Cell.add (affinePoint.evalPair pair)
        (Cell.scale (pair.1.gridSize : Int) translate) := by
  unfold Point.evalPair
  rw [Point.eval_translateByPeriod]
  have sizeEq :
      Expression.eval (RouteDescriptorPairFieldTags.pairFieldValue pair)
          (gridSize .first) =
        (pair.1.gridSize : Int) :=
    evalPair_gridSize pair .first
  rw [sizeEq]

/-- Evaluation of a terminal order expression is its selected translated
drawing coordinate, scaled to the macrogrid and shifted by the local port. -/
theorem Segment.terminalOrderExpression_evalPair
    (segment : Segment) (horizontal : Bool) (translate : Cell)
    (endpoint : SegmentEnd) (localOffset : Int)
    (pair : RouteDescriptor × RouteDescriptor) :
    (segment.terminalOrderExpression horizontal translate endpoint
        localOffset).evalPair pair =
      planarMacroScale *
          (if horizontal then
            (Cell.add
              ((segment.endpointPoint endpoint).evalPair pair)
              (Cell.scale (pair.1.gridSize : Int) translate)).1
          else
            (Cell.add
              ((segment.endpointPoint endpoint).evalPair pair)
              (Cell.scale (pair.1.gridSize : Int) translate)).2) +
        localOffset := by
  simp [Segment.terminalOrderExpression]

/-- Fold the graph-free terminal coordinate to the same translated endpoint
normal form used by the affine expression. -/
theorem carrierNodeOrderCoordinateAtPeriod_terminal_evalPair
    (segment : Segment) (segmentIndex : Nat) (translate : Cell)
    (endpoint : SegmentEnd) (pair : RouteDescriptor × RouteDescriptor) :
    carrierNodeOrderCoordinateAtPeriod pair.1.gridSize
        (.terminal
          ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
            translate, endpoint⟩) =
      planarMacroScale *
          (if decide (segment.evalPair pair).IsHorizontal then
            (Cell.add
              ((segment.endpointPoint endpoint).evalPair pair)
              (Cell.scale (pair.1.gridSize : Int) translate)).1
          else
            (Cell.add
              ((segment.endpointPoint endpoint).evalPair pair)
              (Cell.scale (pair.1.gridSize : Int) translate)).2) +
        (if decide (segment.evalPair pair).IsHorizontal then
          (segmentTerminalLocalPosition
            (segment.evalPair pair) endpoint).1
        else
          (segmentTerminalLocalPosition
            (segment.evalPair pair) endpoint).2) := by
  have startEq :
      (segment.evalPair pair).start = segment.start.evalPair pair :=
    rfl
  have finishEq :
      (segment.evalPair pair).finish = segment.finish.evalPair pair :=
    rfl
  cases endpoint <;>
    by_cases horizontalSegment : (segment.evalPair pair).IsHorizontal <;>
      simp [horizontalSegment, startEq, finishEq,
        carrierNodeOrderCoordinateAtPeriod,
        carrierNodePositionAtPeriod, segmentTerminalPositionAtPeriod,
        segmentTerminalDrawingPointAtPeriod, occurrenceSegmentAtPeriod,
        Segment.endpointPoint, GridSegment.translate, Cell.add,
        Cell.scale] <;>
      ring_nf <;>
      simp

/-- Supplying the finite axis/direction choice makes the affine terminal
expression the exact carrier order coordinate. -/
theorem Segment.terminalOrderExpression_evalPair_eq_carrierNodeOrderCoordinate
    (segment : Segment) (segmentIndex : Nat) (horizontal : Bool)
    (translate : Cell) (endpoint : SegmentEnd) (localOffset : Int)
    (pair : RouteDescriptor × RouteDescriptor)
    (horizontalEq :
      horizontal = decide (segment.evalPair pair).IsHorizontal)
    (localOffsetEq :
      localOffset =
        if horizontal then
          (segmentTerminalLocalPosition
            (segment.evalPair pair) endpoint).1
        else
          (segmentTerminalLocalPosition
            (segment.evalPair pair) endpoint).2) :
    (segment.terminalOrderExpression horizontal translate endpoint
        localOffset).evalPair pair =
      carrierNodeOrderCoordinateAtPeriod pair.1.gridSize
        (.terminal
          ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
            translate, endpoint⟩) := by
  rw [segment.terminalOrderExpression_evalPair]
  rw [carrierNodeOrderCoordinateAtPeriod_terminal_evalPair]
  rw [localOffsetEq, horizontalEq]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
