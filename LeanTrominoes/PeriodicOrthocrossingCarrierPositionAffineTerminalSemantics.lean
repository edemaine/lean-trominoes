/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPositionAffineTerminalCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalRecipeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalFieldAlignmentSemantics

/-! # Exact affine terminal position coordinates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- The two finite port coordinates are determined by the carrier axis and
its increasing/decreasing direction. -/
theorem terminalLocalCoordinate_increasingAlongAxis
    (segment : GridSegment) (axisAligned : segment.IsAxisAligned)
    (endpoint : SegmentEnd) (coordinateHorizontal : Bool) :
    terminalLocalCoordinate coordinateHorizontal (decide segment.IsHorizontal)
        endpoint (GridSegment.increasingAlongAxis segment) =
      if coordinateHorizontal then
        (segmentTerminalLocalPosition segment endpoint).1
      else (segmentTerminalLocalPosition segment endpoint).2 := by
  rcases axisAligned with horizontal | vertical
  · have horizontalEq : decide segment.IsHorizontal = true := by simp [horizontal]
    rcases horizontal with ⟨_sameY, differentX⟩
    by_cases increasing : segment.start.1 < segment.finish.1
    · cases coordinateHorizontal <;> cases endpoint <;>
        simp [terminalLocalCoordinate, GridSegment.increasingAlongAxis,
          terminalLocalOrderOffset, segmentTerminalLocalPosition,
          horizontalEq, increasing]
    · have decreasing : segment.finish.1 < segment.start.1 := by omega
      cases coordinateHorizontal <;> cases endpoint <;>
        simp [terminalLocalCoordinate, GridSegment.increasingAlongAxis,
          terminalLocalOrderOffset, segmentTerminalLocalPosition,
          horizontalEq, increasing, decreasing]
  · rcases vertical with ⟨sameX, differentY⟩
    have notHorizontal : ¬segment.IsHorizontal := by
      intro horizontal
      exact horizontal.2 sameX
    have horizontalEq : decide segment.IsHorizontal = false := by simp [notHorizontal]
    by_cases increasing : segment.start.2 < segment.finish.2
    · cases coordinateHorizontal <;> cases endpoint <;>
        simp [terminalLocalCoordinate, GridSegment.increasingAlongAxis,
          terminalLocalOrderOffset, segmentTerminalLocalPosition,
          horizontalEq, sameX, increasing]
    · have decreasing : segment.finish.2 < segment.start.2 := by omega
      cases coordinateHorizontal <;> cases endpoint <;>
        simp [terminalLocalCoordinate, GridSegment.increasingAlongAxis,
          terminalLocalOrderOffset, segmentTerminalLocalPosition,
          horizontalEq, sameX, increasing, decreasing]

/-- Each physical terminal coordinate is the corresponding translated
endpoint coordinate with its finite local port offset. -/
theorem carrierNodeCoordinateAtPeriod_terminal_evalPair
    (segment : Segment) (segmentIndex : Nat) (translate : Cell)
    (endpoint : SegmentEnd) (pair : RouteDescriptor × RouteDescriptor)
    (horizontal : Bool) :
    carrierNodeCoordinateAtPeriod horizontal pair.1.gridSize
        (.terminal ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
          translate, endpoint⟩) =
      planarMacroScale *
        (if horizontal then
          (Cell.add ((segment.endpointPoint endpoint).evalPair pair)
            (Cell.scale (pair.1.gridSize : Int) translate)).1
        else
          (Cell.add ((segment.endpointPoint endpoint).evalPair pair)
            (Cell.scale (pair.1.gridSize : Int) translate)).2) +
        (if horizontal then
          (segmentTerminalLocalPosition (segment.evalPair pair) endpoint).1
        else (segmentTerminalLocalPosition (segment.evalPair pair) endpoint).2) := by
  have startEq : (segment.evalPair pair).start = segment.start.evalPair pair := rfl
  have finishEq : (segment.evalPair pair).finish = segment.finish.evalPair pair := rfl
  cases endpoint <;> cases horizontal <;>
    simp [startEq, finishEq, carrierNodeCoordinateAtPeriod,
      carrierNodePositionAtPeriod, segmentTerminalPositionAtPeriod,
      segmentTerminalDrawingPointAtPeriod, occurrenceSegmentAtPeriod,
      Segment.endpointPoint, GridSegment.translate, Cell.add, Cell.scale, add_comm]

/-- Selecting the actual axis and direction gives either exact physical
terminal coordinate, including whole-period translations. -/
theorem Segment.terminalCoordinateExpression_evalPair
    (segment : Segment) (segmentIndex : Nat) (translate : Cell)
    (endpoint : SegmentEnd) (pair : RouteDescriptor × RouteDescriptor)
    (coordinateHorizontal : Bool)
    (axisAligned : (segment.evalPair pair).IsAxisAligned) :
    (segment.terminalCoordinateExpression coordinateHorizontal
        (decide (segment.evalPair pair).IsHorizontal) translate endpoint
        ((segment.increasingPredicate
          (decide (segment.evalPair pair).IsHorizontal)).evalPair pair)).evalPair pair =
      carrierNodeCoordinateAtPeriod coordinateHorizontal pair.1.gridSize
        (.terminal ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
          translate, endpoint⟩) := by
  unfold Segment.terminalCoordinateExpression
  rw [Segment.terminalOrderExpression_evalPair,
    carrierNodeCoordinateAtPeriod_terminal_evalPair,
    Segment.increasingPredicate_evalPair,
    terminalLocalCoordinate_increasingAlongAxis _ axisAligned]

@[simp] theorem terminalCoordinateFields_descriptorPairTokens
    (horizontal keepPositive : Bool) (pair : RouteDescriptor × RouteDescriptor) :
    terminalCoordinateFields horizontal keepPositive
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair) =
      (terminalCoordinateExpressions horizontal).map fun expression =>
        normalizedExpressionField keepPositive expression pair := by
  have evalEq : ∀ expression : Expression,
      expression.eval (RouteDescriptorPairFieldTags.tokenFieldValue
        (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) =
        expression.evalPair pair := by
    intro expression
    simpa [Expression.evalTokens] using expression.evalTokens_descriptorPairTokens pair
  cases keepPositive <;>
    simp [terminalCoordinateFields, normalizedExpressionField, evalEq]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
