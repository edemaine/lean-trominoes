/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalRecipeData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateSemantics

/-! # Direction-conditional terminal order-coordinate semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- The increasing/decreasing bit selects exactly the local terminal port on
every nondegenerate axis-aligned segment. -/
theorem terminalLocalOrderOffset_increasingAlongAxis
    (segment : GridSegment) (axisAligned : segment.IsAxisAligned)
    (endpoint : SegmentEnd) :
    terminalLocalOrderOffset endpoint
        (GridSegment.increasingAlongAxis segment) =
      if decide segment.IsHorizontal then
        (segmentTerminalLocalPosition segment endpoint).1
      else
        (segmentTerminalLocalPosition segment endpoint).2 := by
  rcases axisAligned with horizontal | vertical
  · have horizontalEq : decide segment.IsHorizontal = true := by
      simp [horizontal]
    rcases horizontal with ⟨_sameY, differentX⟩
    by_cases increasing : segment.start.1 < segment.finish.1
    · cases endpoint <;>
        simp [GridSegment.increasingAlongAxis, terminalLocalOrderOffset,
          segmentTerminalLocalPosition, horizontalEq, increasing]
    · have decreasing : segment.finish.1 < segment.start.1 := by
        omega
      cases endpoint <;>
        simp [GridSegment.increasingAlongAxis, terminalLocalOrderOffset,
          segmentTerminalLocalPosition, horizontalEq, increasing, decreasing]
  · rcases vertical with ⟨sameX, differentY⟩
    have notHorizontal : ¬segment.IsHorizontal := by
      intro horizontal
      exact horizontal.2 sameX
    have horizontalEq : decide segment.IsHorizontal = false := by
      simp [notHorizontal]
    by_cases increasing : segment.start.2 < segment.finish.2
    · cases endpoint <;>
        simp [GridSegment.increasingAlongAxis, terminalLocalOrderOffset,
          segmentTerminalLocalPosition, horizontalEq, sameX, increasing]
    · have decreasing : segment.finish.2 < segment.start.2 := by
        omega
      cases endpoint <;>
        simp [GridSegment.increasingAlongAxis, terminalLocalOrderOffset,
          segmentTerminalLocalPosition, horizontalEq, sameX, increasing,
          decreasing]

/-- The affine direction predicate is the geometric increasing-axis bit. -/
@[simp] theorem Segment.increasingPredicate_evalPair
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor) :
    (segment.increasingPredicate
        (decide (segment.evalPair pair).IsHorizontal)).evalPair pair =
      GridSegment.increasingAlongAxis (segment.evalPair pair) := by
  by_cases horizontal : (segment.evalPair pair).IsHorizontal
  · have horizontalEq :
        decide (segment.evalPair pair).IsHorizontal = true := by
      simp [horizontal]
    rw [horizontalEq]
    simp only [Segment.increasingPredicate, if_true, evalPair_less,
      GridSegment.increasingAlongAxis]
    rw [horizontalEq]
    rfl
  · have horizontalEq :
        decide (segment.evalPair pair).IsHorizontal = false := by
      simp [horizontal]
    rw [horizontalEq]
    simp only [Segment.increasingPredicate, GridSegment.increasingAlongAxis]
    rw [horizontalEq]
    rfl

/-- Selecting the affine alternative by its compiled direction predicate
recovers the exact terminal order coordinate. -/
theorem Segment.terminalOrderExpressionForDirection_evalPair
    (segment : Segment) (segmentIndex : Nat) (translate : Cell)
    (endpoint : SegmentEnd) (pair : RouteDescriptor × RouteDescriptor)
    (axisAligned : (segment.evalPair pair).IsAxisAligned) :
    (segment.terminalOrderExpressionForDirection
        (decide (segment.evalPair pair).IsHorizontal) translate endpoint
        ((segment.increasingPredicate
          (decide (segment.evalPair pair).IsHorizontal)).evalPair pair)).evalPair
          pair =
      carrierNodeOrderCoordinateAtPeriod pair.1.gridSize
        (.terminal
          ⟨⟨pair.1.edgeIndex, segmentIndex, segment.evalPair pair⟩,
            translate, endpoint⟩) := by
  apply segment.terminalOrderExpression_evalPair_eq_carrierNodeOrderCoordinate
  · rfl
  · rw [segment.increasingPredicate_evalPair]
    exact terminalLocalOrderOffset_increasingAlongAxis
      (segment.evalPair pair) axisAligned endpoint

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
