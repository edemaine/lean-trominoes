/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineExpressionData

/-! # Direction-conditional terminal order-coordinate recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Geometric direction bit of a nondegenerate axis-aligned segment. -/
def GridSegment.increasingAlongAxis (segment : GridSegment) : Bool :=
  if decide segment.IsHorizontal then
    decide (segment.start.1 < segment.finish.1)
  else
    decide (segment.start.2 < segment.finish.2)

/-- Whether an affine segment increases along its selected carrier axis. -/
def Segment.increasingPredicate
    (segment : Segment) (horizontal : Bool) : Predicate :=
  if horizontal then
    less segment.start.horizontal segment.finish.horizontal
  else
    less segment.start.vertical segment.finish.vertical

/-- Local macrocell coordinate of a terminal on a selected directed axis. -/
def terminalLocalOrderOffset
    (endpoint : SegmentEnd) (increasing : Bool) : Int :=
  match endpoint, increasing with
  | .start, true | .finish, false => 11
  | .start, false | .finish, true => 1

/-- Fixed affine terminal expression selected by one direction bit. -/
def Segment.terminalOrderExpressionForDirection
    (segment : Segment) (horizontal : Bool) (translate : Cell)
    (endpoint : SegmentEnd) (increasing : Bool) : Expression :=
  segment.terminalOrderExpression horizontal translate endpoint
    (terminalLocalOrderOffset endpoint increasing)

/-- The decreasing and increasing alternatives in Boolean order. -/
def Segment.terminalOrderExpressionAlternatives
    (segment : Segment) (horizontal : Bool) (translate : Cell)
    (endpoint : SegmentEnd) : List Expression :=
  [segment.terminalOrderExpressionForDirection
      horizontal translate endpoint false,
    segment.terminalOrderExpressionForDirection
      horizontal translate endpoint true]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
