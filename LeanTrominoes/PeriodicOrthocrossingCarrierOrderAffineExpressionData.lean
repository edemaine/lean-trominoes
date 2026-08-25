/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarWires
import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplates

/-! # Affine expressions for physical carrier order coordinates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Select one affine coordinate by carrier axis. -/
def Point.axisExpression (horizontal : Bool) (affinePoint : Point) :
    Expression :=
  if horizontal then affinePoint.horizontal else affinePoint.vertical

/-- Select one endpoint of an affine segment. -/
def Segment.endpointPoint (segment : Segment) : SegmentEnd → Point
  | .start => segment.start
  | .finish => segment.finish

/-- Physical order coordinate of a translated terminal once its axis and
fixed local port offset have been selected. -/
def Segment.terminalOrderExpression
    (segment : Segment) (horizontal : Bool) (translate : Cell)
    (endpoint : SegmentEnd) (localOffset : Int) : Expression :=
  let translated :=
    (segment.endpointPoint endpoint).translateByPeriod
      (gridSize .first) translate
  (translated.axisExpression horizontal).scale planarMacroScale
    |>.addConstant localOffset

/-- Affine intersection point of a fixed oriented occurrence pair after one
retention shift.  Crossing guards ensure the first occurrence is horizontal
and the second is vertical. -/
def occurrencePairCrossingPointAtShift
    (occurrences : Occurrence × Occurrence) (shift : Cell) : Point :=
  let first := occurrences.1.segmentAtFirstPeriod
  let second := occurrences.2.segmentAtFirstPeriod
  (point second.start.horizontal first.start.vertical).translateByPeriod
    (gridSize .first) shift

/-- Fixed local order-axis coordinate of a Figure 8(b) boundary port. -/
def CrossingSide.localOrderOffset : CrossingSide → Int
  | .left | .top => 1
  | .right | .bottom => 11

/-- Physical order coordinate of one retained crossing-boundary template. -/
def occurrencePairCrossingOrderExpression
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (side : CrossingSide) : Expression :=
  let crossingPoint :=
    occurrencePairCrossingPointAtShift occurrences shift
  let coordinate := match side with
    | .left | .right => crossingPoint.horizontal
    | .top | .bottom => crossingPoint.vertical
  coordinate.scale planarMacroScale
    |>.addConstant (CrossingSide.localOrderOffset side)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
