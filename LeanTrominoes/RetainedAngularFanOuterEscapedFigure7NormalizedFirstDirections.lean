/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterEscapedFigure7HeadIsolation

/-! # Normalized first directions after appending a Figure 7 spoke -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

private theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection first).IsGenuine) :
    AxisDirection.polylineFirstDirection
        (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first tail =>
      cases tail with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => rfl

private theorem two_le_length_of_firstDirection_isGenuine
    {points : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection points).IsGenuine) :
    2 ≤ points.length := by
  cases points with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first tail =>
      cases tail with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => simp

/-- Loop erasure preserves the clause-side direction after the matching
Figure 7 spoke is appended to a cardinal escaped outer fan. -/
theorem
    retainedTerminalFanOuterEscapedCompleteFigure7Route_normalized_firstDirection
    (center : Cell)
    (port : Port)
    (length : Nat)
    (slot : RetainedTerminalSlot)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west)
    (lengthLarge : 2 ≤ length) :
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint
            (retainedTerminalFanOuterEscapedCompleteRoute
              center (.compass port, length) slot)
            (retainedTerminalFanFigure7SpokeRouteAt center slot))) =
      AxisDirection.polylineFirstDirection
        (retainedTerminalFanOuterEscapedCompleteRoute
          center (.compass port, length) slot) := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let outer :=
    retainedTerminalFanOuterEscapedCompleteRoute center terminal slot
  let spoke := retainedTerminalFanFigure7SpokeRouteAt center slot
  let route := joinAtEndpoint outer spoke
  have lengthPositive : 0 < length := by omega
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simp [terminal, retainedTerminalFanOuterSourceEscapeLength,
      retainedTerminalFanOuterRadialLength,
      retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedTerminalFanRoutingRefinement,
      retainedTerminalInterfaceMultiplier]
    omega
  have outerOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline outer :=
    retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
      center terminal slot lengthPositive escapeFits
  have spokeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline spoke :=
    retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  have outerLast :=
    retainedTerminalFanOuterEscapedCompleteRoute_getLast?
      center terminal slot lengthPositive escapeFits
  have spokeHead :=
    retainedTerminalFanFigure7SpokeRouteAt_head? center slot
  have routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route :=
    outerOrthogonal.joinAtEndpoint
      spokeOrthogonal outerLast spokeHead
  have outerGenuine :
      (AxisDirection.polylineFirstDirection outer).IsGenuine := by
    rw [retainedTerminalFanOuterEscapedCompleteRoute_firstDirection]
    apply RetainedRay.rasterize_firstDirection_isGenuine
    simp [terminal, retainedTerminalFanOuterSourceEscapeRay,
      retainedTerminalFanOuterInwardRayOfLength,
      retainedTerminalFanOuterSourceEscapeLength]
  have routeDirection :
      AxisDirection.polylineFirstDirection route =
        AxisDirection.polylineFirstDirection outer :=
    polylineFirstDirection_joinAtEndpoint_of_genuine outerGenuine
  have routeGenuine :
      (AxisDirection.polylineFirstDirection route).IsGenuine := by
    rw [routeDirection]
    exact outerGenuine
  have routeLength : 2 ≤ route.length :=
    two_le_length_of_firstDirection_isGenuine routeGenuine
  calc
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline route) =
      AxisDirection.polylineFirstDirection route :=
        AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
          (AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
            routeLength routeOrthogonal)
          routeOrthogonal
          (by
            simpa [route, outer, spoke, terminal] using
              retainedTerminalFanOuterEscapedCompleteFigure7Route_headNotInTail
                center port length slot cardinal lengthLarge)
    _ = AxisDirection.polylineFirstDirection outer := routeDirection

end PeriodicEightOccurrenceSplit
end LeanTrominoes
