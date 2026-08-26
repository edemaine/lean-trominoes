/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanEscapedFirstDirections
import LeanTrominoes.RetainedAngularFanOuterEscapedHeadIsolation

/-! # Normalized first directions of escaped outer routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

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

/-- Loop erasure preserves the clause-side direction of every cardinal
escaped outer fan whose source terminal has length at least two. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_normalized_firstDirection
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
          (retainedTerminalFanOuterEscapedCompleteRoute
            center (.compass port, length) slot)) =
      AxisDirection.polylineFirstDirection
        (retainedTerminalFanOuterEscapedCompleteRoute
          center (.compass port, length) slot) := by
  let terminal : RetainedTerminalData := (.compass port, length)
  let route :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
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
  have orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route :=
    retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
      center terminal slot lengthPositive escapeFits
  have firstGenuine :
      (AxisDirection.polylineFirstDirection route).IsGenuine := by
    rw [retainedTerminalFanOuterEscapedCompleteRoute_firstDirection]
    apply RetainedRay.rasterize_firstDirection_isGenuine
    simp [terminal, retainedTerminalFanOuterSourceEscapeRay,
      retainedTerminalFanOuterInwardRayOfLength,
      retainedTerminalFanOuterSourceEscapeLength]
  have routeLength : 2 ≤ route.length :=
    two_le_length_of_firstDirection_isGenuine firstGenuine
  apply
    AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
  · exact
      AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
        routeLength orthogonal
  · exact orthogonal
  · simpa [route, terminal] using
      retainedTerminalFanOuterEscapedCompleteRoute_headNotInTail
        center port length slot cardinal lengthLarge

end PeriodicEightOccurrenceSplit
end LeanTrominoes
