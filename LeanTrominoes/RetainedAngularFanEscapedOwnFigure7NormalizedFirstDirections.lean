/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanEscapedCardinalClassification
import LeanTrominoes.RetainedAngularFanOuterEscapedFigure7NormalizedFirstDirections

/-! # Normalized first directions of complete escaped source splices -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree

private theorem classified_cardinal_of_length_eq_two
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLengthEq : route.length = 2)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route) :
    ∃ port length,
      terminal = (.compass port, length) ∧
        (port = .north ∨ port = .east ∨
          port = .south ∨ port = .west) ∧
        0 < length := by
  cases route with
  | nil => simp at routeLengthEq
  | cons first tail =>
      cases tail with
      | nil => simp at routeLengthEq
      | cons second rest =>
          have restLength : rest.length = 0 := by
            simp only [List.length_cons] at routeLengthEq
            omega
          have restEmpty : rest = [] :=
            List.length_eq_zero_iff.mp restLength
          subst rest
          exact
            retainedTerminalDirectionClassify_pair_axisAligned_cardinal
              first second terminal classified
              (List.isChain_cons_cons.mp routeOrthogonal).1

/-- Normalizing a complete singleton escaped source splice, including its
matching Figure 7 spoke, preserves the original source-edge direction. -/
theorem
    retainedAngularFanEscapedSplicedOwnFigure7Route_normalized_firstDirection
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (finalPoint : Cell)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (singletonPrefix : route.dropLast.length = 1)
    (terminalLengthLarge : 2 ≤ terminal.2) :
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedAngularFanEscapedSplicedOwnFigure7Route
            route terminal slot finalPoint)) =
      AxisDirection.polylineFirstDirection route := by
  have routeLengthEq : route.length = 2 := by
    rw [List.length_dropLast] at singletonPrefix
    omega
  rcases
      classified_cardinal_of_length_eq_two
        route terminal routeLengthEq classified routeOrthogonal with
    ⟨port, length, terminalEq, cardinal, lengthPositive⟩
  have lengthLarge : 2 ≤ length := by
    simpa [terminalEq] using terminalLengthLarge
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let outer :=
    retainedTerminalFanOuterEscapedCompleteRoute center terminal slot
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have boundaryPolylineEq :
      retainedAngularFanEscapedSplicedBoundaryPolyline
          route terminal slot =
        outer := by
    have boundary :=
      retainedAngularFanEscapedSplicedBoundaryPolyline_eq_outerCompleteRoute_of_singletonPrefix
        route terminal slot routeLength classified singletonPrefix
    rw [routeLastD] at boundary
    simpa [center, outer] using boundary
  have terminalPositive : 0 < terminal.2 := by
    simpa [terminalEq] using lengthPositive
  have outerOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline outer := by
    simpa [outer] using
      retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
        center terminal slot terminalPositive escapeFits
  have boundaryRouteEq :
      retainedAngularFanEscapedSplicedBoundaryRoute
          route terminal slot =
        outer := by
    unfold retainedAngularFanEscapedSplicedBoundaryRoute
    rw [boundaryPolylineEq,
      rasterizeRetainedPolyline_eq_of_orthogonal outerOrthogonal]
  unfold retainedAngularFanEscapedSplicedOwnFigure7Route
  rw [boundaryRouteEq]
  calc
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint outer
            (retainedTerminalFanFigure7SpokeRouteAt center slot))) =
      AxisDirection.polylineFirstDirection outer := by
        simpa [outer, terminalEq] using
          retainedTerminalFanOuterEscapedCompleteFigure7Route_normalized_firstDirection
            center port length slot cardinal lengthLarge
    _ = AxisDirection.polylineFirstDirection route := by
      rw [← boundaryRouteEq]
      exact
        retainedAngularFanEscapedSplicedBoundaryRoute_firstDirection
          route terminal slot routeLength classified routeOrthogonal
          escapeFits singletonPrefix

end PeriodicEightOccurrenceSplit
end LeanTrominoes
