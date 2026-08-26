/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalSourceHeadSeparationSupport
import LeanTrominoes.RetainedAngularFanFallbackEndpointIsolation
import LeanTrominoes.RetainedAngularFanSourceSpliceBounds

/-! # Source-head separation from a final outer fan and spoke -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 500000

/-- If a source point is separated from a route's final-segment rectangle,
then sufficient combined refinement keeps its scaled copy out of both the
unit-subdivided complete outer fan and matching Figure 7 spoke. -/
theorem
    retainedTerminalFanOuterAndSpoke_sourceHead_not_mem_of_separated
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      288 < retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (sourcePoint : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (separated :
      ClosedGridRectanglesSeparated
        sourcePoint sourcePoint
        (GridSegment.mk
          (polylineLastEntrance route)
          (route.getLastD (0, 0))).coordinateLower
        (GridSegment.mk
          (polylineLastEntrance route)
          (route.getLastD (0, 0))).coordinateUpper) :
    let combinedFactor :=
      retainedTerminalFanTotalRefinement * factor
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor route).getLastD (0, 0))
    let scaledTerminal :=
      scaleRetainedTerminalData factor terminal
    let sourceHead := Cell.scale combinedFactor sourcePoint
    sourceHead ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanOuterCompleteRoute
            center scaledTerminal slot) ∧
      sourceHead ∉
        AxisDirection.unitSubdividePolyline
          (retainedTerminalFanFigure7SpokeRouteAt center slot) := by
  dsimp only
  let combinedFactor :=
    retainedTerminalFanTotalRefinement * factor
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline factor route).getLastD (0, 0))
  let scaledTerminal :=
    scaleRetainedTerminalData factor terminal
  let sourceHead := Cell.scale combinedFactor sourcePoint
  let outer :=
    retainedTerminalFanOuterCompleteRoute
      center scaledTerminal slot
  let spoke :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  have combinedPositive : 0 < combinedFactor := by
    exact Nat.mul_pos (by native_decide) factorPositive
  have scaledSeparated :=
    separated.scale_left_rectangle_radius
      combinedPositive clearance
  have sourceHeadBounded :
      InClosedGridRectangle sourceHead sourceHead sourceHead := by
    simp [InClosedGridRectangle]
  have terminalPositive : 0 < scaledTerminal.2 := by
    exact scaleRetainedTerminalData_length_pos factorPositive
      (retainedTerminalDirectionClassify_sound classified).1
  have outerOrthogonal : OrthogonalPolyline outer := by
    exact retainedTerminalFanOuterCompleteRoute_orthogonal
      center scaledTerminal slot terminalPositive
  have outerBounded :
      ∀ point ∈ outer,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale combinedFactor finalSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale combinedFactor finalSegment.coordinateUpper))
          point := by
    intro point pointMember
    exact
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        route terminal slot routeLength classified pointMember
  have centerBounded :
      InClosedGridRectangle
        (Cell.scale combinedFactor finalSegment.coordinateLower)
        (Cell.scale combinedFactor finalSegment.coordinateUpper)
        center := by
    have productNonnegative : (0 : Int) ≤ combinedFactor := by
      exact_mod_cast Nat.zero_le combinedFactor
    have endpointBounded :=
      finalSegment.finish_in_coordinateRectangle.scale
        productNonnegative
    have centerEq :
        center =
          Cell.scale combinedFactor (route.getLastD (0, 0)) := by
      dsimp [center, combinedFactor]
      rw [scalePolyline_getLastD, Cell.scale_scale]
    rw [centerEq]
    simpa [finalSegment] using endpointBounded
  have spokeBounded :
      ∀ point ∈ spoke,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale combinedFactor finalSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale combinedFactor finalSegment.coordinateUpper))
          point := by
    intro point pointMember
    apply inClosedGridRectangle_coordinateRadius_mono
      (inClosedGridRectangle_coordinateRadius_of_center
        centerBounded
        (retainedTerminalFanFigure7SpokeRouteAt_point_within
          center slot point pointMember))
    omega
  have spokeOrthogonal : OrthogonalPolyline spoke :=
    retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  constructor
  · intro sourceMember
    have bounded :=
      unitSubdividePolyline_points_in_rectangle
        outerOrthogonal outerBounded sourceMember
    exact
      (ne_of_inClosedGridRectangles_of_separated
        sourceHeadBounded bounded scaledSeparated) rfl
  · intro sourceMember
    have bounded :=
      unitSubdividePolyline_points_in_rectangle
        spokeOrthogonal spokeBounded sourceMember
    exact
      (ne_of_inClosedGridRectangles_of_separated
        sourceHeadBounded bounded scaledSeparated) rfl

end PeriodicOrthocrossing
end LeanTrominoes
