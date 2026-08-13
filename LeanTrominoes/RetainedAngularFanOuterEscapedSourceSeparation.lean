/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterEscapedRoutes
import LeanTrominoes.RetainedAngularFanOuterSourceSeparation

/-!
# Source-terminal bounds for escaped outer fans

Delaying the occurrence-lane shift does not enlarge the corridor used by an
ordinary outer fan.  The first 64 primitive blocks lie on the unshifted
source-terminal axis; the lane shift remains within radius 56; and the
remaining retained-ray raster remains within radius nine of the shifted
lane.  Thus the complete escaped fan stays in the same radius-288 expansion
of its discarded source-terminal rectangle.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 4096

private theorem retainedTerminalFanOuterInwardRay_length
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterInwardRay terminal).length =
      retainedTerminalFanOuterRadialLength terminal := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem retainedTerminalFanOuterSourceEscapeRay_length
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterSourceEscapeRay terminal).length =
      retainedTerminalFanOuterSourceEscapeLength := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem retainedTerminalFanOuterSourceEscapeRay_primitive
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterSourceEscapeRay terminal).primitive =
      (retainedTerminalFanOuterInwardRay terminal).primitive := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem retainedTerminalFanOuterEscapedRemainingRay_length
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterEscapedRemainingRay terminal).length =
      (retainedTerminalFanOuterInwardRay terminal).length -
        retainedTerminalFanOuterSourceEscapeLength := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem retainedTerminalFanOuterEscapedRemainingRay_primitive
    (terminal : RetainedTerminalData) :
    (retainedTerminalFanOuterEscapedRemainingRay terminal).primitive =
      (retainedTerminalFanOuterInwardRay terminal).primitive := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

private theorem retainedTerminalFanOuterSourceEscapePoint_eq_checkpoint
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterSourceEscapePoint
        center terminal slot =
      Cell.add
        (retainedAngularFanOuterDemand
          center terminal slot).gate
        (Cell.scale retainedTerminalFanOuterSourceEscapeLength
          (retainedTerminalFanOuterInwardRay terminal).primitive) := by
  unfold retainedTerminalFanOuterSourceEscapePoint
  rw [RetainedRay.vector_eq_scale_length_primitive,
    retainedTerminalFanOuterSourceEscapeRay_length,
    retainedTerminalFanOuterSourceEscapeRay_primitive]

/-- Every point of an escaped radial route lies in the same radius-65 tube
around the unshifted source-terminal checkpoints as an ordinary route. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_point_in_tube
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        (retainedTerminalFanOuterInwardRay terminal).length)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterEscapedRadialRoute
          center terminal slot) :
    let gate :=
      (retainedAngularFanOuterDemand
        center terminal slot).gate
    InCoordinateCheckpointTube 65 gate
      (retainedTerminalFanOuterInwardRay terminal).primitive
      (retainedTerminalFanOuterInwardRay terminal).length
      point := by
  dsimp only
  let gate :=
    (retainedAngularFanOuterDemand
      center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint
      center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  change
    InCoordinateCheckpointTube 65 gate
      (retainedTerminalFanOuterInwardRay terminal).primitive
      (retainedTerminalFanOuterInwardRay terminal).length
      point
  rw [retainedTerminalFanOuterEscapedRadialRoute] at pointMember
  change
    point ∈
      joinAtEndpoint
        ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
          gate)
        (joinAtEndpoint
          (retainedTerminalFanOuterLaneShiftRouteAt
            escapePoint terminal.1 slot)
          ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
            shiftedEscapePoint)) at pointMember
  rcases mem_joinAtEndpoint pointMember with
    escapeMember | shiftedTailMember
  · rcases
        (retainedTerminalFanOuterSourceEscapeRay terminal)
          |>.rasterize_point_near_checkpoint gate escapeMember with
      ⟨index, indexBound, pointNear⟩
    refine ⟨index, ?_, ?_⟩
    · rw [retainedTerminalFanOuterSourceEscapeRay_length]
        at indexBound
      omega
    · exact
        (by
          simpa [retainedTerminalFanOuterSourceEscapeRay_primitive]
            using pointNear.mono (by omega : 9 ≤ 65))
  · rcases mem_joinAtEndpoint shiftedTailMember with
      shiftMember | remainingMember
    · rcases
          retainedTerminalFanOuterLaneShiftRouteAt_point_in_tube
            escapePoint terminal.1 slot
            (retainedTerminalFanOuterInwardRay terminal).primitive
            0 shiftMember with
        ⟨index, indexBound, pointNear⟩
      have indexZero : index = 0 := by omega
      subst index
      refine
        ⟨retainedTerminalFanOuterSourceEscapeLength,
          escapeFits, ?_⟩
      simp [Cell.scale, Cell.add] at pointNear
      simpa [escapePoint,
        retainedTerminalFanOuterSourceEscapePoint_eq_checkpoint]
        using pointNear
    · rcases
          (retainedTerminalFanOuterEscapedRemainingRay terminal)
            |>.rasterize_point_near_checkpoint
              shiftedEscapePoint remainingMember with
        ⟨index, indexBound, pointNearShifted⟩
      have remainingBound :
          index ≤
            (retainedTerminalFanOuterInwardRay terminal).length -
              retainedTerminalFanOuterSourceEscapeLength := by
        simpa [retainedTerminalFanOuterEscapedRemainingRay_length]
          using indexBound
      refine
        ⟨retainedTerminalFanOuterSourceEscapeLength + index,
          by omega, ?_⟩
      let unshiftedCheckpoint :=
        Cell.add gate
          (Cell.scale
            (retainedTerminalFanOuterSourceEscapeLength + index)
            (retainedTerminalFanOuterInwardRay terminal).primitive)
      have shiftedCheckpointEq :
          Cell.add shiftedEscapePoint
              (Cell.scale index
                (retainedTerminalFanOuterEscapedRemainingRay
                  terminal).primitive) =
            Cell.add unshiftedCheckpoint
              (retainedTerminalFanOuterLaneOffset
                terminal.1 slot) := by
        rw [retainedTerminalFanOuterEscapedRemainingRay_primitive]
        simp [shiftedEscapePoint, escapePoint,
          retainedTerminalFanOuterSourceEscapePoint_eq_checkpoint,
          unshiftedCheckpoint, gate, Cell.add, Cell.scale]
        constructor <;> ring
      have laneNearUnshifted :
          WithinCoordinateRadius 56
            unshiftedCheckpoint
            (Cell.add shiftedEscapePoint
              (Cell.scale index
                (retainedTerminalFanOuterEscapedRemainingRay
                  terminal).primitive)) := by
        rw [shiftedCheckpointEq]
        have translated :=
          (retainedTerminalFanOuterLaneOffset_within_radius
            terminal.1 slot).translate
              unshiftedCheckpoint
        simpa [Cell.add] using translated
      exact
        (by
          simpa [unshiftedCheckpoint] using
            (laneNearUnshifted.trans pointNearShifted).mono
              (by omega : 56 + 9 ≤ 65))

/-- Every complete escaped-fan point lies either in its radius-65
source-terminal tube or in the fixed radius-288 local fan square. -/
theorem retainedTerminalFanOuterEscapedCompleteRoute_point_in_corridor
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        (retainedTerminalFanOuterInwardRay terminal).length)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot) :
    let gate :=
      (retainedAngularFanOuterDemand
        center terminal slot).gate
    InCoordinateCheckpointTube 65 gate
        (retainedTerminalFanOuterInwardRay terminal).primitive
        (retainedTerminalFanOuterInwardRay terminal).length
        point ∨
      WithinCoordinateRadius 288 center point := by
  dsimp only
  rw [retainedTerminalFanOuterEscapedCompleteRoute] at pointMember
  rcases mem_joinAtEndpoint pointMember with
    radialMember | localMember
  · exact Or.inl
      (retainedTerminalFanOuterEscapedRadialRoute_point_in_tube
        center terminal slot escapeFits radialMember)
  · right
    rw [retainedTerminalFanOuterLocalRouteAt,
      List.mem_map] at localMember
    rcases localMember with
      ⟨offset, offsetMember, rfl⟩
    have localBound :=
      retainedTerminalFanOuterLocalRoute_points_within_outer_frame
        terminal.1 slot offset offsetMember
    have translated := localBound.translate center
    simpa [Cell.add] using translated

/-- Every point of a complete escaped outer fan lies in the radius-288
expansion of the combined-scaled discarded source-terminal rectangle. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
    {factor : Nat}
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor terminal))
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal)
          slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          (⟨polylineLastEntrance route,
              route.getLastD (0, 0)⟩ :
            GridSegment).coordinateUpper))
      point := by
  have corridor :=
    retainedTerminalFanOuterEscapedCompleteRoute_point_in_corridor
      (Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor route).getLastD (0, 0)))
      (scaleRetainedTerminalData factor terminal)
      slot
      (by
        simpa [retainedTerminalFanOuterInwardRay_length]
          using escapeFits)
      pointMember
  rcases corridor with radialBound | localBound
  · have sourceBound :=
      inCoordinateCheckpointTube_outerInward_to_sourceTerminal
        65
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor route).getLastD (0, 0)))
        (scaleRetainedTerminalData factor terminal)
        slot radialBound
    have rectangleBound :=
      inCoordinateSourceTerminalTube_in_coordinateRectangle
        sourceBound
    have productNonnegative :
        (0 : Int) ≤
          retainedTerminalFanTotalRefinement * factor := by
      exact_mod_cast
        Nat.zero_le
          (retainedTerminalFanTotalRefinement * factor)
    rw [
      retainedTerminalFanSourceCorridorAxis_eq_scale_finalSegment
        route terminal routeLength classified,
      GridSegment.coordinateLower_scale productNonnegative,
      GridSegment.coordinateUpper_scale productNonnegative]
        at rectangleBound
    exact
      inClosedGridRectangle_coordinateRadius_mono
        rectangleBound (by omega)
  · have productNonnegative :
        (0 : Int) ≤
          retainedTerminalFanTotalRefinement * factor := by
      exact_mod_cast
        Nat.zero_le
          (retainedTerminalFanTotalRefinement * factor)
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    have centerBounded :
        InClosedGridRectangle
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            finalSegment.coordinateLower)
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            finalSegment.coordinateUpper)
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0))) := by
      have finishBounded :=
        finalSegment.finish_in_coordinateRectangle.scale
          productNonnegative
      rw [scalePolyline_getLastD, Cell.scale_scale]
      simpa [finalSegment, Nat.cast_mul] using finishBounded
    simpa [finalSegment] using
      inClosedGridRectangle_coordinateRadius_of_center
        centerBounded localBound

/-- Separated discarded source-terminal rectangles strictly separate an
escaped outer fan from an ordinary outer fan. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_ordinary_of_finalSegmentRectanglesSeparated
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor firstTerminal))
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (⟨polylineLastEntrance firstRoute,
            firstRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance firstRoute,
            firstRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper
        (⟨polylineLastEntrance secondRoute,
            secondRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance secondRoute,
            secondRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor firstRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor secondRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have combinedPositive :
      0 <
        retainedTerminalFanTotalRefinement * factor :=
    Nat.mul_pos (by native_decide) factorPositive
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance secondRoute,
                secondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance secondRoute,
                secondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
  · intro point pointMember
    exact
      retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
        firstRoute firstTerminal firstSlot
        firstLength firstClassified firstEscapeFits pointMember
  · intro point pointMember
    exact
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        secondRoute secondTerminal secondSlot
        secondLength secondClassified pointMember
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        rectanglesSeparated combinedPositive clearance

/-- Separated discarded source-terminal rectangles also strictly separate
two escaped outer fans. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_finalSegmentRectanglesSeparated
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor firstTerminal))
    (secondEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor secondTerminal))
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (⟨polylineLastEntrance firstRoute,
            firstRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance firstRoute,
            firstRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper
        (⟨polylineLastEntrance secondRoute,
            secondRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateLower
        (⟨polylineLastEntrance secondRoute,
            secondRoute.getLastD (0, 0)⟩ :
          GridSegment).coordinateUpper) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor firstRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor secondRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have combinedPositive :
      0 <
        retainedTerminalFanTotalRefinement * factor :=
    Nat.mul_pos (by native_decide) factorPositive
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance firstRoute,
                firstRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance secondRoute,
                secondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateLower))
      (secondUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            (⟨polylineLastEntrance secondRoute,
                secondRoute.getLastD (0, 0)⟩ :
              GridSegment).coordinateUpper))
  · intro point pointMember
    exact
      retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
        firstRoute firstTerminal firstSlot
        firstLength firstClassified firstEscapeFits pointMember
  · intro point pointMember
    exact
      retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
        secondRoute secondTerminal secondSlot
        secondLength secondClassified secondEscapeFits pointMember
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        rectanglesSeparated combinedPositive clearance

end PeriodicEightOccurrenceSplit
end LeanTrominoes
