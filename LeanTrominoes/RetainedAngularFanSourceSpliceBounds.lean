/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularSuffixSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedSourceSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice

/-!
# Bounding boxes for source/fan splices and Figure 7 suffixes

A source-scaled boundary splice stays in the radius-288 expansion of any
closed rectangle containing its raw source route.  The retained source
prefix lies in the scaled rectangle itself, while the replacement fan is
already bounded by the corresponding expansion of the discarded final
segment.

The complementary Figure 7 suffix stays within coordinate radius 96 of its
scaled canonical source center.  These two bounds turn cross-splice
separation into a small rectangle calculation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- A radius-expanded scaled segment rectangle is contained in the same
radius expansion of any rectangle containing both segment endpoints. -/
theorem
    in_scaledSegmentCoordinateRadius_imp_in_scaledRectangleCoordinateRadius
    {factor radius : Nat}
    {segment : GridSegment}
    {lower upper point : Cell}
    (startBounded :
      InClosedGridRectangle lower upper segment.start)
    (finishBounded :
      InClosedGridRectangle lower upper segment.finish)
    (pointBounded :
      InClosedGridRectangle
        (coordinateRadiusLower radius
          (Cell.scale factor segment.coordinateLower))
        (coordinateRadiusUpper radius
          (Cell.scale factor segment.coordinateUpper))
        point) :
    InClosedGridRectangle
      (coordinateRadiusLower radius
        (Cell.scale factor lower))
      (coordinateRadiusUpper radius
        (Cell.scale factor upper))
      point := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases lower with ⟨lowerX, lowerY⟩
  rcases upper with ⟨upperX, upperY⟩
  rcases point with ⟨pointX, pointY⟩
  have factorNonnegative : (0 : Int) ≤ factor := by
    positivity
  simp only [InClosedGridRectangle,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale] at startBounded finishBounded pointBounded ⊢
  have startLowerX :=
    mul_le_mul_of_nonneg_left
      startBounded.1 factorNonnegative
  have startUpperX :=
    mul_le_mul_of_nonneg_left
      startBounded.2.1 factorNonnegative
  have startLowerY :=
    mul_le_mul_of_nonneg_left
      startBounded.2.2.1 factorNonnegative
  have startUpperY :=
    mul_le_mul_of_nonneg_left
      startBounded.2.2.2 factorNonnegative
  have finishLowerX :=
    mul_le_mul_of_nonneg_left
      finishBounded.1 factorNonnegative
  have finishUpperX :=
    mul_le_mul_of_nonneg_left
      finishBounded.2.1 factorNonnegative
  have finishLowerY :=
    mul_le_mul_of_nonneg_left
      finishBounded.2.2.1 factorNonnegative
  have finishUpperY :=
    mul_le_mul_of_nonneg_left
      finishBounded.2.2.2 factorNonnegative
  simp_all [min_def, max_def]
  all_goals omega

/-- Every point of an ordinary source-scaled splice lies in the radius-288
expansion of any raw source-route rectangle. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryPolyline_point_in_routeRectangle
    {factor : Nat}
    (factorPositive : 0 < factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (lower upper : Cell)
    (routeBounded :
      ∀ point ∈ route,
        InClosedGridRectangle lower upper point)
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          lower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          upper))
      point := by
  let scaledRoute :=
    scalePolyline factor route
  let refinedRoute :=
    scalePolyline retainedTerminalFanTotalRefinement scaledRoute
  let scaledTerminal :=
    scaleRetainedTerminalData factor terminal
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (scaledRoute.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterCompleteRoute
      center scaledTerminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified
        factorPositive classified
  have refinedLength : 2 ≤ refinedRoute.length := by
    simpa [refinedRoute, scalePolyline] using scaledLength
  have reverseTailExists :
      ∃ entrance, refinedRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      refinedRoute refinedLength
  have lastEntranceEq :
      polylineLastEntrance refinedRoute =
        (retainedAngularFanOuterDemand
          center scaledTerminal slot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      scaledLength scaledClassified slot
  have reverseTailHead :
      refinedRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have routeEntrance :
      refinedRoute.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate :=
    dropLast_getLast?_of_reverse_tail_head?
      reverseTailHead
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate :=
    retainedTerminalFanOuterCompleteRoute_head?
      center scaledTerminal slot
  rw [retainedAngularFanSplicedBoundaryPolyline,
    show
      scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor route) =
        refinedRoute by rfl,
    show
      retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal) slot =
        replacement by rfl,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      refinedRoute replacement routeEntrance replacementHead]
      at pointMember
  rcases mem_joinAtEndpoint pointMember with
    prefixMember | replacementMember
  · have refinedMember :
        point ∈ refinedRoute :=
      List.mem_of_mem_dropLast prefixMember
    unfold refinedRoute scaledRoute scalePolyline at refinedMember
    rw [List.mem_map] at refinedMember
    rcases refinedMember with
      ⟨scaledPoint, scaledPointMember, rfl⟩
    rw [List.mem_map] at scaledPointMember
    rcases scaledPointMember with
      ⟨rawPoint, rawPointMember, rfl⟩
    have scaledBound :=
      (routeBounded rawPoint rawPointMember).scale
        (show
          (0 : Int) ≤
            retainedTerminalFanTotalRefinement * factor by
          positivity)
    rw [Cell.scale_scale]
    simpa [Nat.cast_mul] using
      inClosedGridRectangle_coordinateRadius_of_center
        scaledBound
        (withinCoordinateRadius_refl 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            rawPoint))
  · let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    have finalBound :=
      retainedTerminalFanOuterCompleteRoute_point_in_scaledFinalSegmentRectangle
        route terminal slot routeLength classified
        replacementMember
    have reverseTailRaw :
        ∃ entrance, route.reverse.tail.head? =
          some entrance :=
      exists_reverse_tail_head?_of_two_le_length route routeLength
    have entranceMember :
        polylineLastEntrance route ∈ route := by
      have entranceLast :
          route.dropLast.getLast? =
            some (polylineLastEntrance route) :=
        dropLast_getLast?_of_reverse_tail_head?
          (polylineLastEntrance_spec reverseTailRaw)
      exact List.mem_of_mem_dropLast
        (mem_of_getLast?_eq_some entranceLast)
    have targetMember :
        route.getLastD (0, 0) ∈ route := by
      have nonempty : route ≠ [] := by
        intro empty
        rw [empty] at routeLength
        simp at routeLength
      have lastEq :
          route.getLastD (0, 0) =
            route.getLast nonempty := by
        rw [List.getLastD_eq_getLast?,
          List.getLast?_eq_getLast_of_ne_nil nonempty]
        rfl
      rw [lastEq]
      exact List.getLast_mem nonempty
    exact
      in_scaledSegmentCoordinateRadius_imp_in_scaledRectangleCoordinateRadius
        (segment := finalSegment)
        (routeBounded _ entranceMember)
        (routeBounded _ targetMember)
        (by simpa [finalSegment] using finalBound)

/-- Every point of an escaped source-scaled splice satisfies the same raw
route rectangle bound. -/
theorem
    retainedAngularFanSourceScaledEscapedSplicedBoundaryPolyline_point_in_routeRectangle
    {factor : Nat}
    (factorPositive : 0 < factor)
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
    (lower upper : Cell)
    (routeBounded :
      ∀ point ∈ route,
        InClosedGridRectangle lower upper point)
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanEscapedSplicedBoundaryPolyline
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          lower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * factor)
          upper))
      point := by
  let scaledRoute :=
    scalePolyline factor route
  let refinedRoute :=
    scalePolyline retainedTerminalFanTotalRefinement scaledRoute
  let scaledTerminal :=
    scaleRetainedTerminalData factor terminal
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (scaledRoute.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center scaledTerminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified
        factorPositive classified
  have refinedLength : 2 ≤ refinedRoute.length := by
    simpa [refinedRoute, scalePolyline] using scaledLength
  have reverseTailExists :
      ∃ entrance, refinedRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      refinedRoute refinedLength
  have lastEntranceEq :
      polylineLastEntrance refinedRoute =
        (retainedAngularFanOuterDemand
          center scaledTerminal slot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      scaledLength scaledClassified slot
  have reverseTailHead :
      refinedRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have routeEntrance :
      refinedRoute.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate :=
    dropLast_getLast?_of_reverse_tail_head?
      reverseTailHead
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center scaledTerminal slot).gate :=
    retainedTerminalFanOuterEscapedCompleteRoute_head?
      center scaledTerminal slot
  rw [retainedAngularFanEscapedSplicedBoundaryPolyline,
    show
      scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor route) =
        refinedRoute by rfl,
    show
      retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal) slot =
        replacement by rfl,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      refinedRoute replacement routeEntrance replacementHead]
      at pointMember
  rcases mem_joinAtEndpoint pointMember with
    prefixMember | replacementMember
  · have refinedMember :
        point ∈ refinedRoute :=
      List.mem_of_mem_dropLast prefixMember
    unfold refinedRoute scaledRoute scalePolyline at refinedMember
    rw [List.mem_map] at refinedMember
    rcases refinedMember with
      ⟨scaledPoint, scaledPointMember, rfl⟩
    rw [List.mem_map] at scaledPointMember
    rcases scaledPointMember with
      ⟨rawPoint, rawPointMember, rfl⟩
    have scaledBound :=
      (routeBounded rawPoint rawPointMember).scale
        (show
          (0 : Int) ≤
            retainedTerminalFanTotalRefinement * factor by
          positivity)
    rw [Cell.scale_scale]
    simpa [Nat.cast_mul] using
      inClosedGridRectangle_coordinateRadius_of_center
        scaledBound
        (withinCoordinateRadius_refl 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * factor)
            rawPoint))
  · let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    have finalBound :=
      retainedTerminalFanOuterEscapedCompleteRoute_point_in_scaledFinalSegmentRectangle
        route terminal slot routeLength classified
        escapeFits replacementMember
    have reverseTailRaw :
        ∃ entrance, route.reverse.tail.head? =
          some entrance :=
      exists_reverse_tail_head?_of_two_le_length route routeLength
    have entranceMember :
        polylineLastEntrance route ∈ route := by
      have entranceLast :
          route.dropLast.getLast? =
            some (polylineLastEntrance route) :=
        dropLast_getLast?_of_reverse_tail_head?
          (polylineLastEntrance_spec reverseTailRaw)
      exact List.mem_of_mem_dropLast
        (mem_of_getLast?_eq_some entranceLast)
    have targetMember :
        route.getLastD (0, 0) ∈ route := by
      have nonempty : route ≠ [] := by
        intro empty
        rw [empty] at routeLength
        simp at routeLength
      have lastEq :
          route.getLastD (0, 0) =
            route.getLast nonempty := by
        rw [List.getLastD_eq_getLast?,
          List.getLast?_eq_getLast_of_ne_nil nonempty]
        rfl
      rw [lastEq]
      exact List.getLast_mem nonempty
    exact
      in_scaledSegmentCoordinateRadius_imp_in_scaledRectangleCoordinateRadius
        (segment := finalSegment)
        (routeBounded _ entranceMember)
        (routeBounded _ targetMember)
        (by simpa [finalSegment] using finalBound)

/-- A factor-eight Figure 7 suffix lies within coordinate radius 96 of the
factor-288 refinement of its canonical source center. -/
theorem scaledAngularOccurrenceSuffix_point_in_centerRectangle
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    {point : Cell}
    (pointMember :
      point ∈
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex)) :
    InClosedGridRectangle
      (coordinateRadiusLower 96
        (Cell.scale
          (retainedTerminalFanRoutingRefinement *
            PeriodicEightOccurrenceSplitPositioned.refinementScale)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement clause literal)))
      (coordinateRadiusUpper 96
        (Cell.scale
          (retainedTerminalFanRoutingRefinement *
            PeriodicEightOccurrenceSplitPositioned.refinementScale)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement clause literal)))
      point := by
  unfold angularOccurrenceSuffix at pointMember
  rw [angularFanSpokeRouteAt_eq_map_add] at pointMember
  unfold scalePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with
    ⟨unscaledPoint, unscaledMember, rfl⟩
  rw [List.mem_map] at unscaledMember
  rcases unscaledMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    spokeRoute_inClosedGridRectangle
      (angularPortOfIndex
        (angularOccurrenceIndex order
          literal clauseIndex literalIndex))
      localPoint localPointMember
  rw [angularFanOccurrenceOrigin_incidenceRelativeOffset]
  rcases
      PositionedPeriodicCNF.canonicalLiteralPosition
        sourcePlacement clause literal with
    ⟨centerX, centerY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  simp only [InClosedGridRectangle] at localBound
  simp only [coordinateRadiusLower, coordinateRadiusUpper,
    retainedTerminalFanRoutingRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    Cell.scale, Cell.add, Cell.sub,
    InClosedGridRectangle]
  omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
