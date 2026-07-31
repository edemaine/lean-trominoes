import LeanTrominoes.RetainedAngularFanOuterEscapedRoutes
import LeanTrominoes.RetainedAngularFanSourceSplice
import LeanTrominoes.OrthogonalPolylineScaling

/-!
# Source splices with a delayed outer-lane shift

The ordinary outer fan selects its occurrence lane immediately at the
deleted-final-point gate.  When that gate is also a shared clause head, the
short tangential lane shift can follow another incidence route out of the
clause.  The source-escaped fan instead follows its own terminal direction
for 64 primitive blocks before making the same lane shift.

This file packages that escaped fan as a drop-in replacement tail.  It has
the same source gate and Figure 7 boundary endpoint as the ordinary fan, so
only the geometry of the source-side prefix changes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Source polyline at the combined refinement with its old variable
endpoint replaced by the source-escaped complete outer fan. -/
def retainedAngularFanEscapedSplicedBoundaryPolyline
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  replacePolylineTail
    (scalePolyline retainedTerminalFanTotalRefinement route)
    (retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot)

/-- Rasterized source prefix followed by the source-escaped complete outer
fan. -/
def retainedAngularFanEscapedSplicedBoundaryRoute
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  rasterizeRetainedPolyline
    (retainedAngularFanEscapedSplicedBoundaryPolyline
      route terminal slot)

/-- If the retained source route is already orthogonal, the delayed-lane
escaped tail replacement is orthogonal before rasterization as well. -/
theorem retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedAngularFanEscapedSplicedBoundaryPolyline
        route terminal slot) := by
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have reverseTailExists :
      ∃ entrance, scaledRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      scaledRoute scaledLength
  have lastEntranceEq :
      polylineLastEntrance scaledRoute =
        (retainedAngularFanOuterDemand
          center terminal slot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      routeLength classified slot
  have reverseTailHead :
      scaledRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    exact retainedTerminalFanOuterEscapedCompleteRoute_head?
      center terminal slot
  have lengthPositive : 0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have scaledOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline scaledRoute :=
    PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
      routeOrthogonal (by native_decide)
  have replacementOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
      center terminal slot lengthPositive escapeFits
  simpa [retainedAngularFanEscapedSplicedBoundaryPolyline,
    scaledRoute, center, replacement] using
    scaledOrthogonal.replaceTail
      replacementOrthogonal replacementHead reverseTailHead

/-- A classified retained source route admits the escaped splice whenever
its scaled terminal is long enough for the fixed 64-block delay.  The
result has exactly the same endpoints and orthogonality contract as the
ordinary splice. -/
theorem retainedAngularFanEscapedSplicedBoundaryRoute_valid
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (retained : RetainedRayPolyline route)
    {source : Cell}
    (routeHead : route.head? = some source)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        (route.getLastD (0, 0))
    (retainedAngularFanEscapedSplicedBoundaryRoute
      route terminal slot).head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement source) ∧
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot).getLast? =
          some
            (Cell.add center
              (Cell.scale retainedTerminalFanRoutingRefinement
                (angularFanBoundaryOffset slot.val))) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryRoute
          route terminal slot) := by
  dsimp only
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have reverseTailExists :
      ∃ entrance, scaledRoute.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      scaledRoute scaledLength
  have lastEntranceEq :
      polylineLastEntrance scaledRoute =
        (retainedAngularFanOuterDemand
          center terminal slot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      routeLength classified slot
  have reverseTailHead :
      scaledRoute.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    rw [polylineLastEntrance_spec reverseTailExists,
      lastEntranceEq]
  have dropLastLast :
      scaledRoute.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate :=
    dropLast_getLast?_of_reverse_tail_head?
      reverseTailHead
  have replacementHead :
      replacement.head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
    exact retainedTerminalFanOuterEscapedCompleteRoute_head?
      center terminal slot
  have lengthPositive :
      0 < terminal.2 :=
    (retainedTerminalDirectionClassify_sound classified).1
  have replacementLast :
      replacement.getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) :=
    retainedTerminalFanOuterEscapedCompleteRoute_getLast?
      center terminal slot lengthPositive escapeFits
  have scaledHead :
      scaledRoute.head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement source) := by
    simp [scaledRoute, scalePolyline, routeHead]
  have replacedHead :
      (replacePolylineTail scaledRoute replacement).head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement source) :=
    replacePolylineTail_head?
      replacementHead reverseTailHead scaledHead
  have replacedLast :
      (replacePolylineTail scaledRoute replacement).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) :=
    replacePolylineTail_getLast? replacementLast
  have scaledRetained :
      RetainedRayPolyline scaledRoute :=
    retained.scale (by native_decide)
  have replacementRetained :
      RetainedRayPolyline replacement :=
    RetainedRayPolyline.of_orthogonal
      (retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
        center terminal slot lengthPositive escapeFits)
  have replacedRetained :
      RetainedRayPolyline
        (replacePolylineTail scaledRoute replacement) :=
    scaledRetained.replaceTail replacementRetained
      dropLastLast replacementHead
  exact
    ⟨by
      simpa [retainedAngularFanEscapedSplicedBoundaryRoute,
        retainedAngularFanEscapedSplicedBoundaryPolyline,
        scaledRoute, center, replacement] using replacedHead,
    by
      simpa [retainedAngularFanEscapedSplicedBoundaryRoute,
        retainedAngularFanEscapedSplicedBoundaryPolyline,
        scaledRoute, center, replacement] using replacedLast,
    rasterizeRetainedPolyline_orthogonal replacedRetained⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
