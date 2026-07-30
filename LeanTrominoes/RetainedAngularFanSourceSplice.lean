import LeanTrominoes.RetainedRayPolylineTailReplacement
import LeanTrominoes.RetainedAngularFanOuterRouteFamily

/-!
# Splicing retained source routes into the refined angular fan

The retained source route is first scaled by the combined factor
`36 * 8 = 288`.  Its old variable endpoint is then replaced at the exact
classified penultimate gate by the complete separated outer fan route.
The result still consists only of retained rays, so whole-route
rasterization produces an orthogonal route from the scaled source clause to
the factor-eight Figure 7 boundary.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Rasterized source prefix with its former variable endpoint replaced by
one complete outer fan route. -/
def retainedAngularFanSplicedBoundaryRoute
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  rasterizeRetainedPolyline
    (replacePolylineTail
      (scalePolyline retainedTerminalFanTotalRefinement route)
      (retainedTerminalFanOuterCompleteRoute
        center terminal slot))

/-- A classified genuine retained source route splices to its selected
refined Figure 7 boundary with exact endpoints and orthogonality. -/
theorem retainedAngularFanSplicedBoundaryRoute_valid
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
    (routeHead : route.head? = some source) :
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        (route.getLastD (0, 0))
    (retainedAngularFanSplicedBoundaryRoute
      route terminal slot).head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement source) ∧
      (retainedAngularFanSplicedBoundaryRoute
        route terminal slot).getLast? =
          some
            (Cell.add center
              (Cell.scale retainedTerminalFanRoutingRefinement
                (angularFanBoundaryOffset slot.val))) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryRoute
          route terminal slot) := by
  dsimp only
  let scaledRoute :=
    scalePolyline retainedTerminalFanTotalRefinement route
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterCompleteRoute
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
    exact retainedTerminalFanOuterCompleteRoute_head?
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
    retainedTerminalFanOuterCompleteRoute_getLast?
      center terminal slot lengthPositive
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
      RetainedRayPolyline scaledRoute := by
    exact retained.scale (by native_decide)
  have replacementRetained :
      RetainedRayPolyline replacement :=
    RetainedRayPolyline.of_orthogonal
      (retainedTerminalFanOuterCompleteRoute_orthogonal
        center terminal slot lengthPositive)
  have replacedRetained :
      RetainedRayPolyline
        (replacePolylineTail scaledRoute replacement) :=
    scaledRetained.replaceTail replacementRetained
      dropLastLast replacementHead
  exact ⟨by
      simpa [retainedAngularFanSplicedBoundaryRoute,
        scaledRoute, center, replacement] using replacedHead,
    by
      simpa [retainedAngularFanSplicedBoundaryRoute,
        scaledRoute, center, replacement] using replacedLast,
    rasterizeRetainedPolyline_orthogonal
      replacedRetained⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
