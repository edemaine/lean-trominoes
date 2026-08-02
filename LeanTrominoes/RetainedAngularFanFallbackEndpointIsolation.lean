import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin
import LeanTrominoes.RetainedAngularFanOccurrenceSuffixSimplicity
import LeanTrominoes.RetainedAngularFanSourceCompleteOwnCycleSeparation

/-!
# Endpoint isolation for retained angular-fan fallbacks

The ordinary and delayed-lane fallback prefixes strictly avoid their own
inner implication cycle.  A selected cycle edge ends at the same ring vertex
as the matching Figure 7 spoke.  That cycle therefore witnesses that the
prefix cannot visit the spoke's target, while simplicity of the spoke rules
out a second visit within the suffix.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every centered factor-eight Figure 7 spoke contains a genuine edge. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_length_ge_two
    (center : Cell) (slot : RetainedTerminalSlot) :
    2 ≤ (retainedTerminalFanFigure7SpokeRouteAt center slot).length := by
  unfold retainedTerminalFanFigure7SpokeRouteAt
    translatePolyline scalePolyline
  simp only [List.length_map]
  generalize portEquation : angularPortOfIndex slot.val = port
  cases port <;> native_decide

/-- Every centered factor-eight Figure 7 spoke is orthogonal. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_orthogonal
    (center : Cell) (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedTerminalFanFigure7SpokeRouteAt center slot) := by
  have localRoute : OrthogonalPolyline
      (spokeRoute (angularPortOfIndex slot.val)) := by
    generalize portEquation : angularPortOfIndex slot.val = port
    cases port <;> native_decide
  unfold retainedTerminalFanFigure7SpokeRouteAt
  apply OrthogonalPolyline.translate
  apply OrthogonalPolyline.translate
  exact localRoute.scalePolyline (by native_decide)

/-- Every centered factor-eight Figure 7 spoke is geometrically simple. -/
theorem retainedTerminalFanFigure7SpokeRouteAt_isSimple
    (center : Cell) (slot : RetainedTerminalSlot) :
    LocalIncidenceDrawing.RouteIsSimple
      (retainedTerminalFanFigure7SpokeRouteAt center slot) := by
  unfold retainedTerminalFanFigure7SpokeRouteAt
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
  exact routeIsSimple_scalePolyline
    (by native_decide)
    (spokeRoute_isSimple (angularPortOfIndex slot.val))

/-- The implication edge entering the spoke's ring vertex is orthogonal. -/
theorem retainedTerminalFanSelectedInnerCycleRouteAt_orthogonal
    (center : Cell) (slot : RetainedTerminalSlot) :
    OrthogonalPolyline
      (retainedTerminalFanInnerCycleRouteAt center
        (.port (angularPortOfIndex slot.val)) ⟨0, by omega⟩) := by
  have localRoute : OrthogonalPolyline
      (cycleRoute (.port (angularPortOfIndex slot.val)) 0) := by
    generalize portEquation : angularPortOfIndex slot.val = port
    cases port <;> native_decide
  unfold retainedTerminalFanInnerCycleRouteAt
    retainedTerminalFanInnerCycleRoute
  apply OrthogonalPolyline.translate
  apply OrthogonalPolyline.translate
  exact localRoute.scalePolyline (by native_decide)

/-- The selected spoke and entering implication edge have the same final
ring vertex. -/
theorem
    retainedTerminalFanFigure7SpokeRouteAt_getLast?_eq_selectedInnerCycle
    (center : Cell) (slot : RetainedTerminalSlot) :
    (retainedTerminalFanFigure7SpokeRouteAt center slot).getLast? =
      (retainedTerminalFanInnerCycleRouteAt center
        (.port (angularPortOfIndex slot.val))
        ⟨0, by omega⟩).getLast? := by
  unfold retainedTerminalFanFigure7SpokeRouteAt
    retainedTerminalFanInnerCycleRouteAt
    retainedTerminalFanInnerCycleRoute
    translatePolyline scalePolyline
  generalize portEquation : angularPortOfIndex slot.val = port
  cases port <;>
    simp [spokeRoute, cycleRoute,
      ringVariablePosition, OccurrenceSplitRing.variablePosition,
      retainedTerminalFanRoutingRefinement,
      Cell.add, Cell.sub, Cell.scale]

/-- A complete ordinary fallback occurrence does not revisit its final
Figure 7 endpoint after unit subdivision. -/
theorem retainedAngularFanSplicedOwnFigure7Route_lastNotInDropLast
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (source finalPoint : Cell)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeHead : route.head? = some source)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal : OrthogonalPolyline route)
    (retained : RetainedRayPolyline route)
    (radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint)) := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let prefixRoute :=
    retainedAngularFanSplicedBoundaryRoute route terminal slot
  let suffixRoute :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  let cycleRoute :=
    retainedTerminalFanInnerCycleRouteAt center
      (.port (angularPortOfIndex slot.val)) ⟨0, by omega⟩
  have boundaryValid :=
    retainedAngularFanSplicedBoundaryRoute_valid
      route terminal slot routeLength classified retained routeHead
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have prefixHead :
      prefixRoute.head? =
        some (Cell.scale retainedTerminalFanTotalRefinement source) := by
    simpa [prefixRoute, center, routeLastD] using boundaryValid.1
  have prefixNonempty : prefixRoute ≠ [] := by
    intro prefixEmpty
    simp [prefixEmpty] at prefixHead
  have suffixLength : 2 ≤ suffixRoute.length := by
    exact retainedTerminalFanFigure7SpokeRouteAt_length_ge_two center slot
  have suffixNonempty : suffixRoute ≠ [] := by
    intro suffixEmpty
    simp [suffixEmpty] at suffixLength
  let target := suffixRoute.getLast suffixNonempty
  have suffixLast : suffixRoute.getLast? = some target :=
    List.getLast?_eq_some_getLast suffixNonempty
  have cycleLast : cycleRoute.getLast? = some target := by
    rw [← suffixLast]
    exact
      (retainedTerminalFanFigure7SpokeRouteAt_getLast?_eq_selectedInnerCycle
        center slot).symm
  have strict : RoutesStrictlyAvoidEachOther prefixRoute cycleRoute := by
    simpa [prefixRoute, cycleRoute, center] using
      retainedAngularFanSplicedBoundaryRoute_strictlyAvoids_ownInnerCycleRouteAt
        route terminal slot finalPoint
        (.port (angularPortOfIndex slot.val)) ⟨0, by omega⟩
        routeLength classified simple routeFinal routeOrthogonal
        radialLengthPositive
  unfold retainedAngularFanSplicedOwnFigure7Route
  apply
    AxisDirection.lastNotInDropLast_unitSubdividePolyline_joinAtEndpoint_of_strictCycle
      prefixNonempty suffixLength
  · simpa [prefixRoute, center, routeLastD] using boundaryValid.2.2
  · exact retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  · exact
      retainedTerminalFanSelectedInnerCycleRouteAt_orthogonal center slot
  · simpa [prefixRoute, center, routeLastD] using boundaryValid.2.1
  · simpa [suffixRoute, center,
      List.getLastD_eq_getLast?, routeFinal] using
      retainedTerminalFanFigure7SpokeRouteAt_head? center slot
  · exact suffixLast
  · exact cycleLast
  · exact strict
  · exact retainedTerminalFanFigure7SpokeRouteAt_isSimple center slot

/-- A complete delayed-lane fallback occurrence does not revisit its final
Figure 7 endpoint after unit subdivision. -/
theorem retainedAngularFanEscapedSplicedOwnFigure7Route_lastNotInDropLast
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (source finalPoint : Cell)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (routeHead : route.head? = some source)
    (routeFinal : route.getLast? = some finalPoint)
    (routeOrthogonal : OrthogonalPolyline route)
    (retained : RetainedRayPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedAngularFanEscapedSplicedOwnFigure7Route
          route terminal slot finalPoint)) := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let prefixRoute :=
    retainedAngularFanEscapedSplicedBoundaryRoute route terminal slot
  let suffixRoute :=
    retainedTerminalFanFigure7SpokeRouteAt center slot
  let cycleRoute :=
    retainedTerminalFanInnerCycleRouteAt center
      (.port (angularPortOfIndex slot.val)) ⟨0, by omega⟩
  have boundaryValid :=
    retainedAngularFanEscapedSplicedBoundaryRoute_valid
      route terminal slot routeLength classified retained routeHead escapeFits
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have prefixHead :
      prefixRoute.head? =
        some (Cell.scale retainedTerminalFanTotalRefinement source) := by
    simpa [prefixRoute, center, routeLastD] using boundaryValid.1
  have prefixNonempty : prefixRoute ≠ [] := by
    intro prefixEmpty
    simp [prefixEmpty] at prefixHead
  have suffixLength : 2 ≤ suffixRoute.length := by
    exact retainedTerminalFanFigure7SpokeRouteAt_length_ge_two center slot
  have suffixNonempty : suffixRoute ≠ [] := by
    intro suffixEmpty
    simp [suffixEmpty] at suffixLength
  let target := suffixRoute.getLast suffixNonempty
  have suffixLast : suffixRoute.getLast? = some target :=
    List.getLast?_eq_some_getLast suffixNonempty
  have cycleLast : cycleRoute.getLast? = some target := by
    rw [← suffixLast]
    exact
      (retainedTerminalFanFigure7SpokeRouteAt_getLast?_eq_selectedInnerCycle
        center slot).symm
  have strict : RoutesStrictlyAvoidEachOther prefixRoute cycleRoute := by
    simpa [prefixRoute, cycleRoute, center] using
      retainedAngularFanEscapedSplicedBoundaryRoute_strictlyAvoids_ownInnerCycleRouteAt
        route terminal slot finalPoint
        (.port (angularPortOfIndex slot.val)) ⟨0, by omega⟩
        routeLength classified simple routeFinal routeOrthogonal escapeFits
  unfold retainedAngularFanEscapedSplicedOwnFigure7Route
  apply
    AxisDirection.lastNotInDropLast_unitSubdividePolyline_joinAtEndpoint_of_strictCycle
      prefixNonempty suffixLength
  · simpa [prefixRoute, center, routeLastD] using boundaryValid.2.2
  · exact retainedTerminalFanFigure7SpokeRouteAt_orthogonal center slot
  · exact
      retainedTerminalFanSelectedInnerCycleRouteAt_orthogonal center slot
  · simpa [prefixRoute, center, routeLastD] using boundaryValid.2.1
  · simpa [suffixRoute, center,
      List.getLastD_eq_getLast?, routeFinal] using
      retainedTerminalFanFigure7SpokeRouteAt_head? center slot
  · exact suffixLast
  · exact cycleLast
  · exact strict
  · exact retainedTerminalFanFigure7SpokeRouteAt_isSimple center slot

end PeriodicEightOccurrenceSplit
end LeanTrominoes
