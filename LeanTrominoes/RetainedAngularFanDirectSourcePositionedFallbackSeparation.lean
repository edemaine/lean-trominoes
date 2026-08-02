import LeanTrominoes.RetainedAngularFanOuterRouteTranslation
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanPositionedRoutes

/-!
# Positioned direct/fallback complete-route separation

The local strict-order theorem for a direct atlas entry and a canonical
fallback route transports through the direct choice's physical component
translation.  This is the final-coordinate interface needed by mixed
occurrence assembly.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A positioned direct choice strictly avoids an ordinary fallback complete
route at the same positioned fan center under strict compatible order. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_ordinaryFallbackAt_of_order
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackRadialPositive :
      0 < retainedTerminalFanOuterRadialLength fallbackTerminal) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedTerminalFanOuterCompleteRoute
        (retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index)
        fallbackTerminal fallbackSlot) := by
  have localAvoid :=
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_ordinaryFallback_of_order
      choice.kind choice.index directSlot fallbackTerminal fallbackSlot
      angularOrder fallbackLengthPositive fallbackRadialPositive
  have translated :=
    RoutesStrictlyAvoidEachOther.map_add localAvoid
      (retainedDirectSourceFanPositioningOffset choice.origin)
  change RoutesStrictlyAvoidEachOther
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceFanCompleteRouteAt
          choice.kind choice.index directSlot))
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedTerminalFanOuterCompleteRoute
          (retainedDirectSourceFanCenterAt choice.kind choice.index)
          fallbackTerminal fallbackSlot)) at translated
  rw [retainedTerminalFanOuterCompleteRoute_translatePolyline]
    at translated
  simpa [RetainedDirectSourceRouteChoice.completeRoute,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourcePositionedFanCenterAt] using translated

/-- A positioned direct choice strictly avoids a delayed-lane fallback
complete route at the same positioned fan center under strict compatible
order. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_escapedFallbackAt_of_order
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength fallbackTerminal) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        (retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index)
        fallbackTerminal fallbackSlot) := by
  have localAvoid :=
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_escapedFallback_of_order
      choice.kind choice.index directSlot fallbackTerminal fallbackSlot
      angularOrder fallbackLengthPositive fallbackEscapeStrict
  have translated :=
    RoutesStrictlyAvoidEachOther.map_add localAvoid
      (retainedDirectSourceFanPositioningOffset choice.origin)
  change RoutesStrictlyAvoidEachOther
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceFanCompleteRouteAt
          choice.kind choice.index directSlot))
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedTerminalFanOuterEscapedCompleteRoute
          (retainedDirectSourceFanCenterAt choice.kind choice.index)
          fallbackTerminal fallbackSlot)) at translated
  rw [retainedTerminalFanOuterEscapedCompleteRoute_translatePolyline]
    at translated
  simpa [RetainedDirectSourceRouteChoice.completeRoute,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourcePositionedFanCenterAt] using translated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
