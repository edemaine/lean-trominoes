import LeanTrominoes.RetainedAngularFanDirectSourcePositionedFallbackSeparation
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# Positioned direct separation from scaled fallback terminals

Final fallback routes scale their retained terminal data before constructing
the outer fan.  Scaling preserves its direction.  These wrappers combine
that observation with equality of physical fan centers and expose the exact
ordinary and delayed-lane route shapes used by final mixed assembly.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A positioned direct route avoids an ordinary fallback outer route built
from scaled terminal data at an equal physical center. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_scaledOrdinaryFallbackAt_of_order
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (fallbackCenter : Cell)
    (centersEqual :
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        fallbackCenter)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackRadialPositive :
      0 < retainedTerminalFanOuterRadialLength
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor fallbackTerminal)) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedTerminalFanOuterCompleteRoute
        fallbackCenter
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor fallbackTerminal)
        fallbackSlot) := by
  have scaledOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor fallbackTerminal).1
        directSlot fallbackSlot := by
    simpa only [scaleRetainedTerminalData_direction] using angularOrder
  have scaledLengthPositive :
      0 < (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor fallbackTerminal).2 :=
    scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos fallbackLengthPositive
  have avoid :=
    choice.completeRoute_strictlyAvoids_ordinaryFallbackAt_of_order
      directSlot
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor fallbackTerminal)
      fallbackSlot scaledOrder scaledLengthPositive fallbackRadialPositive
  rw [centersEqual] at avoid
  exact avoid

/-- A positioned direct route avoids a delayed-lane fallback outer route
built from scaled terminal data at an equal physical center. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_scaledEscapedFallbackAt_of_order
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (fallbackCenter : Cell)
    (centersEqual :
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        fallbackCenter)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor fallbackTerminal)) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        fallbackCenter
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor fallbackTerminal)
        fallbackSlot) := by
  have scaledOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor fallbackTerminal).1
        directSlot fallbackSlot := by
    simpa only [scaleRetainedTerminalData_direction] using angularOrder
  have scaledLengthPositive :
      0 < (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor fallbackTerminal).2 :=
    scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos fallbackLengthPositive
  have avoid :=
    choice.completeRoute_strictlyAvoids_escapedFallbackAt_of_order
      directSlot
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor fallbackTerminal)
      fallbackSlot scaledOrder scaledLengthPositive fallbackEscapeStrict
  rw [centersEqual] at avoid
  exact avoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
