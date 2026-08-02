import LeanTrominoes.RetainedAngularFanDirectSourceEscapeRadialSeparation

/-!
# Complete direct/fallback outer-route separation

The custom direct escape avoids both pieces of a fallback complete route:
angular separator bounds handle its radial piece, while the exterior-side
bound handles its local fan adapter.  Joining those pieces closes the escape
obligation in the direct-tail replacement reduction, for ordinary and
delayed-lane fallbacks alike.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A translated custom direct escape strictly avoids an ordinary fallback
complete route under strict compatible angular order. -/
theorem
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_ordinaryComplete_of_order
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (offset : Cell)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt kind index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline offset
        (retainedDirectSourceFanEscapeAt kind index directSlot).route)
      (retainedTerminalFanOuterCompleteRoute
        (Cell.add offset
          (retainedDirectSourceFanCenterAt kind index))
        fallbackTerminal fallbackSlot) := by
  have radialAvoid :=
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_ordinaryRadial_of_order
      kind index directSlot fallbackTerminal fallbackSlot offset
      angularOrder fallbackLengthPositive
  have localAvoid :=
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_local
      kind index directSlot fallbackSlot offset fallbackTerminal.1
  unfold retainedTerminalFanOuterCompleteRoute
  exact radialAvoid.join_right localAvoid
    (retainedTerminalFanOuterRadialRoute_getLast?
      (Cell.add offset
        (retainedDirectSourceFanCenterAt kind index))
      fallbackTerminal fallbackSlot fallbackLengthPositive)
    (retainedTerminalFanOuterLocalRouteAt_head?
      (Cell.add offset
        (retainedDirectSourceFanCenterAt kind index))
      fallbackTerminal.1 fallbackSlot)

/-- A translated custom direct escape strictly avoids a delayed-lane
fallback complete route under strict compatible angular order. -/
theorem
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_escapedComplete_of_order
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (offset : Cell)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt kind index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength fallbackTerminal) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline offset
        (retainedDirectSourceFanEscapeAt kind index directSlot).route)
      (retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.add offset
          (retainedDirectSourceFanCenterAt kind index))
        fallbackTerminal fallbackSlot) := by
  have radialAvoid :=
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_escapedRadial_of_order
      kind index directSlot fallbackTerminal fallbackSlot offset
      angularOrder fallbackLengthPositive fallbackEscapeFits
  have localAvoid :=
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_local
      kind index directSlot fallbackSlot offset fallbackTerminal.1
  unfold retainedTerminalFanOuterEscapedCompleteRoute
  exact radialAvoid.join_right localAvoid
    (retainedTerminalFanOuterEscapedRadialRoute_getLast?
      (Cell.add offset
        (retainedDirectSourceFanCenterAt kind index))
      fallbackTerminal fallbackSlot fallbackLengthPositive
      fallbackEscapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      (Cell.add offset
        (retainedDirectSourceFanCenterAt kind index))
      fallbackTerminal.1 fallbackSlot)

/-- Strict compatible angular order automatically separates a complete
custom direct outer route from an ordinary fallback complete route. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_ordinaryFallback_of_order
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt kind index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackRadialPositive :
      0 < retainedTerminalFanOuterRadialLength fallbackTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt
        kind index directSlot)
      (retainedTerminalFanOuterCompleteRoute
        (retainedDirectSourceFanCenterAt kind index)
        fallbackTerminal fallbackSlot) := by
  apply
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_ordinaryFallback_of_order_of_escape
      kind index directSlot fallbackTerminal fallbackSlot angularOrder
      fallbackLengthPositive fallbackRadialPositive
  simpa [Cell.add] using
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_ordinaryComplete_of_order
      kind index directSlot fallbackTerminal fallbackSlot (0, 0)
      angularOrder fallbackLengthPositive

/-- Strict compatible angular order automatically separates a complete
custom direct outer route from a delayed-lane fallback complete route. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_escapedFallback_of_order
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (directSlot : RetainedTerminalSlot)
    (fallbackTerminal : RetainedTerminalData)
    (fallbackSlot : RetainedTerminalSlot)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt kind index).1
        fallbackTerminal.1 directSlot fallbackSlot)
    (fallbackLengthPositive : 0 < fallbackTerminal.2)
    (fallbackEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength fallbackTerminal) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt
        kind index directSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        (retainedDirectSourceFanCenterAt kind index)
        fallbackTerminal fallbackSlot) := by
  apply
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_escapedFallback_of_order_of_escape
      kind index directSlot fallbackTerminal fallbackSlot angularOrder
      fallbackLengthPositive fallbackEscapeStrict
  simpa [Cell.add] using
    retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_escapedComplete_of_order
      kind index directSlot fallbackTerminal fallbackSlot (0, 0)
      angularOrder fallbackLengthPositive (Nat.le_of_lt fallbackEscapeStrict)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
