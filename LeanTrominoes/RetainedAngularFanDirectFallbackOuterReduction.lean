import LeanTrominoes.RetainedAngularFanDirectSourceCompleteTails
import LeanTrominoes.RetainedAngularFanFinalStrictEscape
import LeanTrominoes.RetainedAngularFanOuterEscapedCompleteSeparation
import LeanTrominoes.RetainedAngularFanOuterCoordinatedSeparation

/-!
# Direct/fallback outer-route reduction

The direct atlas changes only the first 64-block escape of an otherwise
canonical escaped outer route.  Strict angular order separates the canonical
route from an ordinary or escaped fallback.  Consequently the complete
mixed pair reduces to separation of the selected direct escape from the
fallback complete route.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The direct and fallback slots and direction ranks increase in the same
strict orientation. -/
def DirectFallbackStrictAngularOrderCompatible
    (directDirection fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot) : Prop :=
  (directSlot.val < fallbackSlot.val ∧
      directDirection.angularRank < fallbackDirection.angularRank) ∨
    (fallbackSlot.val < directSlot.val ∧
      fallbackDirection.angularRank < directDirection.angularRank)

instance
    (directDirection fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot) :
    Decidable
      (DirectFallbackStrictAngularOrderCompatible
        directDirection fallbackDirection directSlot fallbackSlot) := by
  unfold DirectFallbackStrictAngularOrderCompatible
  infer_instance

/-- Every factor-four direct atlas terminal has a nonempty radial remainder
after its fixed source escape. -/
theorem retainedDirectSourceFanTerminalAt_escape_strict
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    retainedTerminalFanOuterSourceEscapeLength <
      retainedTerminalFanOuterRadialLength
        (retainedDirectSourceFanTerminalAt kind index) := by
  rw [retainedDirectSourceFanTerminalAt_eq_scale]
  exact
    retainedTerminalFanOuterSourceEscape_strictlyFits_scale_four
      (retainedDirectSourceLocalTerminalAt kind index)
      (retainedDirectSourceLocalTerminalAt_length_positive kind index)

/-- Under strict angular order, separation of the selected direct escape
from an ordinary fallback route implies separation of both complete routes. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_ordinaryFallback_of_order_of_escape
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
      0 < retainedTerminalFanOuterRadialLength fallbackTerminal)
    (escapeAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanEscapeAt
          kind index directSlot).route
        (retainedTerminalFanOuterCompleteRoute
          (retainedDirectSourceFanCenterAt kind index)
          fallbackTerminal fallbackSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt
        kind index directSlot)
      (retainedTerminalFanOuterCompleteRoute
        (retainedDirectSourceFanCenterAt kind index)
        fallbackTerminal fallbackSlot) := by
  let center := retainedDirectSourceFanCenterAt kind index
  let directTerminal := retainedDirectSourceFanTerminalAt kind index
  have directLengthPositive : 0 < directTerminal.2 := by
    simpa [directTerminal] using
      retainedDirectSourceFanTerminalAt_length_positive kind index
  have directEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength directTerminal := by
    simpa [directTerminal] using
      retainedDirectSourceFanTerminalAt_escape_strict kind index
  have rasterizedAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          center directTerminal directSlot)
        (retainedTerminalFanOuterCompleteRoute
          center fallbackTerminal fallbackSlot) := by
    rcases angularOrder with
        ⟨slotsLt, directionsLt⟩ |
        ⟨slotsLt, directionsLt⟩
    · exact
        retainedTerminalFanOuterEscapedOrdinaryCompleteRoutes_strictlyAvoid_of_direction_lt
          center directTerminal.1 fallbackTerminal.1
          directTerminal.2 fallbackTerminal.2
          directSlot fallbackSlot directionsLt
          directLengthPositive fallbackLengthPositive
          fallbackRadialPositive slotsLt directEscapeStrict
    · exact
        (retainedTerminalFanOuterOrdinaryEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center fallbackTerminal.1 directTerminal.1
          fallbackTerminal.2 directTerminal.2
          fallbackSlot directSlot directionsLt
          fallbackLengthPositive directLengthPositive
          fallbackRadialPositive slotsLt directEscapeStrict).symm
  simpa [retainedDirectSourceFanCompleteRouteAt,
    center, directTerminal] using
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_strictlyAvoid_of_rasterized_escape_replacement
      center directTerminal directSlot
      (retainedDirectSourceFanEscapeAt kind index directSlot)
      (retainedTerminalFanOuterCompleteRoute
        center fallbackTerminal fallbackSlot)
      rasterizedAvoid
      (by simpa [center] using escapeAvoid)

/-- Under strict angular order, separation of the selected direct escape
from an escaped fallback route implies separation of both complete routes. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoid_escapedFallback_of_order_of_escape
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
        retainedTerminalFanOuterRadialLength fallbackTerminal)
    (escapeAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanEscapeAt
          kind index directSlot).route
        (retainedTerminalFanOuterEscapedCompleteRoute
          (retainedDirectSourceFanCenterAt kind index)
          fallbackTerminal fallbackSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceFanCompleteRouteAt
        kind index directSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        (retainedDirectSourceFanCenterAt kind index)
        fallbackTerminal fallbackSlot) := by
  let center := retainedDirectSourceFanCenterAt kind index
  let directTerminal := retainedDirectSourceFanTerminalAt kind index
  have directLengthPositive : 0 < directTerminal.2 := by
    simpa [directTerminal] using
      retainedDirectSourceFanTerminalAt_length_positive kind index
  have directEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength directTerminal := by
    simpa [directTerminal] using
      retainedDirectSourceFanTerminalAt_escape_strict kind index
  have rasterizedAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          center directTerminal directSlot)
        (retainedTerminalFanOuterEscapedCompleteRoute
          center fallbackTerminal fallbackSlot) := by
    rcases angularOrder with
        ⟨slotsLt, directionsLt⟩ |
        ⟨slotsLt, directionsLt⟩
    · exact
        retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center directTerminal.1 fallbackTerminal.1
          directTerminal.2 fallbackTerminal.2
          directSlot fallbackSlot directionsLt
          directLengthPositive fallbackLengthPositive slotsLt
          directEscapeStrict fallbackEscapeStrict
    · exact
        (retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center fallbackTerminal.1 directTerminal.1
          fallbackTerminal.2 directTerminal.2
          fallbackSlot directSlot directionsLt
          fallbackLengthPositive directLengthPositive slotsLt
          fallbackEscapeStrict directEscapeStrict).symm
  simpa [retainedDirectSourceFanCompleteRouteAt,
    center, directTerminal] using
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_strictlyAvoid_of_rasterized_escape_replacement
      center directTerminal directSlot
      (retainedDirectSourceFanEscapeAt kind index directSlot)
      (retainedTerminalFanOuterEscapedCompleteRoute
        center fallbackTerminal fallbackSlot)
      rasterizedAvoid
      (by simpa [center] using escapeAvoid)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
