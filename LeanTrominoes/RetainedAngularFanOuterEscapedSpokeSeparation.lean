import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation
import LeanTrominoes.RetainedAngularFanOuterEscapedCycleSeparation

/-!
# Escaped outer-fan separation from Figure 7 spokes

The escaped radial route remains weakly outside the radius-288 supporting
side, whereas every Figure 7 spoke lies inside radius 96.  This separates
the radial component; the existing finite local-adapter certificate then
assembles the complete escaped outer route.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A fitting escaped radial route avoids every positioned Figure 7 spoke
at the same fan center. -/
theorem
    retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_figure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedRadialRoute
        center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal terminal.1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal terminal.1)
          center + 96)
      (fun point pointMember => by
        rw [← retainedTerminalFanCenteredFigure7Spoke_map_add]
          at pointMember
        rcases List.mem_map.mp pointMember with
          ⟨offset, offsetMember, rfl⟩
        have upper :=
          retainedTerminalFanCenteredFigure7Spoke_side_upper
            terminal.1 secondSlot offset offsetMember
        rw [Cell.linearValue_add]
        omega)
      (fun point pointMember => by
        have lower :=
          retainedTerminalFanOuterEscapedRadialRoute_side_lower
            center terminal firstSlot lengthPositive escapeFits
            point pointMember
        omega)).symm

/-- A fitting complete escaped outer-fan route avoids every different
Figure 7 spoke at the same fan center. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_strictlyAvoid_otherFigure7SpokeRouteAt
    (center : Cell)
    (terminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterEscapedCompleteRoute
        center terminal firstSlot)
      (retainedTerminalFanFigure7SpokeRouteAt
        center secondSlot) := by
  unfold retainedTerminalFanOuterEscapedCompleteRoute
  exact
    (retainedTerminalFanOuterEscapedRadialRoute_strictlyAvoid_figure7SpokeRouteAt
      center terminal firstSlot secondSlot
      lengthPositive escapeFits).join_left
      (retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_otherFigure7SpokeRouteAt
        center terminal.1 firstSlot secondSlot slotsDifferent)
      (retainedTerminalFanOuterEscapedRadialRoute_getLast?
        center terminal firstSlot lengthPositive escapeFits)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 firstSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
