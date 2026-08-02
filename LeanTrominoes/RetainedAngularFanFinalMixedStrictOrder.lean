import LeanTrominoes.RetainedAngularFanDirectFallbackOuterReduction
import LeanTrominoes.RetainedAngularFanFinalMixedOrder

/-!
# Strict angular order of final direct/fallback pairs

The final occurrence ordering gives a weak comparison of terminal-direction
ranks because collinear terminal rays are ordered by a radial tie-break.  If
the direct and fallback directions are different, injectivity of angular rank
upgrades that comparison to the strict order consumed by the outer-route
separation theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Compatible slot and direction order becomes strict when the two terminal
directions are different. -/
theorem
    directFallbackStrictAngularOrderCompatible_of_compatible_of_ne
    (choice : RetainedDirectSourceRouteChoice)
    (fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot)
    (compatible :
      RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
        choice fallbackDirection directSlot fallbackSlot)
    (directionsDifferent :
      (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1 ≠ fallbackDirection) :
    DirectFallbackStrictAngularOrderCompatible
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      fallbackDirection directSlot fallbackSlot := by
  unfold RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible at compatible
  unfold DirectFallbackStrictAngularOrderCompatible
  rcases compatible with
      ⟨slotsLt, ranksLe⟩ |
      ⟨slotsLt, ranksLe⟩
  · exact Or.inl
      ⟨slotsLt,
        Nat.lt_of_le_of_ne ranksLe fun ranksEqual =>
          directionsDifferent
            (RetainedTerminalDirection.angularRank_injective ranksEqual)⟩
  · exact Or.inr
      ⟨slotsLt,
        Nat.lt_of_le_of_ne ranksLe fun ranksEqual =>
          directionsDifferent
            (RetainedTerminalDirection.angularRank_injective ranksEqual.symm)⟩

end PeriodicOrthocrossing
end LeanTrominoes
