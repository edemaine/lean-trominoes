import LeanTrominoes.RetainedAngularFanDirectSourceCompleteTails
import LeanTrominoes.RetainedAngularFanOuterRadialPrefixes

/-!
# Exterior side bounds for direct source escapes

The finite direct-source atlas changes the first two primitive blocks of an
escaped radial route.  Every selected 64-block escape nevertheless remains
strictly outside the radius-288 supporting side of its own terminal
direction.  Translation then separates it from every local fan adapter at
the same center, independently of angular order.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The complete finite direct-source escape atlas satisfies the strict
radius-288 exterior-side inequality. -/
private theorem retainedDirectSourceFanEscapeAt_side_strict_lower_checked :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      (retainedDirectSourceFanEscapeAt kind index slot).route.all
        (fun point =>
          decide
            (Cell.linearValue
                  (retainedTerminalFanOuterSideNormal
                    (retainedDirectSourceFanTerminalAt kind index).1)
                  (retainedDirectSourceFanCenterAt kind index) +
                288 <
              Cell.linearValue
                (retainedTerminalFanOuterSideNormal
                  (retainedDirectSourceFanTerminalAt kind index).1)
                point)) = true := by
  native_decide

/-- Every listed point of a selected direct source escape is strictly
outside the radius-288 local fan frame. -/
theorem retainedDirectSourceFanEscapeAt_side_strict_lower
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈
        (retainedDirectSourceFanEscapeAt kind index slot).route) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal
            (retainedDirectSourceFanTerminalAt kind index).1)
          (retainedDirectSourceFanCenterAt kind index) +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal
          (retainedDirectSourceFanTerminalAt kind index).1)
        point := by
  have checked :=
    retainedDirectSourceFanEscapeAt_side_strict_lower_checked
      kind index slot
  have pointChecked :=
    (List.all_eq_true.mp checked) point pointMember
  exact of_decide_eq_true pointChecked

/-- Translating both the escape and its fan center preserves the strict
exterior-side inequality. -/
theorem retainedDirectSourceFanEscapeAt_translate_side_strict_lower
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot)
    (offset : Cell)
    (point : Cell)
    (pointMember :
      point ∈
        translatePolyline offset
          (retainedDirectSourceFanEscapeAt kind index slot).route) :
    Cell.linearValue
          (retainedTerminalFanOuterSideNormal
            (retainedDirectSourceFanTerminalAt kind index).1)
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index)) +
        288 <
      Cell.linearValue
        (retainedTerminalFanOuterSideNormal
          (retainedDirectSourceFanTerminalAt kind index).1)
        point := by
  unfold translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨relativePoint, relativePointMember, rfl⟩
  have relativeBound :=
    retainedDirectSourceFanEscapeAt_side_strict_lower
      kind index slot relativePoint relativePointMember
  rw [Cell.linearValue_add, Cell.linearValue_add]
  omega

/-- A positioned direct source escape strictly avoids every complete local
fan route at its translated center. -/
theorem retainedDirectSourceFanEscapeAt_translate_strictlyAvoid_local
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (escapeSlot localSlot : RetainedTerminalSlot)
    (offset : Cell)
    (localDirection : RetainedTerminalDirection) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline offset
        (retainedDirectSourceFanEscapeAt
          kind index escapeSlot).route)
      (retainedTerminalFanOuterLocalRouteAt
        (Cell.add offset
          (retainedDirectSourceFanCenterAt kind index))
        localDirection localSlot) := by
  exact
    (routesStrictlyAvoidEachOther_of_linear_separated
      (retainedTerminalFanOuterSideNormal
        (retainedDirectSourceFanTerminalAt kind index).1)
      (Cell.linearValue
          (retainedTerminalFanOuterSideNormal
            (retainedDirectSourceFanTerminalAt kind index).1)
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index)) +
        288)
      (retainedTerminalFanOuterLocalRouteAt_side_upper
        (Cell.add offset
          (retainedDirectSourceFanCenterAt kind index))
        (retainedDirectSourceFanTerminalAt kind index).1
        localDirection localSlot)
      (retainedDirectSourceFanEscapeAt_translate_side_strict_lower
        kind index escapeSlot offset)).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
