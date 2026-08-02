import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation

/-!
# Transverse bounds for direct source routes

The coordinated direct-source atlas changes the first fixed-length escape
of an outer fan but retains the same terminal ray and tail.  This file
records the finite transverse-envelope certificate needed to use a selected
direct route as a bounded replacement for the ordinary outer fan.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Every point of every local coordinated direct-source route lies in a
radius-3103 transverse band around its represented terminal line.  This
coarse certificate includes the unusually wide routed-clause escape. -/
theorem retainedDirectSourceFanCompleteRouteAt_transverse_band :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          retainedDirectSourceFanCompleteRouteAt kind index slot →
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              (retainedDirectSourceFanCenterAt kind index) -
            3103 ≤
          Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ∧
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ≤
          Cell.linearValue
                (retainedTerminalFanOuterTransverseNormal
                  (retainedDirectSourceFanTerminalAt kind index).1)
                (retainedDirectSourceFanCenterAt kind index) +
            3103 := by
  native_decide

/-- Outside the routed-clause component, the finite direct-source atlas has
the much tighter radius-495 transverse envelope. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_transverse_band_of_kind_ne_routedClause :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (_kindNe : kind ≠ .routedClause)
      (point : Cell),
      point ∈
          retainedDirectSourceFanCompleteRouteAt kind index slot →
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              (retainedDirectSourceFanCenterAt kind index) -
            495 ≤
          Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ∧
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ≤
          Cell.linearValue
                (retainedTerminalFanOuterTransverseNormal
                  (retainedDirectSourceFanTerminalAt kind index).1)
                (retainedDirectSourceFanCenterAt kind index) +
            495 := by
  native_decide

/-- Translating a non-routed direct choice into physical component
coordinates preserves its radius-495 transverse envelope. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_transverse_band_of_kind_ne_routedClause
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (kindNe : choice.kind ≠ .routedClause)
    {point : Cell}
    (pointMember : point ∈ choice.completeRoute slot) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          (retainedDirectSourcePositionedFanCenterAt
            choice.origin choice.kind choice.index) -
        495 ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          point ≤
      Cell.linearValue
            (retainedTerminalFanOuterTransverseNormal
              (retainedDirectSourceFanTerminalAt
                choice.kind choice.index).1)
            (retainedDirectSourcePositionedFanCenterAt
              choice.origin choice.kind choice.index) +
        495 := by
  unfold RetainedDirectSourceRouteChoice.completeRoute
    retainedDirectSourcePositionedFanCompleteRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectSourceFanCompleteRouteAt_transverse_band_of_kind_ne_routedClause
      choice.kind choice.index slot kindNe localPoint localPointMember
  unfold retainedDirectSourcePositionedFanCenterAt
  simp only [Cell.linearValue_add]
  constructor <;> omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
