/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation
import LeanTrominoes.ScaledPointNeighborhoodSeparation

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

/-- The shifted radial tail after every customized 64-block escape remains
in the ordinary radius-845 transverse corridor. -/
theorem retainedDirectSourceFanShiftedTailAt_transverse_band :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt kind index)
            (retainedDirectSourceFanTerminalAt kind index)
            slot →
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              (retainedDirectSourceFanCenterAt kind index) -
            845 ≤
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
            845 := by
  native_decide

/-- The same shifted radial tails remain in the radius-65 coordinate tube
around their fully refined represented source segments. -/
theorem
    retainedDirectSourceFanShiftedTailAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt kind index)
            (retainedDirectSourceFanTerminalAt kind index)
            slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 65
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 65
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
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

/-- Physical translation preserves the ordinary transverse envelope of every
direct choice's shifted radial tail. -/
theorem
    RetainedDirectSourceRouteChoice.shiftedTail_transverse_band
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index)
            slot)) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          (retainedDirectSourcePositionedFanCenterAt
            choice.origin choice.kind choice.index) -
        845 ≤
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
        845 := by
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectSourceFanShiftedTailAt_transverse_band
      choice.kind choice.index slot localPoint localPointMember
  unfold retainedDirectSourcePositionedFanCenterAt
  simp only [Cell.linearValue_add]
  constructor <;> omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
