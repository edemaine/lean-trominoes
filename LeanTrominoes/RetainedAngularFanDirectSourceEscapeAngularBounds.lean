/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceEscapeSideBounds
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation

/-!
# Angular separator bounds for direct source escapes

The finite direct-source atlas replaces the canonical first 64 blocks of an
escaped radial route.  Under strict direction and slot order, every point of
the replacement remains on the same side of the ordinary radial separator as
the canonical route.  These finite certificates are stated both at the atlas
center and after an arbitrary translation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Finite certificate for a direct escape whose direction and slot precede
the comparison direction and slot. -/
private theorem retainedDirectSourceFanEscapeAt_angular_linear_upper_checked :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (secondDirection : RetainedTerminalDirection),
      ((retainedDirectSourceFanTerminalAt kind index).1.angularRank <
          secondDirection.angularRank ∧
        slot.val < 7) →
      (retainedDirectSourceFanEscapeAt kind index slot).route.all
        (fun point =>
          decide
            (Cell.linearValue
                (retainedTerminalFanOuterRadialSeparatorNormal
                  (retainedDirectSourceFanTerminalAt kind index).1
                  secondDirection)
                point ≤
              Cell.linearValue
                  (retainedTerminalFanOuterRadialSeparatorNormal
                    (retainedDirectSourceFanTerminalAt kind index).1
                    secondDirection)
                  (retainedDirectSourceFanCenterAt kind index) +
                retainedTerminalFanOuterRadialSeparatorBound
                  (retainedDirectSourceFanTerminalAt kind index).1
                  secondDirection)) = true := by
  native_decide

/-- Finite certificate for a direct escape whose direction and slot follow
the comparison direction and slot. -/
private theorem retainedDirectSourceFanEscapeAt_angular_linear_lower_checked :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (firstDirection : RetainedTerminalDirection),
      (firstDirection.angularRank <
          (retainedDirectSourceFanTerminalAt kind index).1.angularRank ∧
        0 < slot.val) →
      (retainedDirectSourceFanEscapeAt kind index slot).route.all
        (fun point =>
          decide
            (Cell.linearValue
                  (retainedTerminalFanOuterRadialSeparatorNormal
                    firstDirection
                    (retainedDirectSourceFanTerminalAt kind index).1)
                  (retainedDirectSourceFanCenterAt kind index) +
                retainedTerminalFanOuterRadialSeparatorBound
                  firstDirection
                  (retainedDirectSourceFanTerminalAt kind index).1 <
              Cell.linearValue
                (retainedTerminalFanOuterRadialSeparatorNormal
                  firstDirection
                  (retainedDirectSourceFanTerminalAt kind index).1)
                point)) = true := by
  native_decide

/-- Every point of an earlier direct escape lies on the weak side of the
ordinary angular separator. -/
theorem retainedDirectSourceFanEscapeAt_angular_linear_upper
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot)
    (secondDirection : RetainedTerminalDirection)
    (directionsLt :
      (retainedDirectSourceFanTerminalAt kind index).1.angularRank <
        secondDirection.angularRank)
    (slotLtSeven : slot.val < 7)
    (point : Cell)
    (pointMember :
      point ∈ (retainedDirectSourceFanEscapeAt kind index slot).route) :
    Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          (retainedDirectSourceFanTerminalAt kind index).1
          secondDirection)
        point ≤
      Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            (retainedDirectSourceFanTerminalAt kind index).1
            secondDirection)
          (retainedDirectSourceFanCenterAt kind index) +
        retainedTerminalFanOuterRadialSeparatorBound
          (retainedDirectSourceFanTerminalAt kind index).1
          secondDirection := by
  have checked :=
    retainedDirectSourceFanEscapeAt_angular_linear_upper_checked
      kind index slot secondDirection ⟨directionsLt, slotLtSeven⟩
  have pointChecked :=
    (List.all_eq_true.mp checked) point pointMember
  exact of_decide_eq_true pointChecked

/-- Every point of a later direct escape lies strictly on the far side of
the ordinary angular separator. -/
theorem retainedDirectSourceFanEscapeAt_angular_linear_lower
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot)
    (firstDirection : RetainedTerminalDirection)
    (directionsLt :
      firstDirection.angularRank <
        (retainedDirectSourceFanTerminalAt kind index).1.angularRank)
    (slotPositive : 0 < slot.val)
    (point : Cell)
    (pointMember :
      point ∈ (retainedDirectSourceFanEscapeAt kind index slot).route) :
    Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            firstDirection
            (retainedDirectSourceFanTerminalAt kind index).1)
          (retainedDirectSourceFanCenterAt kind index) +
        retainedTerminalFanOuterRadialSeparatorBound
          firstDirection
          (retainedDirectSourceFanTerminalAt kind index).1 <
      Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection
          (retainedDirectSourceFanTerminalAt kind index).1)
        point := by
  have checked :=
    retainedDirectSourceFanEscapeAt_angular_linear_lower_checked
      kind index slot firstDirection ⟨directionsLt, slotPositive⟩
  have pointChecked :=
    (List.all_eq_true.mp checked) point pointMember
  exact of_decide_eq_true pointChecked

/-- Translating an earlier direct escape and its center preserves its weak
angular-separator bound. -/
theorem retainedDirectSourceFanEscapeAt_translate_angular_linear_upper
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot)
    (secondDirection : RetainedTerminalDirection)
    (directionsLt :
      (retainedDirectSourceFanTerminalAt kind index).1.angularRank <
        secondDirection.angularRank)
    (slotLtSeven : slot.val < 7)
    (offset point : Cell)
    (pointMember :
      point ∈ translatePolyline offset
        (retainedDirectSourceFanEscapeAt kind index slot).route) :
    Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          (retainedDirectSourceFanTerminalAt kind index).1
          secondDirection)
        point ≤
      Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            (retainedDirectSourceFanTerminalAt kind index).1
            secondDirection)
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index)) +
        retainedTerminalFanOuterRadialSeparatorBound
          (retainedDirectSourceFanTerminalAt kind index).1
          secondDirection := by
  unfold translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨relativePoint, relativePointMember, rfl⟩
  have relativeBound :=
    retainedDirectSourceFanEscapeAt_angular_linear_upper
      kind index slot secondDirection directionsLt slotLtSeven
      relativePoint relativePointMember
  rw [Cell.linearValue_add, Cell.linearValue_add]
  omega

/-- Translating a later direct escape and its center preserves its strict
angular-separator bound. -/
theorem retainedDirectSourceFanEscapeAt_translate_angular_linear_lower
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot)
    (firstDirection : RetainedTerminalDirection)
    (directionsLt :
      firstDirection.angularRank <
        (retainedDirectSourceFanTerminalAt kind index).1.angularRank)
    (slotPositive : 0 < slot.val)
    (offset point : Cell)
    (pointMember :
      point ∈ translatePolyline offset
        (retainedDirectSourceFanEscapeAt kind index slot).route) :
    Cell.linearValue
          (retainedTerminalFanOuterRadialSeparatorNormal
            firstDirection
            (retainedDirectSourceFanTerminalAt kind index).1)
          (Cell.add offset
            (retainedDirectSourceFanCenterAt kind index)) +
        retainedTerminalFanOuterRadialSeparatorBound
          firstDirection
          (retainedDirectSourceFanTerminalAt kind index).1 <
      Cell.linearValue
        (retainedTerminalFanOuterRadialSeparatorNormal
          firstDirection
          (retainedDirectSourceFanTerminalAt kind index).1)
        point := by
  unfold translatePolyline at pointMember
  rw [List.mem_map] at pointMember
  rcases pointMember with ⟨relativePoint, relativePointMember, rfl⟩
  have relativeBound :=
    retainedDirectSourceFanEscapeAt_angular_linear_lower
      kind index slot firstDirection directionsLt slotPositive
      relativePoint relativePointMember
  rw [Cell.linearValue_add, Cell.linearValue_add]
  omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
