import LeanTrominoes.OccurrenceSplitAngularFanBoundary
import LeanTrominoes.RetainedAngularTerminalDataScaling

/-!
# Centered geometry of retained angular fan boundaries

The positioned Figure 7 fan occupies the coordinate-radius twelve square
around the uniformly scaled source-variable center.  Its eight boundary
sites are exactly the east-first compass vectors of length twelve.

This file exposes those centered coordinates and proves that every positive
retained terminal gate after the factor-24 refinement lies strictly outside
that square.  Thus an adapter route always runs from a certified exterior
splice point to a distinct boundary site of the local fan.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned

/-- Figure 7's angular boundary site as an offset from the old variable
center. -/
def angularFanBoundaryOffset (index : Nat) : Cell :=
  Cell.sub
    (spokeClausePosition (angularPortOfIndex index))
    (12, 12)

/-- Every valid boundary offset is the length-twelve compass vector selected
by the corresponding east-first angular slot. -/
theorem angularFanBoundaryOffset_eq_scale_unitVector
    {index : Nat} (indexLt : index < 8) :
    angularFanBoundaryOffset index =
      Cell.scale 12
        (angularPortOfIndex index).unitVector := by
  interval_cases index <;>
    native_decide

/-- Each valid Figure 7 boundary site lies in the closed coordinate-radius
twelve square about the old variable center. -/
theorem angularFanBoundaryOffset_within_radius
    {index : Nat} (indexLt : index < 8)
    (center : Cell) :
    WithinCoordinateRadius 12 center
      (Cell.add center
        (angularFanBoundaryOffset index)) := by
  interval_cases index <;>
    simp [WithinCoordinateRadius,
      angularFanBoundaryOffset,
      angularPortOfIndex, spokeClausePosition,
      Cell.add, Cell.sub]

/-- Distinct valid angular indices select distinct centered boundary
sites. -/
theorem angularFanBoundaryOffset_injective_of_lt
    {first second : Nat}
    (firstLt : first < 8)
    (secondLt : second < 8)
    (offsetsEqual :
      angularFanBoundaryOffset first =
        angularFanBoundaryOffset second) :
    first = second := by
  interval_cases first <;>
    interval_cases second <;>
    simp_all [angularFanBoundaryOffset,
      angularPortOfIndex, spokeClausePosition,
      Cell.sub]

/-- The positioned angular boundary is the scaled old variable center plus
its centered Figure 7 offset. -/
theorem angularFanBoundaryPosition_eq_scaledCenter_add_offset
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) :
    angularFanBoundaryPosition
        sourcePlacement atom index =
      Cell.add
        (Cell.scale refinementScale
          (sourcePlacement.position atom))
        (angularFanBoundaryOffset index) := by
  apply Prod.ext <;>
    simp [angularFanBoundaryPosition,
      angularFanBoundaryOffset, macroOrigin,
      refinementScale, spokeClausePosition,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- The periodically translated angular boundary is the scaled old literal
center plus the same local offset. -/
theorem angularFanBoundaryPositionAt_eq_scaledCenter_add_offset
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    angularFanBoundaryPositionAt
        sourcePlacement atom logicalOffset index =
      Cell.add
        (Cell.scale refinementScale
          (Cell.add
            (sourcePlacement.position atom)
            (sourcePlacement.translation
              logicalOffset)))
        (angularFanBoundaryOffset index) := by
  rw [angularFanBoundaryPositionAt,
    angularFanBoundaryPosition_eq_scaledCenter_add_offset]
  apply Prod.ext <;>
    simp [PeriodicVariablePlacement.translation,
    PeriodicEightOccurrenceSplitPositioned.placement,
    refinementScale, Cell.add, Cell.scale] <;>
    ring

/-- A positive retained terminal datum, after the factor-24 Figure 7
refinement, reconstructs a splice point strictly outside the local
coordinate-radius twelve square. -/
theorem scaledRetainedTerminalSplicePoint_outside_fan
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    ¬ WithinCoordinateRadius 12 center
        (retainedTerminalSplicePoint center
          (scaleRetainedTerminalData
            refinementScale.toNat terminal)) := by
  rcases center with ⟨centerX, centerY⟩
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [WithinCoordinateRadius,
          retainedTerminalSplicePoint,
          scaleRetainedTerminalData,
          RetainedTerminalDirection.primitive,
          refinementScale, Port.unitVector,
          Cell.add, Cell.scale] <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [WithinCoordinateRadius,
          retainedTerminalSplicePoint,
          scaleRetainedTerminalData,
          RetainedTerminalDirection.primitive,
          refinementScale, routedClauseRayPrimitive,
          Cell.add, Cell.sub, Cell.scale] <;>
        omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
