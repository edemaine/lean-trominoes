import LeanTrominoes.RetainedAngularFanBoundaryGeometry
import LeanTrominoes.RetainedAngularTerminalGateDistinctness

/-!
# A common square interface for retained terminal rays

The three exceptional retained clause rays have primitive maximum
coordinates `9`, `4`, and `4`.  Refining the source by `36 = lcm(9,4)`
therefore lets every positive retained terminal segment reach a common
coordinate-radius-36 square before entering the radius-12 Figure 7 fan.

This removes all unbounded radial lengths from the local routing problem:
the inherited part of each route follows its original retained ray from the
scaled splice gate to one of eleven fixed interface points, while the
remaining annular connector is a finite problem.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Primitive-block multiplier that puts one retained direction on the
coordinate-radius-36 interface square. -/
def retainedTerminalInterfaceMultiplier :
    RetainedTerminalDirection → Nat
  | .compass _ => 36
  | .routedClause .left => 4
  | .routedClause .middle => 9
  | .routedClause .right => 9

/-- Fixed centered interface point for one retained direction. -/
def retainedTerminalInterfaceOffset
    (direction : RetainedTerminalDirection) : Cell :=
  Cell.scale
    (retainedTerminalInterfaceMultiplier direction)
    direction.primitive

/-- Number of interface-radius blocks between a scaled splice gate and the
common interface point. -/
def retainedTerminalInterfaceRadialFactor
    (terminal : RetainedTerminalData) : Nat :=
  match terminal.1 with
  | .compass _ => terminal.2
  | .routedClause .left => 9 * terminal.2
  | .routedClause .middle => 4 * terminal.2
  | .routedClause .right => 4 * terminal.2

/-- Every retained interface offset lies exactly on the
coordinate-radius-36 square. -/
theorem retainedTerminalInterfaceOffset_on_square
    (direction : RetainedTerminalDirection) :
    WithinCoordinateRadius 36 (0, 0)
        (retainedTerminalInterfaceOffset direction) ∧
      ¬ WithinCoordinateRadius 35 (0, 0)
        (retainedTerminalInterfaceOffset direction) := by
  cases direction with
  | compass port =>
      cases port <;>
        decide
  | routedClause arm =>
      cases arm <;>
        decide

/-- Different retained directions select different points of the common
interface square. -/
theorem retainedTerminalInterfaceOffset_injective :
    Function.Injective retainedTerminalInterfaceOffset := by
  intro first second equal
  cases first with
  | compass firstPort =>
      cases firstPort <;>
        cases second with
        | compass secondPort =>
            cases secondPort <;>
              simp [retainedTerminalInterfaceOffset,
                retainedTerminalInterfaceMultiplier,
                RetainedTerminalDirection.primitive,
                Port.unitVector, Cell.scale] at equal ⊢
        | routedClause secondArm =>
            cases secondArm <;>
              simp [retainedTerminalInterfaceOffset,
                retainedTerminalInterfaceMultiplier,
                RetainedTerminalDirection.primitive,
                Port.unitVector, routedClauseRayPrimitive,
                Cell.sub, Cell.scale] at equal
  | routedClause firstArm =>
      cases firstArm <;>
        cases second with
        | compass secondPort =>
            cases secondPort <;>
              simp [retainedTerminalInterfaceOffset,
                retainedTerminalInterfaceMultiplier,
                RetainedTerminalDirection.primitive,
                Port.unitVector, routedClauseRayPrimitive,
                Cell.sub, Cell.scale] at equal
        | routedClause secondArm =>
            cases secondArm <;>
              simp [retainedTerminalInterfaceOffset,
                retainedTerminalInterfaceMultiplier,
                RetainedTerminalDirection.primitive,
                routedClauseRayPrimitive,
                Cell.sub, Cell.scale] at equal ⊢

/-- The radial factor from a positive datum to its interface point remains
positive. -/
theorem retainedTerminalInterfaceRadialFactor_pos
    (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    0 < retainedTerminalInterfaceRadialFactor terminal := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      simp [retainedTerminalInterfaceRadialFactor,
        lengthPositive]
  | routedClause arm =>
      cases arm <;>
        simp [retainedTerminalInterfaceRadialFactor,
          lengthPositive]

/-- Scaling a positive terminal datum by the occurrence-split refinement
places its gate at a positive integral multiple of the corresponding fixed
interface offset. -/
theorem scaleRetainedTerminalData_displacement_eq_scale_interface
    (terminal : RetainedTerminalData) :
    Cell.scale
        (scaleRetainedTerminalData
          PeriodicEightOccurrenceSplitPositioned.refinementScale.toNat
          terminal).2
        terminal.1.primitive =
      Cell.scale
        (retainedTerminalInterfaceRadialFactor terminal)
        (retainedTerminalInterfaceOffset terminal.1) := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [scaleRetainedTerminalData,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          Port.unitVector, Cell.scale] <;>
        ring
  | routedClause arm =>
      cases arm <;>
        simp [scaleRetainedTerminalData,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalInterfaceRadialFactor,
          retainedTerminalInterfaceOffset,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive, Cell.sub,
          Cell.scale] <;>
        omega

/-- Positioned form of the radial-interface equality. -/
theorem retainedTerminalSplicePoint_scaled_eq_interface_ray
    (center : Cell) (terminal : RetainedTerminalData) :
    retainedTerminalSplicePoint center
        (scaleRetainedTerminalData
          PeriodicEightOccurrenceSplitPositioned.refinementScale.toNat
          terminal) =
      Cell.add center
        (Cell.scale
          (retainedTerminalInterfaceRadialFactor terminal)
          (retainedTerminalInterfaceOffset terminal.1)) := by
  simp only [retainedTerminalSplicePoint,
    scaleRetainedTerminalData_direction]
  rw [scaleRetainedTerminalData_displacement_eq_scale_interface]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
