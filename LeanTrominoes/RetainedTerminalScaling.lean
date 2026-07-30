import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPortGeometry
import LeanTrominoes.RetainedTerminalSplicePoint

/-!
# Scaling classified retained terminal data

The fixed-eight occurrence split refines the retained planar drawing before
replacing each old variable-side tail.  This file records the exact effect of
that positive integral scaling on the finite terminal data:

* the direction and its angular rank do not change;
* the primitive-block length is multiplied by the scale factor; and
* the classified splice point becomes exactly the penultimate point of the
  scaled source route.

These facts isolate the global scaling algebra from the later local annular
adapter construction.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Scale the radial length in retained terminal data without changing its
direction. -/
def scaleRetainedTerminalData
    (factor : Nat)
    (terminal : RetainedTerminalData) :
    RetainedTerminalData :=
  (terminal.1, factor * terminal.2)

@[simp]
theorem scaleRetainedTerminalData_direction
    (factor : Nat)
    (terminal : RetainedTerminalData) :
    (scaleRetainedTerminalData factor terminal).1 =
      terminal.1 :=
  rfl

@[simp]
theorem scaleRetainedTerminalData_length
    (factor : Nat)
    (terminal : RetainedTerminalData) :
    (scaleRetainedTerminalData factor terminal).2 =
      factor * terminal.2 :=
  rfl

@[simp]
theorem scaleRetainedTerminalData_angularRank
    (factor : Nat)
    (terminal : RetainedTerminalData) :
    (scaleRetainedTerminalData
      factor terminal).1.angularRank =
        terminal.1.angularRank :=
  rfl

/-- Positive scaling preserves positivity of a classified radial length. -/
theorem scaleRetainedTerminalData_length_pos
    {factor : Nat} (factorPositive : 0 < factor)
    {terminal : RetainedTerminalData}
    (lengthPositive : 0 < terminal.2) :
    0 < (scaleRetainedTerminalData factor terminal).2 := by
  exact Nat.mul_pos factorPositive lengthPositive

/-- The terminal classifier recognizes every positive multiple of each of
the eleven primitive backwards directions with its exact length. -/
theorem retainedTerminalDirectionClassify_scale_primitive
    (direction : RetainedTerminalDirection)
    {length : Nat} (lengthPositive : 0 < length) :
    retainedTerminalDirectionClassify
        (Cell.scale length direction.primitive) =
      some (direction, length) := by
  have lengthPositiveInt : (0 : Int) < length := by
    exact_mod_cast lengthPositive
  cases direction with
  | compass port =>
      have negated :
          Cell.sub (0, 0)
              (Cell.scale length
                (RetainedTerminalDirection.compass
                  port).primitive) =
            Cell.scale length
              (oppositePort port).unitVector := by
        cases port <;>
          simp [RetainedTerminalDirection.primitive,
            oppositePort,
            OccurrenceSplitRing.Port.unitVector,
            Cell.scale, Cell.sub]
      have terminal :
          terminalPort
              (Cell.scale length
                (oppositePort port).unitVector) =
            some (oppositePort port) :=
        terminalPort_scale_unitVector
          (oppositePort port) lengthPositiveInt
      have exactLength :
          compassLength (oppositePort port)
              (Cell.scale length
                (oppositePort port).unitVector) =
            length := by
        cases port <;>
          simp [oppositePort, compassLength,
            OccurrenceSplitRing.Port.unitVector,
            Cell.scale]
      rw [retainedTerminalDirectionClassify,
        negated]
      simp [retainedRayClassify, terminal,
        exactLength, RetainedRay.terminalDirection,
        RetainedRay.length,
        oppositePort_oppositePort]
  | routedClause arm =>
      have negated :
          Cell.sub (0, 0)
              (Cell.scale length
                (RetainedTerminalDirection.routedClause
                  arm).primitive) =
            Cell.scale length
              (routedClauseRayPrimitive arm) := by
        cases arm <;>
          simp [RetainedTerminalDirection.primitive,
            routedClauseRayPrimitive,
            Cell.scale, Cell.sub]
      have terminal :
          terminalPort
              (Cell.scale length
                (routedClauseRayPrimitive arm)) =
            none := by
        rw [terminalPort_scale lengthPositiveInt]
        cases arm <;> rfl
      have routed :=
        routedClauseRayClassify_scale
          arm lengthPositive
      rw [retainedTerminalDirectionClassify,
        negated]
      simp [retainedRayClassify, terminal, routed,
        RetainedRay.terminalDirection,
        RetainedRay.length]

/-- Scaling a successfully classified terminal vector preserves its
direction and multiplies its exact primitive-block length. -/
theorem retainedTerminalDirectionClassify_scale
    {factor : Nat} (factorPositive : 0 < factor)
    {vector : Cell}
    {terminal : RetainedTerminalData}
    (classified :
      retainedTerminalDirectionClassify vector =
        some terminal) :
    retainedTerminalDirectionClassify
        (Cell.scale factor vector) =
      some (scaleRetainedTerminalData factor terminal) := by
  have sound :=
    retainedTerminalDirectionClassify_sound classified
  have productPositive :
      0 < factor * terminal.2 :=
    Nat.mul_pos factorPositive sound.1
  have scaledVector :
      Cell.scale factor vector =
        Cell.scale (factor * terminal.2)
          terminal.1.primitive := by
    rw [sound.2, Cell.scale_scale]
  rw [scaledVector]
  exact
    retainedTerminalDirectionClassify_scale_primitive
      terminal.1 productPositive

/-- Scaling commutes exactly with reconstruction of a terminal splice
point. -/
theorem retainedTerminalSplicePoint_scale
    (factor : Nat)
    (target : Cell)
    (terminal : RetainedTerminalData) :
    Cell.scale factor
        (retainedTerminalSplicePoint target terminal) =
      retainedTerminalSplicePoint
        (Cell.scale factor target)
        (scaleRetainedTerminalData factor terminal) := by
  rcases target with ⟨targetX, targetY⟩
  rcases terminal.1.primitive with
    ⟨primitiveX, primitiveY⟩
  simp [retainedTerminalSplicePoint,
    scaleRetainedTerminalData, Cell.add, Cell.scale]
  constructor <;> ring

/-- The last point of a scaled route is the scaled last point, including the
total empty-route fallback. -/
@[simp]
theorem scalePolyline_getLastD
    (factor : Nat) (route : List Cell) :
    (scalePolyline factor route).getLastD (0, 0) =
      Cell.scale factor (route.getLastD (0, 0)) := by
  induction route with
  | nil =>
      simp [scalePolyline, Cell.scale]
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [scalePolyline]
      | cons second rest =>
          simpa [scalePolyline] using induction

/-- Exact terminal data for a source route scales to the corresponding exact
data for the scaled route. -/
theorem routeTerminalVector_scale_classified
    {factor : Nat} (factorPositive : 0 < factor)
    {route : List Cell}
    {terminal : RetainedTerminalData}
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal) :
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (scalePolyline factor route)) =
      some
        (scaleRetainedTerminalData
          factor terminal) := by
  rw [routeTerminalVector_scalePolyline]
  exact
    retainedTerminalDirectionClassify_scale
      factorPositive classified

/-- The classified penultimate point of a scaled genuine route is exactly
the scaled source splice point. -/
theorem polylineLastEntrance_scalePolyline_of_classified
    {factor : Nat} (factorPositive : 0 < factor)
    {route : List Cell}
    (routeLength : 2 ≤ route.length)
    {terminal : RetainedTerminalData}
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal) :
    polylineLastEntrance
        (scalePolyline factor route) =
      Cell.scale factor
        (polylineLastEntrance route) := by
  have scaledLength :
      2 ≤ (scalePolyline factor route).length := by
    simpa [scalePolyline] using routeLength
  rw [polylineLastEntrance_eq_retainedTerminalSplicePoint
    routeLength classified]
  rw [polylineLastEntrance_eq_retainedTerminalSplicePoint
    scaledLength
    (routeTerminalVector_scale_classified
      factorPositive classified)]
  rw [scalePolyline_getLastD,
    retainedTerminalSplicePoint_scale]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
