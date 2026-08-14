/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterization
import LeanTrominoes.PeriodicThreeDMNormalizationVertexSeparation

/-!
# Geometric positions in the normalized 3DM strip

The strip uses the reflected vertical coordinate `2P - y` without reducing
it modulo `P`.  Points in strict interior rows may move one unit in any
cardinal direction without wrapping across the strip's vertical seam.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Reflect and vertically shift a geometric point before projection to the
finite strip domain. -/
def stripReflectedLocation (period : Nat) (point : Cell) : Cell :=
  (point.1, 2 * (period : Int) - point.2)

/-- Reflection turns a genuine geometric unit step into the correspondingly
named drawing-grid step. -/
theorem stripReflectedLocation_add_step
    (period : Nat) (point : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    stripReflectedLocation period (Cell.add point direction.step) =
      PeriodicOrthogonalDrawing.latticeNeighbor
        (stripReflectedLocation period point)
        (Side.ofAxisDirection direction) := by
  rcases point with ⟨horizontal, vertical⟩
  cases direction <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.step, Cell.add,
      stripReflectedLocation, Side.ofAxisDirection,
      PeriodicOrthogonalDrawing.latticeNeighbor] <;> omega

/-- Project a geometric point to the finite rectangular strip drawing. -/
def PlanarPresentation.stripPositionAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (point : Cell) :
    presentation.stripNormalizedOrthogonalDrawing.Position :=
  presentation.stripNormalizedOrthogonalDrawing.positionAt
    (stripReflectedLocation presentation.finalNormalizationPeriod point)

/-- Geometric unit steps commute with finite strip projection. -/
theorem PlanarPresentation.stripPositionAt_add_step
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (point : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    presentation.stripPositionAt (Cell.add point direction.step) =
      presentation.stripNormalizedOrthogonalDrawing.neighbor
        (presentation.stripPositionAt point)
        (Side.ofAxisDirection direction) := by
  unfold PlanarPresentation.stripPositionAt
  rw [stripReflectedLocation_add_step _ point genuine]
  exact PeriodicOrthogonalDrawing.positionAt_latticeNeighbor _ _ _

/-- An in-range shifted/reflected point is represented by its unreduced
vertical strip coordinate and its horizontally reduced coordinate. -/
theorem PlanarPresentation.stripPositionAt_values
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (point : Cell)
    (verticalBounds :
      0 ≤ (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 ∧
      (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 <
        (presentation.finalStripHeight : Int)) :
    (((presentation.stripPositionAt point).1.val : Int),
      ((presentation.stripPositionAt point).2.val : Int)) =
        stripRasterLocation presentation.finalNormalizationPeriod point := by
  apply Prod.ext
  · change
      ((PeriodicOrthogonalDrawing.residue point.1
          presentation.stripNormalizedOrthogonalDrawing.horizontalPeriodPred).val :
          Int) = point.1 % presentation.finalNormalizationPeriod
    rw [PeriodicOrthogonalDrawing.residue_val_int]
    have periodEquality :
        (presentation.stripNormalizedOrthogonalDrawing.horizontalPeriodPred : Int) +
            1 = (presentation.finalNormalizationPeriod : Int) := by
      exact_mod_cast presentation.stripNormalizedOrthogonalDrawing_periods.1
    rw [periodEquality]
  · change
      ((PeriodicOrthogonalDrawing.residue
        (stripReflectedLocation presentation.finalNormalizationPeriod point).2
        presentation.stripNormalizedOrthogonalDrawing.verticalPeriodPred).val :
          Int) =
        (stripRasterLocation presentation.finalNormalizationPeriod point).2
    rw [PeriodicOrthogonalDrawing.residue_val_int]
    have periodEquality :
        (presentation.stripNormalizedOrthogonalDrawing.verticalPeriodPred : Int) +
            1 = (presentation.finalStripHeight : Int) := by
      exact_mod_cast presentation.stripNormalizedOrthogonalDrawing_periods.2
    rw [periodEquality]
    rw [Int.emod_eq_of_lt verticalBounds.1 verticalBounds.2]
    rfl

/-- A unit step from a strict interior strip point remains inside the closed
finite row range. -/
theorem stripReflectedLocation_add_side_step_bounds
    (period : Nat) (point : Cell) (side : Side)
    (interior :
      0 < (stripReflectedLocation period point).2 ∧
      (stripReflectedLocation period point).2 < 3 * (period : Int)) :
    0 ≤ (stripReflectedLocation period
        (Cell.add point (axisDirectionOfSide side).step)).2 ∧
      (stripReflectedLocation period
        (Cell.add point (axisDirectionOfSide side).step)).2 <
          (3 * period + 1 : Nat) := by
  rcases point with ⟨horizontal, vertical⟩
  cases side <;>
    simp [stripReflectedLocation, axisDirectionOfSide,
      AxisDirection.step, Cell.add] at interior ⊢ <;> omega

/-- Any finite strip position with the representatives of an in-range
geometric point is that point's canonical strip projection. -/
theorem PlanarPresentation.position_eq_stripPositionAt_of_values_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (position : presentation.stripNormalizedOrthogonalDrawing.Position)
    (point : Cell)
    (verticalBounds :
      0 ≤ (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 ∧
      (stripReflectedLocation
        presentation.finalNormalizationPeriod point).2 <
        (presentation.finalStripHeight : Int))
    (valuesEqual :
      (((position.1.val : Int), (position.2.val : Int))) =
        stripRasterLocation presentation.finalNormalizationPeriod point) :
    position = presentation.stripPositionAt point := by
  have normalizedValues :=
    presentation.stripPositionAt_values point verticalBounds
  have representativesEqual := valuesEqual.trans normalizedValues.symm
  apply Prod.ext
  · apply Fin.ext
    have horizontalEqual :
        (position.1.val : Int) =
          ((presentation.stripPositionAt point).1.val : Int) := by
      simpa using congrArg Prod.fst representativesEqual
    exact_mod_cast horizontalEqual
  · apply Fin.ext
    have verticalEqual :
        (position.2.val : Int) =
          ((presentation.stripPositionAt point).2.val : Int) := by
      simpa using congrArg Prod.snd representativesEqual
    exact_mod_cast verticalEqual

/-- At a strict interior strip assignment, the finite neighbor's stored
representatives equal the strip raster of the corresponding geometric unit
step. -/
theorem PlanarPresentation.stripNeighbor_values_eq_raster_add_side_step
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (position : presentation.stripNormalizedOrthogonalDrawing.Position)
    (point : Cell) (side : Side)
    (interior :
      0 < (stripRasterLocation
        presentation.finalNormalizationPeriod point).2 ∧
      (stripRasterLocation
        presentation.finalNormalizationPeriod point).2 <
          3 * presentation.finalNormalizationPeriod)
    (valuesEqual :
      (((position.1.val : Int), (position.2.val : Int))) =
        stripRasterLocation presentation.finalNormalizationPeriod point) :
    ((((presentation.stripNormalizedOrthogonalDrawing.neighbor
          position side).1.val : Int),
        ((presentation.stripNormalizedOrthogonalDrawing.neighbor
          position side).2.val : Int))) =
      stripRasterLocation presentation.finalNormalizationPeriod
        (Cell.add point (axisDirectionOfSide side).step) := by
  have currentBounds :
      0 ≤ (stripReflectedLocation
          presentation.finalNormalizationPeriod point).2 ∧
        (stripReflectedLocation
          presentation.finalNormalizationPeriod point).2 <
          (presentation.finalStripHeight : Int) := by
    simp only [stripRasterLocation, stripReflectedLocation] at interior ⊢
    unfold PlanarPresentation.finalStripHeight
    constructor <;> omega
  have positionEqual :=
    presentation.position_eq_stripPositionAt_of_values_eq
      position point currentBounds valuesEqual
  have neighborEqual :
      presentation.stripNormalizedOrthogonalDrawing.neighbor position side =
        presentation.stripPositionAt
          (Cell.add point (axisDirectionOfSide side).step) := by
    rw [positionEqual]
    symm
    simpa using presentation.stripPositionAt_add_step point
      (axisDirectionOfSide_isGenuine side)
  have nextBounds := stripReflectedLocation_add_side_step_bounds
    presentation.finalNormalizationPeriod point side (by
      simpa [stripRasterLocation, stripReflectedLocation] using interior)
  have representativesEqual := congrArg
    (fun finitePosition :
        presentation.stripNormalizedOrthogonalDrawing.Position =>
      (((finitePosition.1.val : Int), (finitePosition.2.val : Int))))
    neighborEqual
  exact representativesEqual.trans
    (presentation.stripPositionAt_values
      (Cell.add point (axisDirectionOfSide side).step) (by
        simpa [PlanarPresentation.finalStripHeight] using nextBounds))

end PeriodicThreeDM
end LeanTrominoes
