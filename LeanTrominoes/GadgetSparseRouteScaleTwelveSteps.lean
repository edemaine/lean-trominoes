/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionSteps

/-! # Factor-twelve expansion of unit-subdivision offset words -/

namespace LeanTrominoes
namespace Gadget

/-- Scaling both endpoints by twelve multiplies their Manhattan distance by
twelve. -/
@[simp]
theorem segmentLength_scale_twelve (first second : Cell) :
    AxisDirection.segmentLength (Cell.scale 12 first)
        (Cell.scale 12 second) =
      12 * AxisDirection.segmentLength first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [AxisDirection.segmentLength, Cell.scale]
  have horizontal :
      12 * secondX - 12 * firstX = 12 * (secondX - firstX) := by
    ring
  have vertical :
      12 * secondY - 12 * firstY = 12 * (secondY - firstY) := by
    ring
  rw [horizontal, vertical, Int.natAbs_mul, Int.natAbs_mul]
  norm_num
  omega

/-- Positive factor-twelve scaling preserves the computed cardinal
direction, including the total invalid fallback. -/
@[simp]
theorem between_scale_twelve (first second : Cell) :
    AxisDirection.between (Cell.scale 12 first) (Cell.scale 12 second) =
      AxisDirection.between first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [AxisDirection.between, Cell.scale]
  split_ifs <;> simp_all

/-- Fixed block transduction replacing every offset by twelve copies. -/
def repeatTwelveOffsets (offsets : List Cell) : List Cell :=
  offsets.flatMap fun offset => List.replicate 12 offset

@[simp]
theorem repeatTwelveOffsets_append (first second : List Cell) :
    repeatTwelveOffsets (first ++ second) =
      repeatTwelveOffsets first ++ repeatTwelveOffsets second := by
  simp [repeatTwelveOffsets]

@[simp]
theorem repeatTwelveOffsets_replicate (count : Nat) (offset : Cell) :
    repeatTwelveOffsets (List.replicate count offset) =
      List.replicate (12 * count) offset := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change List.replicate 12 offset ++
          repeatTwelveOffsets (List.replicate count offset) = _
      rw [induction, ← List.replicate_add]
      congr 1
      omega

/-- Subdividing a factor-twelve scaled polyline is the fixed twelve-copy
expansion of the original subdivision-offset word. -/
theorem unitSubdivisionOffsets_scale_twelve (points : List Cell) :
    unitSubdivisionOffsets (scalePolyline 12 points) =
      repeatTwelveOffsets (unitSubdivisionOffsets points) := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [unitSubdivisionOffsets,
      repeatTwelveOffsets]
  | cons_cons first second rest _ induction =>
      simp only [scalePolyline_cons, unitSubdivisionOffsets,
        segmentLength_scale_twelve, between_scale_twelve]
      rw [show unitSubdivisionOffsets
          (Cell.scale 12 second :: scalePolyline 12 rest) =
            repeatTwelveOffsets
              (unitSubdivisionOffsets (second :: rest)) by
        simpa only [scalePolyline_cons] using induction second]
      rw [repeatTwelveOffsets_append,
        repeatTwelveOffsets_replicate]

end Gadget
end LeanTrominoes
