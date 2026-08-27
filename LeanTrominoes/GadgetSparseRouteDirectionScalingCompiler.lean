/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections

/-! # Fixed scaling of sparse route direction words

Positive integral scaling preserves the direction of every lattice segment
and multiplies its unary length by the scale factor.  Thus a fixed finite
block transducer compiles the direction word of a scaled polyline without
constructing its coordinates.
-/

noncomputable section

namespace LeanTrominoes
namespace Gadget

open Computability Turing

/-- Scaling both endpoints by a natural factor multiplies their Manhattan
distance by that factor. -/
@[simp] theorem segmentLength_scale
    (factor : Nat) (first second : Cell) :
    AxisDirection.segmentLength (Cell.scale factor first)
        (Cell.scale factor second) =
      factor * AxisDirection.segmentLength first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [AxisDirection.segmentLength, Cell.scale]
  have horizontal :
      (factor : Int) * secondX - (factor : Int) * firstX =
        (factor : Int) * (secondX - firstX) := by
    ring
  have vertical :
      (factor : Int) * secondY - (factor : Int) * firstY =
        (factor : Int) * (secondY - firstY) := by
    ring
  rw [horizontal, vertical, Int.natAbs_mul, Int.natAbs_mul]
  simp [Nat.mul_add]

/-- Positive scaling preserves the computed direction, including the total
fallback on malformed segments. -/
@[simp] theorem between_scale_of_pos
    (factor : Nat) (positive : 0 < factor)
    (first second : Cell) :
    AxisDirection.between (Cell.scale factor first)
        (Cell.scale factor second) =
      AxisDirection.between first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [AxisDirection.between, Cell.scale]
  have factorIntPositive : (0 : Int) < factor := by
    exact_mod_cast positive
  simp only [mul_eq_mul_left_iff]
  split_ifs <;> simp_all

/-- Replace every direction by `factor` consecutive copies. -/
def repeatDirections
    (factor : Nat) (directions : List AxisDirection) :
    List AxisDirection :=
  directions.flatMap fun direction => List.replicate factor direction

@[simp] theorem repeatDirections_append
    (factor : Nat) (first second : List AxisDirection) :
    repeatDirections factor (first ++ second) =
      repeatDirections factor first ++ repeatDirections factor second := by
  simp [repeatDirections]

@[simp] theorem repeatDirections_replicate
    (factor count : Nat) (direction : AxisDirection) :
    repeatDirections factor (List.replicate count direction) =
      List.replicate (factor * count) direction := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change List.replicate factor direction ++
          repeatDirections factor (List.replicate count direction) = _
      rw [induction, ← List.replicate_add]
      congr 1
      simp [Nat.mul_succ, Nat.add_comm]

/-- Consecutive fixed-copy expansions multiply their repetition factors. -/
@[simp] theorem repeatDirections_repeatDirections
    (outer inner : Nat) (directions : List AxisDirection) :
    repeatDirections outer (repeatDirections inner directions) =
      repeatDirections (outer * inner) directions := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change repeatDirections outer
          (List.replicate inner direction ++
            repeatDirections inner directions) =
        List.replicate (outer * inner) direction ++
          repeatDirections (outer * inner) directions
      rw [repeatDirections_append, repeatDirections_replicate,
        induction]

/-- The direction word of a positively scaled polyline is the fixed-copy
expansion of its original direction word. -/
theorem unitSubdivisionDirections_scalePolyline
    (factor : Nat) (positive : 0 < factor) (points : List Cell) :
    unitSubdivisionDirections (scalePolyline factor points) =
      repeatDirections factor (unitSubdivisionDirections points) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [unitSubdivisionDirections, repeatDirections]
  | cons_cons first second rest _ induction =>
      simp only [scalePolyline_cons, unitSubdivisionDirections,
        segmentLength_scale, between_scale_of_pos factor positive]
      rw [show unitSubdivisionDirections
          (Cell.scale factor second :: scalePolyline factor rest) =
            repeatDirections factor
              (unitSubdivisionDirections (second :: rest)) by
        simpa only [scalePolyline_cons] using induction second]
      rw [repeatDirections_append, repeatDirections_replicate]

local instance directionScalingCompilerAxisDirectionInhabited :
    Inhabited AxisDirection := ⟨.invalid⟩

/-- For every fixed factor, direction repetition is polynomial-time. -/
noncomputable def repeatDirectionsComputableInPolyTime
    (factor : Nat) :
    TM2ComputableInPolyTime id id (repeatDirections factor) := by
  change TM2ComputableInPolyTime id id
    (fun directions => directions.flatMap fun direction =>
      List.replicate factor direction)
  exact FiniteBlockTransducer.computableInPolyTime
    (fun direction : AxisDirection => List.replicate factor direction)

end Gadget
end LeanTrominoes

end
