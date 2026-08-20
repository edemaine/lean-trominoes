/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestTripleIndexed

/-! # Indexed computed-position scans for direct element requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Computed element-position list selected by color. -/
def horizontalThreeDMElementPositionsComputed
    (source : PeriodicCNF Nat) : WireColor → List Cell
  | .red => horizontalThreeDMRedPositionsComputed source
  | .green => horizontalThreeDMGreenPositionsComputed source
  | .blue => horizontalThreeDMBluePositionsComputed source

@[simp] theorem horizontalThreeDMVertexPositionAtComputed_element
    (source : PeriodicCNF Nat) (color : WireColor) (atom : Nat) :
    horizontalThreeDMVertexPositionAtComputed source (.element color atom) =
      (horizontalThreeDMElementPositionsComputed source color).getD
        atom (0, 0) := by
  cases color <;> rfl

@[simp] theorem directSparseComputedAffineElementRequestRecordAt_eq_position
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    directSparseComputedAffineElementRequestRecordAt source input color atom =
      directSparseComputedAffinePositionRequestRecord input.drawing.gridSize
        ((horizontalThreeDMElementPositionsComputed source color).getD
          atom (0, 0))
        (.monochromaticVertex color) := by
  cases color <;> rfl

theorem range_getD_filter_flatMap_eq_zipIdx {Value Output : Type}
    (values : List Value) (default : Value)
    (selected : Nat → Bool)
    (output : Value → Nat → List Output) :
    ((List.range values.length).filter selected).flatMap
        (fun index => output (values.getD index default) index) =
      (values.zipIdx.filter fun tagged => selected tagged.2).flatMap
        fun tagged => output tagged.1 tagged.2 := by
  rw [zipIdx_eq_range_getD values default]
  simp only [List.filter_map, Function.comp_def, List.flatMap_map]

/-- Each lookup-free monochromatic block is a filtered scan of the matching
computed position list, paired with stable atom indices. -/
theorem directSparseComputedAffineElementRequestsAtForColor_eq_zipIdx
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor)
    (problemEq : input.problem = horizontalThreeDMProblemComputed source) :
    ((List.range (input.problem.elementCount color)).filter fun atom =>
        input.problem.degree color atom = 3).flatMap
        (directSparseComputedAffineElementRequestRecordAt
          source input color) =
      ((horizontalThreeDMElementPositionsComputed source color).zipIdx.filter
        fun tagged => input.problem.degree color tagged.2 = 3).flatMap
        fun tagged =>
          directSparseComputedAffinePositionRequestRecord
            input.drawing.gridSize tagged.1 (.monochromaticVertex color) := by
  have positionProblemEq :=
    horizontalThreeDMPositionProblemComputed_eq source
  have lengthEq :
      input.problem.elementCount color =
        (horizontalThreeDMElementPositionsComputed source color).length := by
    rw [problemEq, ← positionProblemEq]
    cases color with
    | red =>
        simpa only [horizontalThreeDMElementPositionsComputed] using
          (horizontalThreeDMRedPositionsComputed_length source).symm
    | green =>
        simpa only [horizontalThreeDMElementPositionsComputed] using
          (horizontalThreeDMGreenPositionsComputed_length source).symm
    | blue =>
        simpa only [horizontalThreeDMElementPositionsComputed] using
          (horizontalThreeDMBluePositionsComputed_length source).symm
  rw [lengthEq]
  have recordEq :
      directSparseComputedAffineElementRequestRecordAt source input color =
        fun atom =>
          directSparseComputedAffinePositionRequestRecord
            input.drawing.gridSize
            ((horizontalThreeDMElementPositionsComputed source color).getD
              atom (0, 0))
            (.monochromaticVertex color) := by
    funext atom
    exact directSparseComputedAffineElementRequestRecordAt_eq_position
      source input color atom
  rw [recordEq]
  exact range_getD_filter_flatMap_eq_zipIdx
    (horizontalThreeDMElementPositionsComputed source color) (0, 0)
    (fun atom => input.problem.degree color atom = 3)
    (fun position _atom =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize position (.monochromaticVertex color))

end PeriodicCNFStripReduction
end LeanTrominoes
