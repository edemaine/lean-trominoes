/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexRecordSplit

/-! # Modulus-free affine sparse vertex records -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Modulus-free affine data for an original drawing vertex known to lie in
the horizontal fundamental interval. -/
def sparseBoundedInputVertexRecordAssignment
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    Cell × OrthogonalCellType :=
  let position :=
    input.drawing.vertexPosition input.problem.incidenceGraph vertex
  (((1728 * position.1 + 471),
      3456 * (input.drawing.gridSize : Int) -
        (1728 * position.2 + 471)),
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType input vertex)

/-- Horizontal fundamental-square bounds make the affine vertex residue a
literal coordinate, so no runtime remainder operation is needed. -/
theorem sparseInputVertexRecordAssignment_eq_bounded
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex)
    (horizontalNonnegative :
      0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).1)
    (horizontalLt :
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).1 <
        (input.drawing.gridSize : Int)) :
    sparseInputVertexRecordAssignment input vertex =
      sparseBoundedInputVertexRecordAssignment input vertex := by
  rcases positionEq :
      input.drawing.vertexPosition input.problem.incidenceGraph vertex with
    ⟨horizontal, vertical⟩
  have horizontalNonnegative' : 0 ≤ horizontal := by
    simpa [positionEq] using horizontalNonnegative
  have horizontalLt' :
      horizontal < (input.drawing.gridSize : Int) := by
    simpa [positionEq] using horizontalLt
  unfold sparseInputVertexRecordAssignment
    sparseBoundedInputVertexRecordAssignment
  rw [positionEq]
  apply Prod.ext
  · apply Prod.ext
    · exact Int.emod_eq_of_lt (by omega) (by
        push_cast
        omega)
    · push_cast
      ring
  · rfl

/-- Under the same bound, a complete vertex block uses the modulus-free
affine assignment. -/
theorem sparseInputVertexRecordBlock_eq_bounded
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex)
    (horizontalNonnegative :
      0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).1)
    (horizontalLt :
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).1 <
        (input.drawing.gridSize : Int)) :
    sparseInputVertexRecordBlock input vertex =
      GadgetSparseAssignmentTokens.assignmentTokens
        (sparseBoundedInputVertexRecordAssignment input vertex) := by
  unfold sparseInputVertexRecordBlock
  rw [sparseInputVertexRecordAssignment_eq_bounded input vertex
    horizontalNonnegative horizontalLt]

end PeriodicCNFStripReduction
end LeanTrominoes
