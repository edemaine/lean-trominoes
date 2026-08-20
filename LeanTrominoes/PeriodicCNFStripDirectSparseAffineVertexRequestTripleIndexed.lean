/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestPositionSplit

/-! # Indexed computed-position scan for direct triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Compact affine request from an already selected computed position. -/
def directSparseComputedAffinePositionRequestRecord
    (gridSize : Nat) (position : Cell)
    (cellType : Gadget.OrthogonalCellType) :
    List GadgetSparseAffineVertexTokens.Token :=
  GadgetSparseAffineVertexTokens.record position.1.toNat
    (2 * gridSize - position.2.toNat - 1) cellType

@[simp] theorem directSparseComputedAffineVertexRequestRecordAt_triple
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (index : Nat) :
    directSparseComputedAffineVertexRequestRecordAt source input
        (.triple index) =
      directSparseComputedAffinePositionRequestRecord input.drawing.gridSize
        ((horizontalThreeDMTriplePositionsComputed source).getD
          index (0, 0))
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple index)) := by
  rfl

theorem zipIdx_eq_range_getD {Value : Type}
    (values : List Value) (default : Value) :
    values.zipIdx =
      (List.range values.length).map fun index =>
        (values.getD index default, index) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    have indexLt : index < values.length := by
      simpa using leftBound
    simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ indexLt]
    simp only [Nat.zero_add]

theorem range_getD_flatMap_eq_zipIdx {Value Output : Type}
    (values : List Value) (default : Value)
    (output : Value → Nat → List Output) :
    (List.range values.length).flatMap
        (fun index => output (values.getD index default) index) =
      values.zipIdx.flatMap fun tagged => output tagged.1 tagged.2 := by
  rw [zipIdx_eq_range_getD]
  rw [List.flatMap_map]

/-- The lookup-free triple block is a direct scan of computed positions paired
with their stable triple indices. -/
theorem directSparseComputedAffineTripleRequestsAt_eq_zipIdx
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem = horizontalThreeDMProblemComputed source) :
    input.problem.tripleVertices.flatMap
        (directSparseComputedAffineVertexRequestRecordAt source input) =
      (horizontalThreeDMTriplePositionsComputed source).zipIdx.flatMap
        fun tagged =>
          directSparseComputedAffinePositionRequestRecord
            input.drawing.gridSize tagged.1
            (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
              input (.triple tagged.2)) := by
  have positionProblemEq :=
    horizontalThreeDMPositionProblemComputed_eq source
  have lengthEq :
      input.problem.triples.length =
        (horizontalThreeDMTriplePositionsComputed source).length := by
    rw [problemEq, ← positionProblemEq]
    exact (horizontalThreeDMTriplePositionsComputed_length source).symm
  unfold PeriodicThreeDM.tripleVertices
  rw [List.flatMap_map, lengthEq]
  simp only [directSparseComputedAffineVertexRequestRecordAt_triple]
  exact range_getD_flatMap_eq_zipIdx
    (horizontalThreeDMTriplePositionsComputed source) (0, 0)
    (fun position index =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize position
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple index)))

end PeriodicCNFStripReduction
end LeanTrominoes
