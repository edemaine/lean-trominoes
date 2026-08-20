/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionBlocks
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData

/-! # Variable and clause blocks in the indexed affine triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Indexed affine requests from the variable-module triple-position prefix. -/
def directSparseComputedAffineVariableTripleRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMVariableTriplePositionsComputed source).zipIdx.flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2))

/-- Indexed affine requests from the clause-core triple-position suffix.  Its
stable indices start immediately after the variable-module prefix. -/
def directSparseComputedAffineClauseTripleRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMClauseTriplePositionsComputed source).zipIdx
      (horizontalThreeDMVariableTriplePositionsComputed source).length |>.flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2))

/-- The indexed triple request stream is exactly its variable-module prefix
followed by its clause-core suffix. -/
theorem directSparseComputedAffineIndexedTripleRequests_eq_blocks
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineIndexedTripleRequests source input =
      directSparseComputedAffineVariableTripleRequests source input ++
        directSparseComputedAffineClauseTripleRequests source input := by
  unfold directSparseComputedAffineIndexedTripleRequests
    directSparseComputedAffineVariableTripleRequests
    directSparseComputedAffineClauseTripleRequests
  rw [horizontalThreeDMTriplePositionsComputed_eq_blocks,
    List.zipIdx_append, List.flatMap_append]
  simp only [Nat.zero_add]

end PeriodicCNFStripReduction
end LeanTrominoes
