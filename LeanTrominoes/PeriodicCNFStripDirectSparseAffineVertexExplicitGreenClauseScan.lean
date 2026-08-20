/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexClauseGreenScan
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeGreenClauseBlock

/-! # Explicit green affine request blocks per clause -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineExplicitGreenClauseRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMGreenDegreeThreeClauseElementsComputed source).flatMap
    fun element =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMGreenPositionComputed source element)
        (.monochromaticVertex .green)

theorem directSparseComputedAffineClauseGreenRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineClauseGreenRequests source input =
      directSparseComputedAffineExplicitGreenClauseRequests source input := by
  unfold directSparseComputedAffineClauseGreenRequests
    directSparseComputedAffineExplicitGreenClauseRequests
  rw [horizontalThreeDMGreenClauseElements_filter_eq_explicit]

theorem directSparseComputedAffineIndexedGreenRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .green =
      directSparseComputedAffineExplicitGreenClauseRequests source input := by
  rw [directSparseComputedAffineIndexedGreenRequests_eq_typed
      source input problemEq,
    directSparseComputedAffineTypedGreenRequests_eq_selected,
    directSparseComputedAffineSelectedGreenRequests_eq_clause,
    directSparseComputedAffineClauseGreenRequests_eq_explicit]

end PeriodicCNFStripReduction
end LeanTrominoes
