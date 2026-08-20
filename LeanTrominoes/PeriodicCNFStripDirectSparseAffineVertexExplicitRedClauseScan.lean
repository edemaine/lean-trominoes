/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexClauseRedScan
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeRedClauseBlock

/-! # Explicit red affine request blocks per clause -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineExplicitRedClauseRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMRedDegreeThreeClauseElementsComputed source).flatMap
    fun element =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMRedPositionComputed source element)
        (.monochromaticVertex .red)

theorem directSparseComputedAffineClauseRedRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineClauseRedRequests source input =
      directSparseComputedAffineExplicitRedClauseRequests source input := by
  unfold directSparseComputedAffineClauseRedRequests
    directSparseComputedAffineExplicitRedClauseRequests
  rw [horizontalThreeDMRedClauseElements_filter_eq_explicit]

theorem directSparseComputedAffineIndexedRedRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .red =
      directSparseComputedAffineExplicitRedClauseRequests source input := by
  rw [directSparseComputedAffineIndexedRedRequests_eq_typed
      source input problemEq,
    directSparseComputedAffineTypedRedRequests_eq_selected,
    directSparseComputedAffineSelectedRedRequests_eq_clause,
    directSparseComputedAffineClauseRedRequests_eq_explicit]

end PeriodicCNFStripReduction
end LeanTrominoes
