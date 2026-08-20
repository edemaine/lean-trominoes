/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexClauseBlueScan
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeBlueClauseBlock

/-! # Explicit blue affine request blocks per clause -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineExplicitBlueClauseRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMBlueDegreeThreeClauseElementsComputed source).flatMap
    fun element =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMBluePositionComputed source element)
        (.monochromaticVertex .blue)

theorem directSparseComputedAffineClauseBlueRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineClauseBlueRequests source input =
      directSparseComputedAffineExplicitBlueClauseRequests source input := by
  unfold directSparseComputedAffineClauseBlueRequests
    directSparseComputedAffineExplicitBlueClauseRequests
  rw [horizontalThreeDMBlueClauseElements_filter_eq_explicit]

theorem directSparseComputedAffineIndexedBlueRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .blue =
      directSparseComputedAffineExplicitBlueClauseRequests source input := by
  rw [directSparseComputedAffineIndexedBlueRequests_eq_typed
      source input problemEq,
    directSparseComputedAffineTypedBlueRequests_eq_selected,
    directSparseComputedAffineSelectedBlueRequests_eq_clause,
    directSparseComputedAffineClauseBlueRequests_eq_explicit]

end PeriodicCNFStripReduction
end LeanTrominoes
