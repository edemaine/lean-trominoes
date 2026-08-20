/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeRedClauseData

/-! # Clause-only red affine request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineClauseRedRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMRedClauseElementsComputed source).filter
      (horizontalThreeDMRedElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source))).flatMap fun element =>
    directSparseComputedAffinePositionRequestRecord
      input.drawing.gridSize
      (horizontalThreeDMRedPositionComputed source element)
      (.monochromaticVertex .red)

theorem directSparseComputedAffineSelectedRedRequests_eq_clause
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineSelectedRedRequests source input =
      directSparseComputedAffineClauseRedRequests source input := by
  unfold directSparseComputedAffineSelectedRedRequests
    directSparseComputedAffineClauseRedRequests
  rw [horizontalThreeDMRedElementDegreeThree_filter_eq_clause]

end PeriodicCNFStripReduction
end LeanTrominoes
