/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeGreenClauseData

/-! # Clause-only green affine request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineClauseGreenRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMGreenClauseElementsComputed source).filter
      (horizontalThreeDMGreenElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source))).flatMap fun element =>
    directSparseComputedAffinePositionRequestRecord
      input.drawing.gridSize
      (horizontalThreeDMGreenPositionComputed source element)
      (.monochromaticVertex .green)

theorem directSparseComputedAffineSelectedGreenRequests_eq_clause
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineSelectedGreenRequests source input =
      directSparseComputedAffineClauseGreenRequests source input := by
  unfold directSparseComputedAffineSelectedGreenRequests
    directSparseComputedAffineClauseGreenRequests
  rw [horizontalThreeDMGreenElementDegreeThree_filter_eq_clause]

end PeriodicCNFStripReduction
end LeanTrominoes
