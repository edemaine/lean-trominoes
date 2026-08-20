/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeBlueClauseData

/-! # Clause-only blue affine request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineClauseBlueRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMBlueClauseElementsComputed source).filter
      (horizontalThreeDMBlueElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source))).flatMap fun element =>
    directSparseComputedAffinePositionRequestRecord
      input.drawing.gridSize
      (horizontalThreeDMBluePositionComputed source element)
      (.monochromaticVertex .blue)

theorem directSparseComputedAffineSelectedBlueRequests_eq_clause
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineSelectedBlueRequests source input =
      directSparseComputedAffineClauseBlueRequests source input := by
  unfold directSparseComputedAffineSelectedBlueRequests
    directSparseComputedAffineClauseBlueRequests
  rw [horizontalThreeDMBlueElementDegreeThree_filter_eq_clause]

end PeriodicCNFStripReduction
end LeanTrominoes
