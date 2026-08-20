/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedGreenScan

/-! # Index-free selected green request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineSelectedGreenRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMGreenElementsComputed source).filter
      (horizontalThreeDMGreenElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source))).flatMap fun element =>
    directSparseComputedAffinePositionRequestRecord
      input.drawing.gridSize
      (horizontalThreeDMGreenPositionComputed source element)
      (.monochromaticVertex .green)

theorem directSparseComputedAffineTypedGreenRequests_eq_selected
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineTypedGreenRequests source input =
      directSparseComputedAffineSelectedGreenRequests source input := by
  unfold directSparseComputedAffineTypedGreenRequests
    directSparseComputedAffineSelectedGreenRequests
  exact IndexedListScan.zipIdx_filter_fst_flatMap
    (horizontalThreeDMGreenElementsComputed source)
    (horizontalThreeDMGreenElementDegreeThree
      (horizontalThreeDMTypedSourceComputed source))
    (fun element =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMGreenPositionComputed source element)
        (.monochromaticVertex .green))

end PeriodicCNFStripReduction
end LeanTrominoes
