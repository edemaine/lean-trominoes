/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedRedScan

/-! # Index-free selected red request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineSelectedRedRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMRedElementsComputed source).filter
      (horizontalThreeDMRedElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source))).flatMap fun element =>
    directSparseComputedAffinePositionRequestRecord
      input.drawing.gridSize
      (horizontalThreeDMRedPositionComputed source element)
      (.monochromaticVertex .red)

theorem directSparseComputedAffineTypedRedRequests_eq_selected
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineTypedRedRequests source input =
      directSparseComputedAffineSelectedRedRequests source input := by
  unfold directSparseComputedAffineTypedRedRequests
    directSparseComputedAffineSelectedRedRequests
  exact IndexedListScan.zipIdx_filter_fst_flatMap
    (horizontalThreeDMRedElementsComputed source)
    (horizontalThreeDMRedElementDegreeThree
      (horizontalThreeDMTypedSourceComputed source))
    (fun element =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMRedPositionComputed source element)
        (.monochromaticVertex .red))

end PeriodicCNFStripReduction
end LeanTrominoes
