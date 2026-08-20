/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedBlueScan

/-! # Index-free selected blue request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def directSparseComputedAffineSelectedBlueRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMBlueElementsComputed source).filter
      (horizontalThreeDMBlueElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source))).flatMap fun element =>
    directSparseComputedAffinePositionRequestRecord
      input.drawing.gridSize
      (horizontalThreeDMBluePositionComputed source element)
      (.monochromaticVertex .blue)

theorem directSparseComputedAffineTypedBlueRequests_eq_selected
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineTypedBlueRequests source input =
      directSparseComputedAffineSelectedBlueRequests source input := by
  unfold directSparseComputedAffineTypedBlueRequests
    directSparseComputedAffineSelectedBlueRequests
  exact IndexedListScan.zipIdx_filter_fst_flatMap
    (horizontalThreeDMBlueElementsComputed source)
    (horizontalThreeDMBlueElementDegreeThree
      (horizontalThreeDMTypedSourceComputed source))
    (fun element =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMBluePositionComputed source element)
        (.monochromaticVertex .blue))

end PeriodicCNFStripReduction
end LeanTrominoes
