/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedGreenDegreeClassifier

/-! # Typed green request-scan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

@[simp] theorem horizontalThreeDMGreenPositionsComputed_eq_typed_map
    (source : PeriodicCNF Nat) :
    horizontalThreeDMGreenPositionsComputed source =
      (horizontalThreeDMGreenElementsComputed source).map
        (horizontalThreeDMGreenPositionComputed source) := by
  rfl

def directSparseComputedAffineTypedGreenRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (((horizontalThreeDMGreenElementsComputed source).zipIdx.filter fun tagged =>
      horizontalThreeDMGreenElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source) tagged.1).flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMGreenPositionComputed source tagged.1)
        (.monochromaticVertex .green))

end PeriodicCNFStripReduction
end LeanTrominoes
