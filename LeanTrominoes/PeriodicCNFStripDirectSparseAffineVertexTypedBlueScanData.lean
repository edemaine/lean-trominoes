/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedBlueDegreeClassifier

/-! # Typed blue request-scan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

@[simp] theorem horizontalThreeDMBluePositionsComputed_eq_typed_map
    (source : PeriodicCNF Nat) :
    horizontalThreeDMBluePositionsComputed source =
      (horizontalThreeDMBlueElementsComputed source).map
        (horizontalThreeDMBluePositionComputed source) := by
  rfl

def directSparseComputedAffineTypedBlueRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (((horizontalThreeDMBlueElementsComputed source).zipIdx.filter fun tagged =>
      horizontalThreeDMBlueElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source) tagged.1).flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMBluePositionComputed source tagged.1)
        (.monochromaticVertex .blue))

end PeriodicCNFStripReduction
end LeanTrominoes
