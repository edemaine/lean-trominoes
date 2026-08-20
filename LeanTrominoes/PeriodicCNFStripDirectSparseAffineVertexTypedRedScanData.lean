/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedRedDegreeClassifier

/-! # Typed red request-scan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

@[simp] theorem horizontalThreeDMRedPositionsComputed_eq_typed_map
    (source : PeriodicCNF Nat) :
    horizontalThreeDMRedPositionsComputed source =
      (horizontalThreeDMRedElementsComputed source).map
        (horizontalThreeDMRedPositionComputed source) := by
  rfl

/-- Red requests scanned directly over typed red elements. -/
def directSparseComputedAffineTypedRedRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (((horizontalThreeDMRedElementsComputed source).zipIdx.filter fun tagged =>
      horizontalThreeDMRedElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source) tagged.1).flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize
        (horizontalThreeDMRedPositionComputed source tagged.1)
        (.monochromaticVertex .red))

end PeriodicCNFStripReduction
end LeanTrominoes
