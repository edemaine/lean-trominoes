/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedBlueScanPredicate

/-! # Typed blue scan for direct affine vertex requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem directSparseComputedAffineIndexedBlueRequests_eq_typed
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .blue =
      directSparseComputedAffineTypedBlueRequests source input := by
  unfold directSparseComputedAffineIndexedElementRequests
    horizontalThreeDMElementPositionsComputed
    directSparseComputedAffineTypedBlueRequests
  rw [horizontalThreeDMBluePositionsComputed_eq_typed_map, problemEq]
  exact IndexedListScan.map_zipIdx_filter_flatMap_congr
    (horizontalThreeDMBlueElementsComputed source)
    (horizontalThreeDMBluePositionComputed source)
    (fun index => decide
      ((horizontalThreeDMPositionProblemComputed source).degree
        .blue index = 3))
    (horizontalThreeDMBlueElementDegreeThree
      (horizontalThreeDMTypedSourceComputed source))
    (fun position =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize position (.monochromaticVertex .blue))
    (horizontalThreeDMBlueDegreeFilter_eq_typed source)

end PeriodicCNFStripReduction
end LeanTrominoes
