/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedGreenScanPredicate

/-! # Typed green scan for direct affine vertex requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem directSparseComputedAffineIndexedGreenRequests_eq_typed
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .green =
      directSparseComputedAffineTypedGreenRequests source input := by
  unfold directSparseComputedAffineIndexedElementRequests
    horizontalThreeDMElementPositionsComputed
    directSparseComputedAffineTypedGreenRequests
  rw [horizontalThreeDMGreenPositionsComputed_eq_typed_map, problemEq]
  exact IndexedListScan.map_zipIdx_filter_flatMap_congr
    (horizontalThreeDMGreenElementsComputed source)
    (horizontalThreeDMGreenPositionComputed source)
    (fun index => decide
      ((horizontalThreeDMPositionProblemComputed source).degree
        .green index = 3))
    (horizontalThreeDMGreenElementDegreeThree
      (horizontalThreeDMTypedSourceComputed source))
    (fun position =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize position (.monochromaticVertex .green))
    (horizontalThreeDMGreenDegreeFilter_eq_typed source)

end PeriodicCNFStripReduction
end LeanTrominoes
