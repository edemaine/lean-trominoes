/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedRedScanPredicate

/-! # Typed red scan for direct affine vertex requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem directSparseComputedAffineIndexedRedRequests_eq_typed
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (problemEq : input.problem =
      horizontalThreeDMPositionProblemComputed source) :
    directSparseComputedAffineIndexedElementRequests source input .red =
      directSparseComputedAffineTypedRedRequests source input := by
  unfold directSparseComputedAffineIndexedElementRequests
    horizontalThreeDMElementPositionsComputed
    directSparseComputedAffineTypedRedRequests
  rw [horizontalThreeDMRedPositionsComputed_eq_typed_map, problemEq]
  exact IndexedListScan.map_zipIdx_filter_flatMap_congr
    (horizontalThreeDMRedElementsComputed source)
    (horizontalThreeDMRedPositionComputed source)
    (fun index => decide
      ((horizontalThreeDMPositionProblemComputed source).degree
        .red index = 3))
    (horizontalThreeDMRedElementDegreeThree
      (horizontalThreeDMTypedSourceComputed source))
    (fun position =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize position (.monochromaticVertex .red))
    (horizontalThreeDMRedDegreeFilter_eq_typed source)

end PeriodicCNFStripReduction
end LeanTrominoes
