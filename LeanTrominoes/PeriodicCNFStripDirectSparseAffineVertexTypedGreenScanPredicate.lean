/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexTypedGreenScanData

/-! # Predicate agreement for the typed green request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMGreenDegreeFilter_eq_typed
    (source : PeriodicCNF Nat)
    (tagged :
      PeriodicPlanarOneInThreeToThreeDM.GreenElement RoutedVariable × Nat)
    (member : tagged ∈
      (horizontalThreeDMGreenElementsComputed source).zipIdx) :
    decide
        ((horizontalThreeDMPositionProblemComputed source).degree
          .green tagged.2 = 3) =
      horizontalThreeDMGreenElementDegreeThree
        (horizontalThreeDMTypedSourceComputed source) tagged.1 := by
  have elementMember : tagged.1 ∈
      horizontalThreeDMGreenElementsComputed source :=
    List.fst_mem_of_mem_zipIdx member
  have indexEq := IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
    (horizontalThreeDMGreenElementsComputed source)
    (PeriodicPlanarOneInThreeToThreeDM.greenElements_nodup
      (horizontalThreeDMTypedSourceComputed source))
    tagged member
  rw [← indexEq,
    horizontalThreeDMPositionProblemComputed_green_degree_idxOf
      source tagged.1 elementMember]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact horizontalThreeDMGreenElement_degree_eq_three_iff
    (horizontalThreeDMTypedSourceComputed source) tagged.1 elementMember

end PeriodicCNFStripReduction
end LeanTrominoes
