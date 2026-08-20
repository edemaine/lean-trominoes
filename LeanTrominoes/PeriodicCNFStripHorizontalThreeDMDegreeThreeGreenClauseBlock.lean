/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeGreenClauseBlockPredicate
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceArity
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceOccurrences

/-! # Explicit degree-three green clause scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMGreenClauseElements_filter_eq_explicit
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMGreenClauseElementsComputed source).filter
        (horizontalThreeDMGreenElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) =
      horizontalThreeDMGreenDegreeThreeClauseElementsComputed source := by
  rw [horizontalThreeDMGreenClauseElementsComputed_eq_zipped]
  unfold horizontalThreeDMGreenClauseElementsZippedComputed
    horizontalThreeDMGreenDegreeThreeClauseElementsComputed
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro tagged taggedMember
  apply horizontalThreeDMGreenClauseBlock_filter_of_arity
  · exact horizontalThreeDMTypedSourceComputed_occurrencesAtMostThree source
  · exact (List.mem_zipIdx_iff_getElem?).mp taggedMember
  · exact
      horizontalThreeDMTypedSourceComputed_arityTwoOrThree source
        tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)

end PeriodicCNFStripReduction
end LeanTrominoes
