/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDegreeThreeRedClauseBlockPredicate
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceArity
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMSourceOccurrences

/-! # Explicit degree-three red clause scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMRedClauseElements_filter_eq_explicit
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMRedClauseElementsComputed source).filter
        (horizontalThreeDMRedElementDegreeThree
          (horizontalThreeDMTypedSourceComputed source)) =
      horizontalThreeDMRedDegreeThreeClauseElementsComputed source := by
  rw [horizontalThreeDMRedClauseElementsComputed_eq_zipped]
  unfold horizontalThreeDMRedClauseElementsZippedComputed
    horizontalThreeDMRedDegreeThreeClauseElementsComputed
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro tagged taggedMember
  apply horizontalThreeDMRedClauseBlock_filter_of_arity
  · exact horizontalThreeDMTypedSourceComputed_occurrencesAtMostThree source
  · exact (List.mem_zipIdx_iff_getElem?).mp taggedMember
  · exact
      horizontalThreeDMTypedSourceComputed_arityTwoOrThree source
        tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)

end PeriodicCNFStripReduction
end LeanTrominoes
