/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTripleRequestBlocks
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableCellTypeAt
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableTripleLength
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableTripleMembership

/-! # Typed finite-table variable scan for affine triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRibbonRoutedVariableDecidableEq

/-- Variable-prefix requests scanned through their typed constructors.  The
ordinary and fixed-red constructors select finite local cell tables; the
clause branch is unreachable in the variable prefix. -/
def directSparseComputedAffineTypedTableVariableTripleRequests
    (source : PeriodicCNF Nat) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMVariableTriplesComputed source).zipIdx.flatMap
    fun tagged =>
      match tagged.1 with
      | triple@(.ordinary atom _ _ _) =>
          directSparseComputedAffinePositionRequestRecord
            (horizontalNormalizationInputComputed source).drawing.gridSize
            (horizontalThreeDMTriplePositionComputed source triple)
            (horizontalVariableTripleCellTypeComputed source atom triple)
      | triple@(.fixedRed atom _ _) =>
          directSparseComputedAffinePositionRequestRecord
            (horizontalNormalizationInputComputed source).drawing.gridSize
            (horizontalThreeDMTriplePositionComputed source triple)
            (horizontalVariableTripleCellTypeComputed source atom triple)
      | .clause _ _ => []

/-- At the horizontal normalization input, the canonical variable-prefix
requests are exactly the typed finite-table scan. -/
theorem directSparseComputedAffineVariableTripleRequests_eq_cellTable
    (source : PeriodicCNF Nat) :
    directSparseComputedAffineVariableTripleRequests
        source (horizontalNormalizationInputComputed source) =
      directSparseComputedAffineTypedTableVariableTripleRequests source := by
  unfold directSparseComputedAffineVariableTripleRequests
    directSparseComputedAffineTypedTableVariableTripleRequests
  rw [horizontalThreeDMVariableTriplePositionsComputed_eq_map_typed,
    List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  rintro ⟨triple, tripleIndex⟩ member
  cases triple with
  | ordinary atom slot variant localTriple =>
      simp only [Prod.map, id_eq]
      rw [horizontalFinalOrdinaryVariableTripleCellTypeAtComputed_eq_table
        source tripleIndex atom slot variant localTriple member]
  | fixedRed atom slot localTriple =>
      simp only [Prod.map, id_eq]
      rw [horizontalFinalFixedRedVariableTripleCellTypeAtComputed_eq_table
        source tripleIndex atom slot localTriple member]
  | clause clauseIndex set =>
      have clauseMember : Triple.clause clauseIndex set ∈
          horizontalThreeDMVariableTriplesComputed source :=
        List.fst_mem_of_mem_zipIdx member
      unfold horizontalThreeDMVariableTriplesComputed at clauseMember
      exact (clause_not_mem_variableTriples
        (horizontalNormalizedRoutedFormulaComputed source).erase
        clauseIndex set clauseMember).elim

end PeriodicCNFStripReduction
end LeanTrominoes
