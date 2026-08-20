/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleBlockData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseTripleIndex

/-! # Stable indices of horizontal clause triples -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The local set index in a nine-triple clause block gives the advertised
global index after the variable prefix. -/
theorem horizontalThreeDMClauseTriple_mem_zipIdx
    (source : PeriodicCNF Nat)
    (clauseIndex : Nat)
    (clauseIndexLt : clauseIndex <
      (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length)
    (set : X3CClauseSet) (setIndex : Nat)
    (setMember : (set, setIndex) ∈ allClauseSets.zipIdx) :
    (Triple.clause clauseIndex set,
      (horizontalThreeDMVariableTriplesComputed source).length +
        9 * clauseIndex + setIndex) ∈
      (horizontalThreeDMTypedTriplesComputed source).zipIdx := by
  unfold horizontalThreeDMVariableTriplesComputed
    horizontalThreeDMTypedTriplesComputed
  exact clauseTriple_mem_triples_zipIdx
    (horizontalNormalizedRoutedFormulaComputed source).erase
    clauseIndex clauseIndexLt set setIndex setMember

end PeriodicCNFStripReduction
end LeanTrominoes
