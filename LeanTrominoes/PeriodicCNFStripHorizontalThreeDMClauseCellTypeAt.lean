/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseCellTypeTable
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseTripleLookup
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleLength
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableTripleLength

/-! # Clause-table cell types at executable stable indices -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- The final cell type at the executable stable index of a clause triple is
the cell type from the finite clause table. -/
theorem horizontalFinalClauseTripleCellTypeAtComputed_eq_table
    (source : PeriodicCNF Nat)
    (clauseIndex : Nat)
    (clauseIndexLt : clauseIndex <
      (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length)
    (set : X3CClauseSet) (setIndex : Nat)
    (setMember : (set, setIndex) ∈ allClauseSets.zipIdx) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple
          ((horizontalThreeDMVariableTriplePositionsComputed source).length +
            9 * clauseIndex + setIndex)) =
      horizontalClauseTripleCellTypeComputed set := by
  have tripleLookup :
      (horizontalThreeDMTypedTriplesComputed source)[
        (horizontalThreeDMVariableTriplePositionsComputed source).length +
          9 * clauseIndex + setIndex]? =
        some (.clause clauseIndex set) := by
    simpa only [horizontalThreeDMVariableTriplePositionsComputed_length] using
      horizontalThreeDMClauseTriple_getElem?
        source clauseIndex clauseIndexLt set setIndex setMember
  have indexLt :
      (horizontalThreeDMVariableTriplePositionsComputed source).length +
          9 * clauseIndex + setIndex <
        (horizontalNormalizationInputComputed source).problem.triples.length := by
    have typedIndexLt := (List.getElem?_eq_some_iff.mp tripleLookup).1
    simpa only [horizontalNormalizationInputComputed_triples_length] using
      typedIndexLt
  exact horizontalFinalClauseTripleCellTypeComputed_eq_table
    source
    ((horizontalThreeDMVariableTriplePositionsComputed source).length +
      9 * clauseIndex + setIndex)
    clauseIndex set indexLt tripleLookup

end PeriodicCNFStripReduction
end LeanTrominoes
