/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseTripleIndex

/-! # Lookup of horizontal clause triples at stable indices -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Direct optional lookup at a clause block's advertised global index
returns its named typed triple. -/
theorem horizontalThreeDMClauseTriple_getElem?
    (source : PeriodicCNF Nat)
    (clauseIndex : Nat)
    (clauseIndexLt : clauseIndex <
      (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length)
    (set : X3CClauseSet) (setIndex : Nat)
    (setMember : (set, setIndex) ∈ allClauseSets.zipIdx) :
    (horizontalThreeDMTypedTriplesComputed source)[
      (horizontalThreeDMVariableTriplesComputed source).length +
        9 * clauseIndex + setIndex]? =
      some (.clause clauseIndex set) := by
  unfold horizontalThreeDMTypedTriplesComputed
    horizontalThreeDMVariableTriplesComputed
  exact clauseTriple_getElem?
    (horizontalNormalizedRoutedFormulaComputed source).erase
    clauseIndex clauseIndexLt set setIndex setMember

end PeriodicCNFStripReduction
end LeanTrominoes
