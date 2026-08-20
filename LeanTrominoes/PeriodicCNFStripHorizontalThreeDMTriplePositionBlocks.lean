/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleBlockData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionListComputability

/-! # Explicit variable and clause blocks in the horizontal triple positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- Positions of the variable-module triple prefix. -/
def horizontalThreeDMVariableTriplePositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (variableTriples
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (horizontalThreeDMTriplePositionComputed source)

/-- The nine fixed local clause-core positions contributed by each clause. -/
def horizontalThreeDMClauseTriplePositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.zipIdx.flatMap
    fun tagged =>
      allClauseSets.map fun set =>
        Cell.add (horizontalThreeDMClauseOriginComputed source tagged.2)
          (X3CClauseOrthogonal.setPosition set)

theorem horizontalThreeDMClauseTriplePositionComputed_eq
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (set : X3CClauseSet) :
    horizontalThreeDMTriplePositionComputed source
        (.clause clauseIndex set) =
      Cell.add (horizontalThreeDMClauseOriginComputed source clauseIndex)
        (X3CClauseOrthogonal.setPosition set) := by
  rfl

/-- The complete computed position list is the variable-module prefix followed
by nine fixed translated positions per clause. -/
theorem horizontalThreeDMTriplePositionsComputed_eq_blocks
    (source : PeriodicCNF Nat) :
    horizontalThreeDMTriplePositionsComputed source =
      horizontalThreeDMVariableTriplePositionsComputed source ++
        horizontalThreeDMClauseTriplePositionsComputed source := by
  unfold horizontalThreeDMTriplePositionsComputed
    horizontalThreeDMVariableTriplePositionsComputed
    horizontalThreeDMClauseTriplePositionsComputed
    triples
  rw [List.map_append, clauseTriples_eq_zipIdx, List.map_flatMap]
  congr 1

end PeriodicCNFStripReduction
end LeanTrominoes
