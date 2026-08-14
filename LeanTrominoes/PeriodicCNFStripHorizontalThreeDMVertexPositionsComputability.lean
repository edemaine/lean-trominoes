/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMColoredPositionsComputability

/-! # Computability of the concrete assembled vertex-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMVertexPositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  horizontalThreeDMTriplePositionsComputed source ++
    horizontalThreeDMColoredPositionsComputed source

theorem horizontalThreeDMVertexPositionsComputed_primrec :
    Primrec horizontalThreeDMVertexPositionsComputed := by
  exact Primrec.list_append.comp
    horizontalThreeDMTriplePositionsComputed_primrec
    horizontalThreeDMColoredPositionsComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
