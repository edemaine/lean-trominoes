/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsData

/-! # Data identification for the assembled triple-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMTriplePositionsComputed_eq_data
    (source : PeriodicCNF Nat) :
    horizontalThreeDMTriplePositionsComputed source =
      horizontalThreeDMTriplePositionsData source := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
