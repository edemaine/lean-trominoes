/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMBluePositionListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsData

/-! # Data identification for the assembled blue-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMBluePositionsComputed_eq_data
    (source : PeriodicCNF Nat) :
    horizontalThreeDMBluePositionsComputed source =
      horizontalThreeDMBluePositionsData source := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
