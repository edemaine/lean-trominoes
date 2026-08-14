/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionsBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMColoredPositionsBridge

/-! # Identification of executable and data-only assembled vertex positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMVertexPositionsComputed_eq_data
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVertexPositionsComputed source =
      horizontalThreeDMVertexPositionsData source := by
  unfold horizontalThreeDMVertexPositionsComputed
    horizontalThreeDMVertexPositionsData
  rw [horizontalThreeDMTriplePositionsComputed_eq_data,
    horizontalThreeDMColoredPositionsComputed_eq_data]

end PeriodicCNFStripReduction
end LeanTrominoes
