/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMColoredPositionsComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMRedPositionsBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMGreenBluePositionsBridge

/-! # Data identification for the colored-element position suffix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMColoredPositionsComputed_eq_data
    (source : PeriodicCNF Nat) :
    horizontalThreeDMColoredPositionsComputed source =
      horizontalThreeDMColoredPositionsData source := by
  unfold horizontalThreeDMColoredPositionsComputed
    horizontalThreeDMColoredPositionsData
  rw [horizontalThreeDMRedPositionsComputed_eq_data,
    horizontalThreeDMGreenBluePositionsComputed_eq_data]

end PeriodicCNFStripReduction
end LeanTrominoes
