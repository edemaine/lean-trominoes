/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalThreeDMGreenBluePositionsComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalThreeDMGreenPositionsBridge
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalThreeDMBluePositionsBridge

/-! # Data identification for the green-and-blue position suffix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMGreenBluePositionsComputed_eq_data
    (source : PeriodicCNF Nat) :
    horizontalThreeDMGreenBluePositionsComputed source =
      horizontalThreeDMGreenBluePositionsData source := by
  unfold horizontalThreeDMGreenBluePositionsComputed
    horizontalThreeDMGreenBluePositionsData
  rw [horizontalThreeDMGreenPositionsComputed_eq_data,
    horizontalThreeDMBluePositionsComputed_eq_data]

end PeriodicCNFStripReduction
end LeanTrominoes
