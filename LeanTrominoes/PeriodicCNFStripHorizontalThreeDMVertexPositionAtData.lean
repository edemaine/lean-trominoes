/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsComputability

/-! # Pointwise executable horizontal 3DM vertex-position data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- The encoded 3DM problem underlying the computed position lists, stated
without importing any assembled-route data. -/
def horizontalThreeDMPositionProblemComputed
    (source : PeriodicCNF Nat) : PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.encodedProblem
    (horizontalNormalizedRoutedFormulaComputed source).erase

/-- Proof-free pointwise view of the four computed vertex-position lists. -/
def horizontalThreeDMVertexPositionAtComputed
    (source : PeriodicCNF Nat) : PeriodicThreeDMVertex → Cell
  | .triple index =>
      (horizontalThreeDMTriplePositionsComputed source).getD index (0, 0)
  | .element .red atom =>
      (horizontalThreeDMRedPositionsComputed source).getD atom (0, 0)
  | .element .green atom =>
      (horizontalThreeDMGreenPositionsComputed source).getD atom (0, 0)
  | .element .blue atom =>
      (horizontalThreeDMBluePositionsComputed source).getD atom (0, 0)

end PeriodicCNFStripReduction
end LeanTrominoes
