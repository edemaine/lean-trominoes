/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMEdgeRoutesSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalProblemBridge

/-! # Semantic identification of the executable horizontal 3DM problem -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalThreeDMProblemComputed_eq_problem
    (source : PeriodicCNF Nat) :
    horizontalThreeDMProblemComputed source = problem source := by
  rw [horizontalThreeDMProblemComputed_eq_semantic]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
