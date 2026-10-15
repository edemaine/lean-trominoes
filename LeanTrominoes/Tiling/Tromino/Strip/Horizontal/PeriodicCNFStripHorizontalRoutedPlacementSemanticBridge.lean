/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRibbonSemanticData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedPlacementBridge
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutesSemanticBridge

/-! # Semantic bridge for the horizontal routed placement -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

theorem horizontalRoutedPlacementComputed_eq_semanticData
    (source : PeriodicCNF Nat) :
    horizontalRoutedPlacementComputed source =
      horizontalSemanticRoutedPlacement source := by
  rw [horizontalSemanticRoutedPlacement,
    horizontalRoutes_eq_finalGaugedIncidenceRoutes]
  exact horizontalRoutedPlacementComputed_eq_semantic source

end PeriodicCNFStripReduction
end LeanTrominoes
