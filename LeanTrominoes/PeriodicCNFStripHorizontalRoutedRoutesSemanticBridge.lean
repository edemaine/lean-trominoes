/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonSemanticData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutesSemanticBridge

/-! # Semantic bridge for horizontal routed incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

theorem horizontalRoutedRoutesComputed_eq_semanticData
    (source : PeriodicCNF Nat) :
    horizontalRoutedRoutesComputed source =
      horizontalSemanticRoutedRoutes source := by
  rw [horizontalSemanticRoutedRoutes,
    horizontalRoutes_eq_finalGaugedIncidenceRoutes]
  exact horizontalRoutedRoutesComputed_eq_semantic source

end PeriodicCNFStripReduction
end LeanTrominoes
