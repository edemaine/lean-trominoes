/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData

/-! # Computability of the concrete routed-placement period -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedPlacementSourceVariableDecidableEq

theorem horizontalRoutedPlacementComputed_period_primrec :
    Primrec fun source : PeriodicCNF Nat =>
      (horizontalRoutedPlacementComputed source).period := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPlacementComputed_period_primrec.comp
      sourceFormula_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
