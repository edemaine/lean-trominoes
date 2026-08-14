/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData

/-! # Generic point query used by the concrete routed placement -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedPlacementSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

/-- Query a routed placement before composing it with the guarded source. -/
def horizontalRoutedPlacementQuery
    (input : PeriodicCNF Variable × RoutedVariable) : Cell :=
  (PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPlacementComputed
    input.1).position input.2

theorem horizontalRoutedPlacementQuery_primrec :
    Primrec horizontalRoutedPlacementQuery := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPlacementComputed_position_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
