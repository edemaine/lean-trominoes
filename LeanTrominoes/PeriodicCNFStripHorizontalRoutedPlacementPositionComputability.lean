/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementQueryComputability

/-! # Pointwise computability of the concrete routed placement -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedPlacementSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalRoutedPlacementComputed_position_eq_query
    (input : PeriodicCNF Nat × RoutedVariable) :
    (horizontalRoutedPlacementComputed input.1).position input.2 =
      horizontalRoutedPlacementQuery
        (horizontalRoutedPlacementInput input) :=
  rfl

theorem horizontalRoutedPlacementComputed_position_primrec :
    Primrec fun input : PeriodicCNF Nat × RoutedVariable =>
      (horizontalRoutedPlacementComputed input.1).position input.2 := by
  exact
    (horizontalRoutedPlacementQuery_primrec.comp
      horizontalRoutedPlacementInput_primrec).of_eq
        horizontalRoutedPlacementComputed_position_eq_query

end PeriodicCNFStripReduction
end LeanTrominoes
