/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesQueryComputability

/-! # Computability of the concrete routed incidence family -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq

theorem horizontalRoutedRoutesComputed_eq_query
    (input : (PeriodicCNF Nat × Nat) × Nat) :
    horizontalRoutedRoutesComputed input.1.1 input.1.2 input.2 =
      horizontalRoutedRoutesQuery (horizontalRoutedRoutesInput input) :=
  rfl

theorem horizontalRoutedRoutesComputed_primrec :
    Primrec fun input : (PeriodicCNF Nat × Nat) × Nat =>
      horizontalRoutedRoutesComputed input.1.1 input.1.2 input.2 := by
  exact
    (horizontalRoutedRoutesQuery_primrec.comp
      horizontalRoutedRoutesInput_primrec).of_eq
        horizontalRoutedRoutesComputed_eq_query

end PeriodicCNFStripReduction
end LeanTrominoes
