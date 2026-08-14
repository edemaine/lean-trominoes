/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData

/-! # Input adapter for the concrete routed-placement query -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Pair the guarded source formula with the routed variable being queried. -/
def horizontalRoutedPlacementInput
    (input : PeriodicCNF Nat × RoutedVariable) :
    PeriodicCNF Variable × RoutedVariable :=
  (sourceFormula input.1, input.2)

theorem horizontalRoutedPlacementInput_primrec :
    Primrec horizontalRoutedPlacementInput := by
  exact
    (Primrec.pair (sourceFormula_primrec.comp Primrec.fst) Primrec.snd).of_eq
      fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
