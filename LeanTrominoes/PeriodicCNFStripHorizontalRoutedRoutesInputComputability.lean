/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesData

/-! # Input adapter for the concrete routed-incidence query -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Replace the concrete source by its guarded formula while retaining the
two incidence indices. -/
def horizontalRoutedRoutesInput
    (input : (PeriodicCNF Nat × Nat) × Nat) :
    (PeriodicCNF Variable × Nat) × Nat :=
  ((sourceFormula input.1.1, input.1.2), input.2)

theorem horizontalRoutedRoutesInput_primrec :
    Primrec horizontalRoutedRoutesInput := by
  exact
    (Primrec.pair
      (Primrec.pair
        (sourceFormula_primrec.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
