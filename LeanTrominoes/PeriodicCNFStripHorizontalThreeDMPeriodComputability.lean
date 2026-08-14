/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementPeriodComputability

/-! # Executable period of the concrete horizontal 3DM drawing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The three-strand macrocell factor is `128`; padding doubles the routed
placement before the final assembly. -/
def horizontalThreeDMPeriodComputed (source : PeriodicCNF Nat) : Nat :=
  128 * (2 * (horizontalRoutedPlacementComputed source).period)

/-- The grid drawing stores its positive side length as a predecessor. -/
def horizontalThreeDMGridSizePredComputed
    (source : PeriodicCNF Nat) : Nat :=
  horizontalThreeDMPeriodComputed source - 1

theorem horizontalThreeDMPeriodComputed_primrec :
    Primrec horizontalThreeDMPeriodComputed := by
  exact
    (Primrec.nat_mul.comp (Primrec.const 128)
      (Primrec.nat_mul.comp (Primrec.const 2)
        horizontalRoutedPlacementComputed_period_primrec)).of_eq
          fun _ => rfl

theorem horizontalThreeDMGridSizePredComputed_primrec :
    Primrec horizontalThreeDMGridSizePredComputed := by
  exact
    (Primrec.nat_sub.comp horizontalThreeDMPeriodComputed_primrec
      (Primrec.const 1)).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
