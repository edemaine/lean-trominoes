/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaComputability
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementPeriodComputability
import LeanTrominoes.PositionedPeriodicCNFScalingComputability

/-! # Executable doubled routed formula for the horizontal 3DM assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Routed positioned formula after the padding scale used by the 3DM
assembly. -/
def horizontalPaddedRoutedFormulaComputed (source : PeriodicCNF Nat) :=
  (horizontalRoutedFormulaComputed source).scale 2

/-- Period of the parallel doubled routed placement. -/
def horizontalPaddedRoutedPeriodComputed (source : PeriodicCNF Nat) : Nat :=
  2 * (horizontalRoutedPlacementComputed source).period

theorem horizontalPaddedRoutedFormulaComputed_primrec :
    Primrec horizontalPaddedRoutedFormulaComputed := by
  exact
    (PositionedPeriodicCNF.scale_primrec 2).comp
      horizontalRoutedFormulaComputed_primrec

theorem horizontalPaddedRoutedPeriodComputed_primrec :
    Primrec horizontalPaddedRoutedPeriodComputed := by
  exact
    (Primrec.nat_mul.comp (Primrec.const 2)
      horizontalRoutedPlacementComputed_period_primrec).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
