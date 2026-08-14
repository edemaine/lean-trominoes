/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRoutedFormulaComputability
import LeanTrominoes.PeriodicCNFStripSourceFormulaComputability

/-! # Executable routed formula for the concrete strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

local instance horizontalRoutedFormulaSourceVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Proof-free routed positioned formula for a concrete strip source. -/
def horizontalRoutedFormulaComputed (source : PeriodicCNF Nat) :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed
    (sourceFormula source)

theorem horizontalRoutedFormulaComputed_primrec :
    Primrec horizontalRoutedFormulaComputed := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed_primrec.comp
      sourceFormula_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
