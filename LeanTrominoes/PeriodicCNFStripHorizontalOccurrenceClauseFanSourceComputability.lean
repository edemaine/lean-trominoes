/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability
import LeanTrominoes.PositionedPeriodicCNFComputability

/-! # Computability of the normalized clause-fan source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseSourceComputed_primrec :
    Primrec horizontalOccurrenceClauseSourceComputed := by
  exact PositionedPeriodicCNF.erase_primrec.comp
    (horizontalNormalizedRoutedFormulaComputed_primrec.comp Primrec.fst)

end PeriodicCNFStripReduction
end LeanTrominoes
