/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryQueryComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceLookupComputability

/-! # Computability of proof-erased clause-entry lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryLookupComputed_primrec :
    Primrec horizontalOccurrenceClauseEntryLookupComputed := by
  exact horizontalOccurrenceLookupComputed_primrec.comp
    horizontalOccurrenceClauseEntryQueryComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
