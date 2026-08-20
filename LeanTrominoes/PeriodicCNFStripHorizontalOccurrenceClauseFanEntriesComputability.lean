/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanAllEntriesComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanKeepEntryComputability

/-! # Computability of normalized clause-orbit entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntriesComputed_primrec :
    Primrec horizontalOccurrenceClauseEntriesComputed := by
  exact Primrec.listFilterMap
    horizontalOccurrenceClauseAllEntriesComputed_primrec
    horizontalOccurrenceClauseKeepEntryComputed_primrec₂

end PeriodicCNFStripReduction
end LeanTrominoes
