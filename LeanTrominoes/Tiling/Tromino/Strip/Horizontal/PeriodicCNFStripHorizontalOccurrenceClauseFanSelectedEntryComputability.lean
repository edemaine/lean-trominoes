/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Compiler.PrimrecListFind
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseFanEntriesComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryMatchesGroupComputability

/-! # Computability of selected clause-fan entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseSelectedEntryComputed_primrec :
    Primrec horizontalOccurrenceClauseSelectedEntryComputed := by
  exact Primrec.list_find?
    (horizontalOccurrenceClauseEntriesComputed_primrec.comp Primrec.fst)
    horizontalOccurrenceClauseEntryMatchesGroupComputed_primrec₂

end PeriodicCNFStripReduction
end LeanTrominoes
