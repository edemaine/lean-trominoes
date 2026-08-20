/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanHasRightComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDirectionCodesListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanDirectionCodesTripleComputability

/-! # Computability of complete clause-fan codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseRibbonFanCodeComputed_primrec :
    Primrec horizontalOccurrenceClauseRibbonFanCodeComputed := by
  exact Primrec.pair horizontalOccurrenceClauseHasRightComputed_primrec
    (horizontalOccurrenceClauseDirectionCodesTriple_primrec.comp
      horizontalOccurrenceClauseDirectionCodesListComputed_primrec)

end PeriodicCNFStripReduction
end LeanTrominoes
