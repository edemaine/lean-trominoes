/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryLiteralIndexComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-! # Computability of clause terminal groups at proof-erased entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseEntryGroupComputed_primrec :
    Primrec horizontalOccurrenceClauseEntryGroupComputed := by
  exact terminalGroupOfLiteralIndex_primrec.comp
    horizontalOccurrenceClauseEntryLiteralIndexComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
