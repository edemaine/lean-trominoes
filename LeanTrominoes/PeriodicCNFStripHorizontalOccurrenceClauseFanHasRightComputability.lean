/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSelectedEntryComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseRibbonFanDataEncoding

/-! # Computability of the clause-fan right-terminal flag -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseHasRightComputed_primrec :
    Primrec horizontalOccurrenceClauseHasRightComputed := by
  exact Primrec.option_isSome.comp
    (horizontalOccurrenceClauseSelectedEntryComputed_primrec.comp
      (Primrec.pair Primrec.id
        (Primrec.const X3CClauseTerminalGroup.right)))

end PeriodicCNFStripReduction
end LeanTrominoes
