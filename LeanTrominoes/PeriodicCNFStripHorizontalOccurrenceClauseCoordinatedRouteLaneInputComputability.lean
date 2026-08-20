/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteMetadataComputability

/-! # Computability of clause coordinated-route lane inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRibbonLaneInputComputed_primrec :
    Primrec horizontalOccurrenceRibbonLaneInputComputed := by
  exact Primrec.pair
    (horizontalOccurrenceClauseTerminalGroupComputed_primrec.comp
      Primrec.fst)
    Primrec.snd

end PeriodicCNFStripReduction
end LeanTrominoes
