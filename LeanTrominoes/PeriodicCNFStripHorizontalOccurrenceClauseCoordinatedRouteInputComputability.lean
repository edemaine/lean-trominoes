/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteFanQueryComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteLaneComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanComputability

/-! # Computability of clause coordinated-route table inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseCoordinatedRouteInputComputed_primrec :
    Primrec horizontalOccurrenceClauseCoordinatedRouteInputComputed := by
  exact Primrec.pair
    (horizontalOccurrenceClauseRibbonFanDataComputed_primrec.comp
      horizontalOccurrenceClauseRibbonFanQueryComputed_primrec)
    (Primrec.pair
      (horizontalOccurrenceClauseTerminalGroupComputed_primrec.comp
        Primrec.fst)
      horizontalOccurrenceRibbonLaneComputed_primrec)

end PeriodicCNFStripReduction
end LeanTrominoes
