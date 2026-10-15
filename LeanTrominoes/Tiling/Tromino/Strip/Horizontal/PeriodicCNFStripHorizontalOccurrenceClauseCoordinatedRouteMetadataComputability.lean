/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteEntryInputComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryClauseIndexComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceClauseFanEntryGroupComputability

/-! # Computability of clause coordinated-route metadata -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseIndexComputed_primrec :
    Primrec horizontalOccurrenceClauseIndexComputed := by
  exact horizontalOccurrenceClauseEntryClauseIndexComputed_primrec.comp
    horizontalOccurrenceClauseFanEntryInputComputed_primrec

theorem horizontalOccurrenceClauseTerminalGroupComputed_primrec :
    Primrec horizontalOccurrenceClauseTerminalGroupComputed := by
  exact horizontalOccurrenceClauseEntryGroupComputed_primrec.comp
    horizontalOccurrenceClauseFanEntryInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
