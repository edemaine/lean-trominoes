/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData

/-! # Projections of executable horizontal clause-fan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

@[simp]
theorem horizontalOccurrenceClauseRibbonFanDataComputed_hasRight
    (input : HorizontalClauseRibbonFanInput) :
    (horizontalOccurrenceClauseRibbonFanDataComputed input).hasRight =
      horizontalOccurrenceClauseHasRightComputed input := by
  simp [horizontalOccurrenceClauseRibbonFanDataComputed,
    horizontalOccurrenceClauseRibbonFanCodeComputed,
    horizontalOccurrenceClauseRibbonFanDataOfCode]

@[simp]
theorem horizontalOccurrenceClauseRibbonFanDataComputed_direction
    (input : HorizontalClauseRibbonFanInput)
    (group : X3CClauseTerminalGroup) :
    (horizontalOccurrenceClauseRibbonFanDataComputed input).direction group =
      horizontalOccurrenceClauseDirectionComputed input group := by
  cases group <;>
    simp [horizontalOccurrenceClauseRibbonFanDataComputed,
      horizontalOccurrenceClauseRibbonFanCodeComputed,
      horizontalOccurrenceClauseRibbonFanDataOfCode,
      horizontalOccurrenceClauseDirectionCodesTriple,
      horizontalOccurrenceClauseDirectionCodesListComputed]

end PeriodicCNFStripReduction
end LeanTrominoes
