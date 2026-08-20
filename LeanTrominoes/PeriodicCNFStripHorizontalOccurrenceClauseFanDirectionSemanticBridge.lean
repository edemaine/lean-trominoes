/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanSelectionSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanProjections

/-! # Semantic correctness of executable clause-fan directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseDirectionComputed_eq_semantic
    (source : PeriodicCNF Nat) (clauseIndex : Nat)
    (group : X3CClauseTerminalGroup) :
    horizontalOccurrenceClauseDirectionComputed
        (source, clauseIndex) group =
      (sourceClauseRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        clauseIndex).direction group := by
  unfold horizontalOccurrenceClauseDirectionComputed
  rw [sourceClauseRibbonFanData_direction_eq]
  rw [horizontalOccurrenceClauseSelectedEntryComputed_eq_semantic]
  generalize selectedEquation :
      (activeClauseOccurrenceEntries
        (horizontalSemanticNormalizedRibbonSource source).erase
        clauseIndex).find? (fun entry =>
          decide
            (occurrenceClauseTerminalGroup
              (horizontalSemanticNormalizedRibbonSource source).erase
              entry = group)) = selected
  cases selected with
  | none => rfl
  | some entry =>
      simp
      exact
        horizontalOccurrenceSourceClauseDirectionComputed_eq_semantic
          source entry

end PeriodicCNFStripReduction
end LeanTrominoes
