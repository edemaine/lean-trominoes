/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge

/-! # Semantic bridge for variable-fan occurrence lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableSourceComputed_eq_semantic
    (source : PeriodicCNF Nat) (atom : RoutedVariable) :
    horizontalOccurrenceVariableSourceComputed (source, atom) =
      (horizontalSemanticNormalizedRibbonSource source).erase := by
  exact horizontalNormalizedRoutedEraseComputed_eq_semanticData source

theorem horizontalOccurrenceVariableRibbonLookupComputed_eq_semantic
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : VariableSiteSlot) :
    horizontalOccurrenceVariableRibbonLookupComputed
        ((source, atom), slot) =
      occurrenceAt
        (horizontalSemanticNormalizedRibbonSource source).erase atom
        (variableSiteOccurrenceSlot slot) := by
  unfold horizontalOccurrenceVariableRibbonLookupComputed
    horizontalOccurrenceVariableRibbonLookupInput
  rw [horizontalOccurrenceVariableSourceComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
