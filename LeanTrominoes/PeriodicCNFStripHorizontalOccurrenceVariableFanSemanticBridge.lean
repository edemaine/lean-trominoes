/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDataProjections
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanCountSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanKindSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanPolaritySemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionSemanticBridge

/-! # Semantic correctness of executable horizontal variable-fan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceVariableRibbonFanDataComputed
        (source, entry.1.1) =
      sourceVariableRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry := by
  apply variableRibbonFanDataEquivData.injective
  simp [variableRibbonFanDataEquivData,
    variableRibbonFanDataToCode, sourceVariableRibbonFanData,
    horizontalOccurrenceVariableRibbonCountPredComputed_eq_semantic,
    horizontalOccurrenceVariableRibbonKindComputed_eq_semantic,
    horizontalOccurrenceVariableRibbonPolarityComputed_eq_semantic,
    horizontalOccurrenceVariableRibbonDirectionComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
