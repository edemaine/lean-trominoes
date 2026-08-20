/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanData

/-! # Projections of executable variable-fan data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

@[simp]
theorem horizontalOccurrenceVariableRibbonFanDataComputed_countPred
    (input : HorizontalVariableRibbonFanInput) :
    (horizontalOccurrenceVariableRibbonFanDataComputed input).countPred =
      horizontalOccurrenceVariableRibbonCountPredComputed input := by
  simp [horizontalOccurrenceVariableRibbonFanDataComputed,
    horizontalOccurrenceVariableRibbonFanCodeComputed,
    variableRibbonFanDataOfCode]

@[simp]
theorem horizontalOccurrenceVariableRibbonFanDataComputed_kind
    (input : HorizontalVariableRibbonFanInput) (slot : VariableSiteSlot) :
    (horizontalOccurrenceVariableRibbonFanDataComputed input).kind slot =
      horizontalOccurrenceVariableRibbonKindComputed (input, slot) := by
  cases slot <;>
    simp [horizontalOccurrenceVariableRibbonFanDataComputed,
      horizontalOccurrenceVariableRibbonFanCodeComputed,
      horizontalOccurrenceVariableRibbonKindsCodeComputed,
      variableRibbonFanDataOfCode]

@[simp]
theorem horizontalOccurrenceVariableRibbonFanDataComputed_polarity
    (input : HorizontalVariableRibbonFanInput) (slot : VariableSiteSlot) :
    (horizontalOccurrenceVariableRibbonFanDataComputed input).polarity slot =
      horizontalOccurrenceVariableRibbonPolarityComputed (input, slot) := by
  cases slot <;>
    simp [horizontalOccurrenceVariableRibbonFanDataComputed,
      horizontalOccurrenceVariableRibbonFanCodeComputed,
      horizontalOccurrenceVariableRibbonPolaritiesCodeComputed,
      variableRibbonFanDataOfCode]

@[simp]
theorem horizontalOccurrenceVariableRibbonFanDataComputed_direction
    (input : HorizontalVariableRibbonFanInput) (slot : VariableSiteSlot) :
    (horizontalOccurrenceVariableRibbonFanDataComputed input).direction slot =
      horizontalOccurrenceVariableRibbonDirectionComputed input slot := by
  cases slot <;>
    simp [horizontalOccurrenceVariableRibbonFanDataComputed,
      horizontalOccurrenceVariableRibbonFanCodeComputed,
      horizontalOccurrenceVariableRibbonDirectionsCodeComputed,
      horizontalOccurrenceVariableRibbonDirectionCodesTriple,
      horizontalOccurrenceVariableRibbonDirectionCodesListComputed,
      variableRibbonFanDataOfCode]

end PeriodicCNFStripReduction
end LeanTrominoes
