/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceSourceRouteDataBridge
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalSemanticOccurrenceRouteData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedPlacementSemanticBridge
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRoutesSemanticBridge

/-! # Executable-to-semantic occurrence-route data bridge -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The executable occurrence route is the proof-free route instantiated
with the exact semantic ribbon data. -/
theorem horizontalOccurrenceSourceRouteComputed_eq_semanticData
    (input : HorizontalOccurrenceRouteInput) :
    horizontalOccurrenceSourceRouteComputed input =
      horizontalSemanticOccurrenceSourceRouteData input := by
  rw [horizontalOccurrenceSourceRouteComputed_eq_data,
    horizontalNormalizedRoutedFormulaComputed_eq_semanticData,
    horizontalRoutedPlacementComputed_eq_semanticData,
    horizontalRoutedRoutesComputed_eq_semanticData]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes
