/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceVariableFanKindCodeComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceVariableFanPolarityCodeComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceVariableFanDirectionCodeComputability
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalOccurrenceVariableFanCountComputability

/-! # Computability of the complete variable-fan code -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonFanCodeComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonFanCodeComputed := by
  exact Primrec.pair
    horizontalOccurrenceVariableRibbonCountPredComputed_primrec
    (Primrec.pair
      horizontalOccurrenceVariableRibbonKindsCodeComputed_primrec
      (Primrec.pair
        horizontalOccurrenceVariableRibbonPolaritiesCodeComputed_primrec
        horizontalOccurrenceVariableRibbonDirectionsCodeComputed_primrec))

end PeriodicCNFStripReduction
end LeanTrominoes
