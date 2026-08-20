/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorComputability

/-! # Computability of central occurrence ribbon corridors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRibbonCorridorCoreComputed_primrec :
    Primrec horizontalOccurrenceRibbonCorridorCoreComputed := by
  exact ribbonCorridorCore_primrec.comp
    horizontalOccurrenceRibbonCorridorInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
