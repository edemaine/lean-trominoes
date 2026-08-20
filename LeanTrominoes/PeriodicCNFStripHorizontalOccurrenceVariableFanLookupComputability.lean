/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of finite variable-fan occurrence lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonLookupComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonLookupComputed := by
  exact PeriodicPlanarOneInThreeToThreeDM.occurrenceAt_primrec.comp
    horizontalOccurrenceVariableRibbonLookupInput_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
