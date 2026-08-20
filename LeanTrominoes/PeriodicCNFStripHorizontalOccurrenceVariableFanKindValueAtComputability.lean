/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSelectedOccurrenceInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of one variable-fan connector kind -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonKindComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonKindComputed := by
  exact occurrenceConnectorKind_primrec.comp
    horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
