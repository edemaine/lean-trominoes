/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotActiveComputability

/-! # Computability of third variable-fan slot activity -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonCountThirdComputed_primrec :
    PrimrecPred fun input : HorizontalVariableRibbonFanInput =>
      (horizontalOccurrenceVariableRibbonLookupComputed
        (input, VariableSiteSlot.third)).isSome :=
  horizontalOccurrenceVariableRibbonSlotActiveComputed_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const VariableSiteSlot.third))

theorem horizontalOccurrenceVariableRibbonCountThirdBoolComputed_primrec :
    Primrec fun input : HorizontalVariableRibbonFanInput =>
      (horizontalOccurrenceVariableRibbonLookupComputed
        (input, VariableSiteSlot.third)).isSome :=
  horizontalOccurrenceVariableRibbonSlotActiveBoolComputed_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const VariableSiteSlot.third))

end PeriodicCNFStripReduction
end LeanTrominoes
