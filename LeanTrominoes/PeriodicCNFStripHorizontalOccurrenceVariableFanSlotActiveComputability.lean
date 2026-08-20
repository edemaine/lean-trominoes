/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanLookupComputability

/-! # Computability of variable-fan slot activity -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonSlotActiveBoolComputed_primrec :
    Primrec fun input :
        HorizontalVariableRibbonFanInput × VariableSiteSlot =>
      (horizontalOccurrenceVariableRibbonLookupComputed input).isSome :=
  Primrec.option_isSome.comp
    horizontalOccurrenceVariableRibbonLookupComputed_primrec

theorem horizontalOccurrenceVariableRibbonSlotActiveComputed_primrec :
    PrimrecPred fun input :
        HorizontalVariableRibbonFanInput × VariableSiteSlot =>
      (horizontalOccurrenceVariableRibbonLookupComputed input).isSome := by
    refine ⟨inferInstance, ?_⟩
    simpa using
      horizontalOccurrenceVariableRibbonSlotActiveBoolComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
