/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanLookupSemanticBridge

/-! # Semantic activity of variable-fan slots -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem occurrenceAt_isSome_eq_true_iff_mem_usedSlots
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) :
    (occurrenceAt source atom slot).isSome = true ↔
      slot ∈ usedSlots source atom := by
  cases slot <;>
    simp [usedSlots, allOccurrenceSlots,
      PeriodicOneInThreeToThreeDM.OccurrenceSlot.all]

theorem horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : VariableSiteSlot) :
    (horizontalOccurrenceVariableRibbonLookupComputed
        ((source, atom), slot)).isSome = true ↔
      variableSiteOccurrenceSlot slot ∈
        usedSlots
          (horizontalSemanticNormalizedRibbonSource source).erase atom := by
  rw [horizontalOccurrenceVariableRibbonLookupComputed_eq_semantic]
  exact occurrenceAt_isSome_eq_true_iff_mem_usedSlots _ _ _

end PeriodicCNFStripReduction
end LeanTrominoes
