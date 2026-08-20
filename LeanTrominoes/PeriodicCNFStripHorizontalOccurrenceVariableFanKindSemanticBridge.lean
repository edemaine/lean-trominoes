/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSelectedSiteSlotSemanticBridge

/-! # Semantic correctness of variable-fan connector kinds -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonKindComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (slot : VariableSiteSlot) :
    horizontalOccurrenceVariableRibbonKindComputed
        ((source, entry.1.1), slot) =
      sourceVariableSiteKind
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 slot := by
  unfold horizontalOccurrenceVariableRibbonKindComputed
    horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
  rw [horizontalOccurrenceVariableSourceComputed_eq_semantic,
    horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed_eq_semantic]
  rcases usedSlots_cases_of_atom_mem
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1.1 entry.atom_mem with one | twoOrThree
  · cases slot <;>
      simp [sourceVariableRibbonSelectedSiteSlot,
        sourceVariableSiteKind, one, variableSiteOccurrenceSlot]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp [sourceVariableRibbonSelectedSiteSlot,
          sourceVariableSiteKind, two, variableSiteOccurrenceSlot]
    · cases slot <;>
        simp [sourceVariableRibbonSelectedSiteSlot,
          sourceVariableSiteKind, three, variableSiteOccurrenceSlot]

end PeriodicCNFStripReduction
end LeanTrominoes
