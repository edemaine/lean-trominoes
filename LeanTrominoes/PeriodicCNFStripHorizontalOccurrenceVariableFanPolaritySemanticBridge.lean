/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSelectedSiteSlotSemanticBridge

/-! # Semantic correctness of variable-fan polarities -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonPolarityComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (slot : VariableSiteSlot) :
    horizontalOccurrenceVariableRibbonPolarityComputed
        ((source, entry.1.1), slot) =
      sourceVariableSitePolarity
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 slot := by
  unfold horizontalOccurrenceVariableRibbonPolarityComputed
    horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
  rw [horizontalOccurrenceVariableSourceComputed_eq_semantic,
    horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed_eq_semantic]
  rcases usedSlots_cases_of_atom_mem
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1.1 entry.atom_mem with one | twoOrThree
  · cases slot <;>
      simp [sourceVariableRibbonSelectedSiteSlot,
        sourceVariableSitePolarity, one, variableSiteOccurrenceSlot]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp [sourceVariableRibbonSelectedSiteSlot,
          sourceVariableSitePolarity, two, variableSiteOccurrenceSlot]
    · cases slot <;>
        simp [sourceVariableRibbonSelectedSiteSlot,
          sourceVariableSitePolarity, three, variableSiteOccurrenceSlot]

end PeriodicCNFStripReduction
end LeanTrominoes
