/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotActivitySemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSoundness

/-! # Semantic correctness of the variable-fan count code -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonCountPredComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceVariableRibbonCountPredComputed
        (source, entry.1.1) =
      sourceVariableRibbonCountPred
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 := by
  rcases usedSlots_cases_of_atom_mem
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1.1 entry.atom_mem with one | twoOrThree
  · have secondFalse :
        (horizontalOccurrenceVariableRibbonLookupComputed
          ((source, entry.1.1), VariableSiteSlot.second)).isSome = false :=
      Bool.eq_false_of_not_eq_true fun active => by
        have member :=
          (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
            source entry.1.1 VariableSiteSlot.second).mp active
        simp [one, variableSiteOccurrenceSlot] at member
    simp [horizontalOccurrenceVariableRibbonCountPredComputed,
      secondFalse, sourceVariableRibbonCountPred, one]
  · rcases twoOrThree with two | three
    · have secondTrue :
          (horizontalOccurrenceVariableRibbonLookupComputed
            ((source, entry.1.1), VariableSiteSlot.second)).isSome = true :=
        (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
          source entry.1.1 VariableSiteSlot.second).mpr
            (by simp [two, variableSiteOccurrenceSlot])
      have thirdFalse :
          (horizontalOccurrenceVariableRibbonLookupComputed
            ((source, entry.1.1), VariableSiteSlot.third)).isSome = false :=
        Bool.eq_false_of_not_eq_true fun active => by
          have member :=
            (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
              source entry.1.1 VariableSiteSlot.third).mp active
          simp [two, variableSiteOccurrenceSlot] at member
      simp [horizontalOccurrenceVariableRibbonCountPredComputed,
        secondTrue, thirdFalse, sourceVariableRibbonCountPred, two]
    · have secondTrue :
          (horizontalOccurrenceVariableRibbonLookupComputed
            ((source, entry.1.1), VariableSiteSlot.second)).isSome = true :=
        (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
          source entry.1.1 VariableSiteSlot.second).mpr
            (by simp [three, variableSiteOccurrenceSlot])
      have thirdTrue :
          (horizontalOccurrenceVariableRibbonLookupComputed
            ((source, entry.1.1), VariableSiteSlot.third)).isSome = true :=
        (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
          source entry.1.1 VariableSiteSlot.third).mpr
            (by simp [three, variableSiteOccurrenceSlot])
      simp [horizontalOccurrenceVariableRibbonCountPredComputed,
        secondTrue, thirdTrue, sourceVariableRibbonCountPred, three]

end PeriodicCNFStripReduction
end LeanTrominoes
