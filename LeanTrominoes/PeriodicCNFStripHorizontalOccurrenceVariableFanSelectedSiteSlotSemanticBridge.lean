/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotActivitySemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSoundness

/-! # Semantic correctness of variable-fan source-slot selection -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Semantic one-, two-, or three-occurrence source slot supplying a finite fan
site. -/
def sourceVariableRibbonSelectedSiteSlot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : VariableSiteSlot) : VariableSiteSlot :=
  match usedSlots source atom with
  | [.first] => .first
  | [.first, .second] => if slot = .first then .first else .second
  | _ => slot

theorem horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (slot : VariableSiteSlot) :
    horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed
        ((source, entry.1.1), slot) =
      sourceVariableRibbonSelectedSiteSlot
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 slot := by
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
    simp [horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed,
      horizontalOccurrenceVariableRibbonSiteSlotSelect,
      sourceVariableRibbonSelectedSiteSlot, secondFalse, one]
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
      simp [horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed,
        horizontalOccurrenceVariableRibbonSiteSlotSelect,
        sourceVariableRibbonSelectedSiteSlot, secondTrue, thirdFalse, two]
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
      simp [horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed,
        horizontalOccurrenceVariableRibbonSiteSlotSelect,
        sourceVariableRibbonSelectedSiteSlot, secondTrue, thirdTrue, three]

end PeriodicCNFStripReduction
end LeanTrominoes
