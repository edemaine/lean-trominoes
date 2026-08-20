/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotActivitySemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans

/-! # Semantic correctness of variable-fan endpoint directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonDirectionComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (slot : VariableSiteSlot) :
    horizontalOccurrenceVariableRibbonDirectionComputed
        (source, entry.1.1) slot =
      (sourceVariableRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry).direction slot := by
  let occurrenceSlot := variableSiteOccurrenceSlot slot
  by_cases member :
      (entry.1.1, occurrenceSlot) ∈ occurrenceEntries
        (horizontalSemanticNormalizedRibbonSource source).erase
  · have activeBool :
        (horizontalOccurrenceVariableRibbonLookupComputed
          ((source, entry.1.1), slot)).isSome = true :=
      (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
        source entry.1.1 slot).mpr
          ((mem_occurrenceEntries_iff
            (horizontalSemanticNormalizedRibbonSource source).erase
            entry.1.1 occurrenceSlot).mp member).2
    unfold horizontalOccurrenceVariableRibbonDirectionComputed
      horizontalOccurrenceVariableRibbonDirectionSelect
      horizontalOccurrenceVariableRibbonRouteInput
    simp only [activeBool, if_true]
    rw [horizontalOccurrenceSourceVariableDirectionComputed_eq_semantic
      source
      (⟨(entry.1.1, occurrenceSlot), member⟩ :
        ActiveOccurrenceEntry
          (horizontalSemanticNormalizedRibbonSource source).erase)]
    simp [sourceVariableRibbonFanData, occurrenceSlot, member]
  · have inactiveBool :
        (horizontalOccurrenceVariableRibbonLookupComputed
          ((source, entry.1.1), slot)).isSome = false :=
      Bool.eq_false_of_not_eq_true fun active => by
        apply member
        exact (mem_occurrenceEntries_iff
          (horizontalSemanticNormalizedRibbonSource source).erase
          entry.1.1 occurrenceSlot).mpr
            ⟨entry.atom_mem,
              (horizontalOccurrenceVariableRibbonSlotActive_iff_mem_usedSlots
                source entry.1.1 slot).mp active⟩
    unfold horizontalOccurrenceVariableRibbonDirectionComputed
      horizontalOccurrenceVariableRibbonDirectionSelect
    simp [inactiveBool, sourceVariableRibbonFanData, occurrenceSlot, member]

end PeriodicCNFStripReduction
end LeanTrominoes
