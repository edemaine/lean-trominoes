/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeyCyclicSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceSuccessorIndex

/-! # Compiled successor keys name the actual next occurrence entry -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private theorem cyclicSuccessorKey_base_rank (values : List Nat) (value rank : Nat)
    (rankLt : rank < 3) :
    StableOccurrenceRanks.cyclicSuccessorKey values (value * 3 + rank) =
      value * 3 + (rank + 1) % values.count value := by
  have quotient : (value * 3 + rank) / 3 = value := by omega
  have remainder : (value * 3 + rank) % 3 = rank := by omega
  simp only [StableOccurrenceRanks.cyclicSuccessorKey, quotient, remainder]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The numeric cyclic map advances to the key of the actual next used
occurrence, including the one-slot case where that entry stays the same. -/
theorem directSourceFinalHorizontalOccurrenceKey_cyclicSuccessor
    (symbols : List encoding.Γ) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase) :
    StableOccurrenceRanks.cyclicSuccessorKey (directSourceFinalAtomIdentityCodes decider symbols)
        (directSourceFinalHorizontalOccurrenceKey decider symbols entry) =
      directSourceFinalHorizontalOccurrenceKey decider symbols
        (entry.1, nextUsedSlot (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2) := by
  have memberships := (mem_occurrenceEntries_iff
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2).mp member
  have nextMember := (mem_occurrenceEntries_iff
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1
    (nextUsedSlot (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2)).mpr
      ⟨memberships.1, nextUsedSlot_mem _ _ _ memberships.2⟩
  have lookup := (occurrenceEntryIndex_spec (horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry member).1
  have currentKey := directSourceFinalHorizontalOccurrenceKey_eq_base_rank decider symbols
    (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry)
    entry.1 lookup entry.2 member
  have nextKey := directSourceFinalHorizontalOccurrenceKey_eq_base_rank decider symbols
    (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry)
    entry.1 lookup
    (nextUsedSlot (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2) nextMember
  have rankLt : entry.2.index < 3 := by cases entry.2 <;> decide
  have countLe := directSourceFinalNormalizedAtom_count_le_three decider symbols entry.1
    (List.mem_iff_getElem?.mpr ⟨_, lookup⟩)
  have nextIndex : (nextUsedSlot (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2).index =
      (entry.2.index + 1) % (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count entry.1 := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      nextUsedSlot_index_eq_mod_count (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase
        entry.1 memberships.1 entry.2 memberships.2
        (by simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using countLe)
  rw [currentKey, nextKey, cyclicSuccessorKey_base_rank _ _ _ rankLt,
    directSourceFinalAtomIdentityCodes_count_eq_normalized decider symbols _ entry.1 lookup, nextIndex]

/-- The complete compiled successor column preserves canonical entry order
and names each entry's actual cyclic successor. -/
theorem directSourceFinalGroupedNextOccurrenceKeys_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedNextOccurrenceKeys decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (fun entry => directSourceFinalHorizontalOccurrenceKey decider symbols
          (entry.1, nextUsedSlot (horizontalSemanticNormalizedRibbonSource
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1 entry.2)) := by
  rw [directSourceFinalGroupedNextOccurrenceKeys_eq_map_cyclic,
    directSourceFinalUniqueFanQueryKeys_eq_horizontal, List.map_map]
  apply List.map_congr_left
  intro entry member
  exact directSourceFinalHorizontalOccurrenceKey_cyclicSuccessor decider symbols entry member

end LeanTrominoes.PeriodicCNFStripReduction

end
