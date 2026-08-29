/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackQuerySlotBlockArityTail

/-! # Arity alignment of the final crossover family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverArityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCrossoverQueryArity_eq_slotBlockLengths
    (symbols : List encoding.Γ) :
    (directRetainedFinalCrossoverClauseQueries decider symbols).map
        FinalOccurrenceRoleSlotGrouper.queryArity =
      (directSourceFinalCrossoverStableRankSlotBlocks decider symbols).map
        List.length := by
  have total :=
    directSourceFinalQueryArity_eq_stableRankSlotBlockLengths
      decider symbols
  have crossoverLength :
      ((directRetainedFinalCrossoverClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity).length =
        ((directSourceFinalCrossoverStableRankSlotBlocks
            decider symbols).map List.length).length := by
    simp only [List.length_map]
    exact (directRetainedFinalCrossoverClauseQueries_length
      decider symbols).trans
      (directSourceFinalCrossoverStableRankSlotBlocks_length
        decider symbols).symm
  let prefixLength :=
    ((directRetainedFinalCrossoverClauseQueries decider symbols).map
      FinalOccurrenceRoleSlotGrouper.queryArity).length
  have taken := congrArg (List.take prefixLength) total
  calc
    (directRetainedFinalCrossoverClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity =
        ((directRetainedFinalClauseQueryAssembly decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity).take
            prefixLength := by
      unfold directRetainedFinalClauseQueryAssembly prefixLength
      simp only [List.map_append]
      rw [List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
    _ = ((directSourceFinalStableRankSlotBlocks decider symbols).map
          List.length).take prefixLength := taken
    _ = (directSourceFinalCrossoverStableRankSlotBlocks
          decider symbols).map List.length := by
      rw [directSourceFinalStableRankSlotBlocks_eq_fiveFamilies]
      unfold prefixLength
      simp only [List.map_append]
      rw [crossoverLength]
      rw [List.append_assoc]
      rw [List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]

end LeanTrominoes.PeriodicCNFStripReduction

end
