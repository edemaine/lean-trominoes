/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackQuerySlotBlockIndividualLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilySemantics
import LeanTrominoes.AlignedRetainedTerminalSlotFilterSemantics

/-! # Arity alignment after the final crossover prefix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackArityTailStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalFallbackArityTailVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Four-family query-arity suffix beginning immediately after crossovers. -/
def directSourceFinalFallbackQueryArityTail
    (symbols : List encoding.Γ) : List Nat :=
  (directRetainedFinalCarrierClauseQueries decider symbols).map
      FinalOccurrenceRoleSlotGrouper.queryArity ++
    (directRetainedFinalBendClauseQueries decider symbols).map
        FinalOccurrenceRoleSlotGrouper.queryArity ++
      ((directRetainedFinalRoutedClauseQueries decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity ++
        (directRetainedFinalRoutedVariableClauseQueries
            decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity)

/-- Four-family stable-slot block-length suffix after crossovers. -/
def directSourceFinalFallbackSlotBlockLengthTail
    (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalCarrierStableRankSlotBlocks decider symbols).map
      List.length ++
    (directSourceFinalBendStableRankSlotBlocks decider symbols).map
        List.length ++
      ((directSourceFinalRoutedClauseStableRankSlotBlocks
            decider symbols).map List.length ++
        (directSourceFinalRoutedVariableStableRankSlotBlocks
            decider symbols).map List.length)

/-- Cancelling the equally long crossover prefixes exposes the four-family
arity alignment beginning with retained carriers. -/
theorem directSourceFinalFallbackArityTail_eq
    (symbols : List encoding.Γ) :
    directSourceFinalFallbackQueryArityTail decider symbols =
      directSourceFinalFallbackSlotBlockLengthTail decider symbols := by
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
  have dropped := congrArg (List.drop prefixLength) total
  calc
    directSourceFinalFallbackQueryArityTail decider symbols =
        ((directRetainedFinalClauseQueryAssembly decider symbols).map
          FinalOccurrenceRoleSlotGrouper.queryArity).drop prefixLength := by
      unfold directSourceFinalFallbackQueryArityTail prefixLength
        directRetainedFinalClauseQueryAssembly
        directRetainedFinalCarrierClauseQuerySuffix
        directRetainedFinalBendClauseQuerySuffix
        directRetainedFinalRoutedClauseQuerySuffix
      simp only [List.map_append]
      rw [List.drop_append_of_le_length (Nat.le_refl _),
        List.drop_length, List.nil_append]
      simp only [List.append_assoc]
    _ = ((directSourceFinalStableRankSlotBlocks decider symbols).map
          List.length).drop prefixLength := dropped
    _ = directSourceFinalFallbackSlotBlockLengthTail decider symbols := by
      rw [directSourceFinalStableRankSlotBlocks_eq_fiveFamilies]
      unfold directSourceFinalFallbackSlotBlockLengthTail prefixLength
      simp only [List.map_append, List.append_assoc]
      rw [crossoverLength]
      rw [List.drop_append_of_le_length (Nat.le_refl _),
        List.drop_length, List.nil_append]

end LeanTrominoes.PeriodicCNFStripReduction

end
