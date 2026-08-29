/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackQuerySlotBlockFamilyLength

/-! # Individual fallback-family query/slot-block lengths -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackIndividualLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalFallbackIndividualLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem carrierDescriptorLength_eq_clauseLength
    {OtherVariable : Type}
    (first second : DecidableEq OtherVariable)
    (source : PeriodicCNF OtherVariable) :
    (@carrierMetadataClauseDescriptors OtherVariable first source).length =
      (@carrierMetadataNormalizedClauses
        OtherVariable second source).length := by
  have implementationEq : first = second := Subsingleton.elim _ _
  subst second
  simp [carrierMetadataClauseDescriptors,
    carrierMetadataNormalizedClauses]

private theorem retainedFinalPrecomputedClauseQueries_length
    (tokens : List FormulaShapeDirectionOrdering.Token) :
    (retainedFinalPrecomputedClauseQueries tokens).length =
      tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      change
        (retainedFinalPrecomputedClauseQueryBlock token ++
          retainedFinalPrecomputedClauseQueries tokens).length =
        (token :: tokens).length
      rw [List.length_append, induction]
      simp [retainedFinalPrecomputedClauseQueryBlock, Nat.add_comm]

theorem directSourceFinalCarrierQuerySlotBlocks_length
    (symbols : List encoding.Γ) :
    (directRetainedFinalCarrierClauseQueries decider symbols).length =
      (directSourceFinalCarrierStableRankSlotBlocks
        decider symbols).length := by
  rw [directSourceFinalCarrierStableRankSlotBlocks_length]
  unfold directRetainedFinalCarrierClauseQueries
  rw [retainedFinalPrecomputedClauseQueries_length]
  unfold
    directRetainedPlanarMetadataCarrierClauseDescriptors
    directSourceFinalCarrierClauses
    PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
  rw [directSourceFormula_eq_threeSATThree]
  unfold directThreeCNFSourceFormula
  exact carrierDescriptorLength_eq_clauseLength _ _ _

theorem directSourceFinalBendQuerySlotBlocks_length
    (symbols : List encoding.Γ) :
    (directRetainedFinalBendClauseQueries decider symbols).length =
      (directSourceFinalBendStableRankSlotBlocks
        decider symbols).length := by
  have combined :=
    directSourceFinalFallbackQuerySlotBlocks_length decider symbols
  have carrier :=
    directSourceFinalCarrierQuerySlotBlocks_length decider symbols
  simp only [List.length_append] at combined
  omega

end LeanTrominoes.PeriodicCNFStripReduction

end
