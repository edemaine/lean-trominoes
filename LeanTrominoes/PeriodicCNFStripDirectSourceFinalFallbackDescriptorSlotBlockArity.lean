/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQuerySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendQuerySlotBlockArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverQuerySlotBlockArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskSemantics

/-! # Descriptor arities of final fallback slot-block families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackDescriptorArityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalFallbackDescriptorArityVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem evaluatedDescriptorArities_eq_queryArities
    (queries : List RetainedFinalCopiedClauseQuery) :
    (retainedFinalCopiedClauseDescriptors queries).map
        retainedFinalCopiedDescriptorArity =
      queries.map FinalOccurrenceRoleSlotGrouper.queryArity := by
  rw [retainedFinalCopiedClauseDescriptorArities_eq_queryArities]
  rfl

theorem directSourceFinalCrossoverDescriptorArities_eq_slotBlockLengths
    (symbols : List encoding.Γ) :
    (retainedFinalCopiedClauseDescriptors
        (directRetainedFinalCrossoverClauseQueries decider symbols)).map
          retainedFinalCopiedDescriptorArity =
      (directSourceFinalCrossoverStableRankSlotBlocks decider symbols).map
        List.length := by
  exact (evaluatedDescriptorArities_eq_queryArities _).trans
    (directSourceFinalCrossoverQueryArity_eq_slotBlockLengths
      decider symbols)

theorem directSourceFinalCarrierDescriptorArities_eq_slotBlockLengths
    (symbols : List encoding.Γ) :
    (directRetainedPlanarMetadataCarrierClauseDescriptors
        decider symbols).map retainedFinalCopiedDescriptorArity =
      (directSourceFinalCarrierStableRankSlotBlocks decider symbols).map
        List.length := by
  rw [← directRetainedFinalCarrierClauseQueryDescriptors_eq]
  exact (evaluatedDescriptorArities_eq_queryArities _).trans
    (directSourceFinalCarrierQueryArity_eq_slotBlockLengths
      decider symbols)

theorem directSourceFinalBendDescriptorArities_eq_slotBlockLengths
    (symbols : List encoding.Γ) :
    (directRetainedPlanarMetadataBaseBendClauseDescriptors
        decider symbols).map retainedFinalCopiedDescriptorArity =
      (directSourceFinalBendStableRankSlotBlocks decider symbols).map
        List.length := by
  rw [← directRetainedFinalBendClauseQueryDescriptors_eq]
  exact (evaluatedDescriptorArities_eq_queryArities _).trans
    (directSourceFinalBendQueryArity_eq_slotBlockLengths
      decider symbols)

theorem directSourceFinalCrossoverOccurrenceMaskBlock_eq_replicate
    (active : Bool) (symbols : List encoding.Γ) :
    descriptorOccurrenceMask active
        (retainedFinalCopiedClauseDescriptors
          (directRetainedFinalCrossoverClauseQueries decider symbols)) =
      List.replicate
        (directSourceFinalCrossoverStableRankSlotBlocks
          decider symbols).flatten.length active := by
  rw [descriptorOccurrenceMask_eq_replicate,
    directSourceFinalCrossoverDescriptorArities_eq_slotBlockLengths,
    List.length_flatten]

theorem directSourceFinalCarrierOccurrenceMaskBlock_eq_replicate
    (active : Bool) (symbols : List encoding.Γ) :
    descriptorOccurrenceMask active
        (directRetainedPlanarMetadataCarrierClauseDescriptors
          decider symbols) =
      List.replicate
        (directSourceFinalCarrierStableRankSlotBlocks
          decider symbols).flatten.length active := by
  rw [descriptorOccurrenceMask_eq_replicate,
    directSourceFinalCarrierDescriptorArities_eq_slotBlockLengths,
    List.length_flatten]

theorem directSourceFinalBendOccurrenceMaskBlock_eq_replicate
    (active : Bool) (symbols : List encoding.Γ) :
    descriptorOccurrenceMask active
        (directRetainedPlanarMetadataBaseBendClauseDescriptors
          decider symbols) =
      List.replicate
        (directSourceFinalBendStableRankSlotBlocks
          decider symbols).flatten.length active := by
  rw [descriptorOccurrenceMask_eq_replicate,
    directSourceFinalBendDescriptorArities_eq_slotBlockLengths,
    List.length_flatten]

end LeanTrominoes.PeriodicCNFStripReduction

end
