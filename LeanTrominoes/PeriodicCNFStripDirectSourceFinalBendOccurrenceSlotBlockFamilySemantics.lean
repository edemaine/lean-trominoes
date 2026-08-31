/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData

/-! # Semantic occurrence-slot blocks of the direct bend family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendSlotBlockFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendSlotBlockFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Semantic occurrence slots, grouped by indexed final bend clause. -/
def directSourceFinalBendSemanticOccurrenceSlotBlocks
    (symbols : List encoding.Γ) : List (List RetainedTerminalSlot) :=
  ((directSourceFinalBendClauses decider symbols).zipIdx
      (directSourceFinalBendStart decider symbols)).map
    (fun taggedClause =>
      taggedClause.1.zipIdx.map (fun taggedLiteral =>
        retainedFinalCoordinatedOccurrenceSlot
          (directSourceFormula decider symbols)
          taggedLiteral.1 taggedClause.2 taggedLiteral.2))

/-- The semantic bend occurrence-slot blocks are exactly the corresponding
subfamily of global stable-rank blocks. -/
theorem directSourceFinalBendSemanticOccurrenceSlotBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendSemanticOccurrenceSlotBlocks decider symbols =
      directSourceFinalBendStableRankSlotBlocks decider symbols := by
  unfold directSourceFinalBendSemanticOccurrenceSlotBlocks
    directSourceFinalBendStableRankSlotBlocks
    directSourceFinalStableRankSlotBlocksFrom
  apply List.map_congr_left
  intro taggedClause taggedMember
  exact directSourceFinalBendClauseOccurrenceSlots_eq_stableRankBlock
    decider symbols taggedClause taggedMember

/-- The compiled bend occurrence-slot stream is the flattened sequence of
semantic occurrence slots in final bend-clause order. -/
theorem directSourceFinalBendOccurrenceSlots_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalBendOccurrenceSlots decider symbols =
      (directSourceFinalBendSemanticOccurrenceSlotBlocks
        decider symbols).flatten := by
  rw [directSourceFinalBendOccurrenceSlots_eq_stableRankSlots]
  unfold directSourceFinalBendStableRankSlots
  rw [directSourceFinalBendSemanticOccurrenceSlotBlocks_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
