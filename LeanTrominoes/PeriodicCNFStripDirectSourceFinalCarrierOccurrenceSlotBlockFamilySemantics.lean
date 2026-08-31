/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData

/-! # Semantic occurrence-slot blocks of the direct carrier family -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierSlotBlockFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierSlotBlockFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Semantic occurrence slots, grouped by indexed final carrier clause. -/
def directSourceFinalCarrierSemanticOccurrenceSlotBlocks
    (symbols : List encoding.Γ) : List (List RetainedTerminalSlot) :=
  ((directSourceFinalCarrierClauses decider symbols).zipIdx
      (directSourceFinalCarrierStart decider symbols)).map
    (fun taggedClause =>
      taggedClause.1.zipIdx.map (fun taggedLiteral =>
        retainedFinalCoordinatedOccurrenceSlot
          (directSourceFormula decider symbols)
          taggedLiteral.1 taggedClause.2 taggedLiteral.2))

/-- The semantic carrier occurrence-slot blocks are exactly the corresponding
subfamily of global stable-rank blocks. -/
theorem directSourceFinalCarrierSemanticOccurrenceSlotBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierSemanticOccurrenceSlotBlocks decider symbols =
      directSourceFinalCarrierStableRankSlotBlocks decider symbols := by
  unfold directSourceFinalCarrierSemanticOccurrenceSlotBlocks
    directSourceFinalCarrierStableRankSlotBlocks
    directSourceFinalStableRankSlotBlocksFrom
  apply List.map_congr_left
  intro taggedClause taggedMember
  exact directSourceFinalCarrierClauseOccurrenceSlots_eq_stableRankBlock
    decider symbols taggedClause taggedMember

end LeanTrominoes.PeriodicCNFStripReduction

end
