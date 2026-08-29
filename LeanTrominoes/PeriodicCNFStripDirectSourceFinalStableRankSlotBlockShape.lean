/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockData

/-! # Shape of direct-source stable-rank slot blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotBlockShapeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotBlockShapeVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalStableRankSlotBlocks_nonempty
    (symbols : List encoding.Γ) :
    ∀ block ∈ directSourceFinalStableRankSlotBlocks decider symbols,
      block ≠ [] := by
  intro block blockMember
  rcases List.mem_map.mp blockMember with
    ⟨taggedClause, taggedMember, rfl⟩
  have clauseMember := List.fst_mem_of_mem_zipIdx taggedMember
  rw [directSourceFinalScaledClauses_eq decider symbols] at clauseMember
  have clauseNonempty := directSource_deduplicatedClauses_nonempty
    decider symbols taggedClause.1 clauseMember
  unfold retainedOccurrenceGlobalStableTerminalSlotBlock
  simpa using clauseNonempty

theorem directSourceFinalStableRankSlotBlocks_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ block ∈ directSourceFinalStableRankSlotBlocks decider symbols,
      block.length ≤ 3 := by
  intro block blockMember
  rcases List.mem_map.mp blockMember with
    ⟨taggedClause, taggedMember, rfl⟩
  have clauseMember := List.fst_mem_of_mem_zipIdx taggedMember
  rw [directSourceFinalScaledClauses_eq decider symbols] at clauseMember
  unfold retainedOccurrenceGlobalStableTerminalSlotBlock
  simpa using directSource_deduplicatedClauses_widthAtMostThree
    decider symbols taggedClause.1 clauseMember

end LeanTrominoes.PeriodicCNFStripReduction

end
