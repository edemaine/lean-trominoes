/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockShape
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperListBlockSemantics

/-! # Clause-block semantics of final copied-clause slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotInputBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotInputBlockVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled slot inputs are the five-family query list zipped with one
packed global stable-rank slot block per final copied clause. -/
theorem directSourceFinalClauseRouteTailRecordSlotInputs_eq_zip_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalClauseRouteTailRecordSlotInputs decider symbols =
      List.zip
        (directRetainedFinalClauseQueryAssembly decider symbols)
        ((directSourceFinalStableRankSlotBlocks decider symbols).map
          RetainedDirectClauseOccurrenceSlots.ofList) := by
  rw [directSourceFinalClauseRouteTailRecordSlotInputs_eq_grouped
    decider symbols]
  rw [← directSourceFinalStableRankSlotBlocks_flatten decider symbols]
  exact
    FinalOccurrenceRoleSlotGrouper.slotInputsOfQueries_flatten_blocks
      _ _
      (directSourceFinalQuery_length_eq_stableRankSlotBlocks
        decider symbols)
      (directSourceFinalStableRankSlotBlocks_nonempty decider symbols)
      (directSourceFinalStableRankSlotBlocks_widthAtMostThree
        decider symbols)
      (directSourceFinalQueryArity_eq_stableRankSlotBlockLengths
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
