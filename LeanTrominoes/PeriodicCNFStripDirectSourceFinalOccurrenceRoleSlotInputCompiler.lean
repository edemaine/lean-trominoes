/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputData
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for final copied-clause slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotInputStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Decoding followed by one finite-state grouping pass compiles the exact
slot-input stream expected by direct Figure 9 route-record attachment. -/
noncomputable def
    directSourceFinalClauseRouteTailRecordSlotInputsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List RetainedDirectClauseRouteTailRecordSlotInput)
      encoding.Γ RetainedDirectClauseRouteTailRecordSlotInput
      id id
      (directSourceFinalClauseRouteTailRecordSlotInputs decider) := by
  unfold directSourceFinalClauseRouteTailRecordSlotInputs
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceRoleSlotPairsComputableInPolyTime decider)
    FinalOccurrenceRoleSlotGrouper.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
