/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotPairCompiler
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperData

/-! # Final copied-clause slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Regroup the decoded occurrence stream into one finite query/slot-tuple
input per represented copied clause. -/
def directSourceFinalClauseRouteTailRecordSlotInputs
    (symbols : List encoding.Γ) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  FinalOccurrenceRoleSlotGrouper.slotInputs
    (directSourceFinalOccurrenceRoleSlotPairs decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
