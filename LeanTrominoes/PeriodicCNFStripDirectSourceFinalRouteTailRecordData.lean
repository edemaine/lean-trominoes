/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordQuery
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachment

/-! # Final direct-clause Figure 9 route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Attach bounded slots to every successful direct final clause query and
emit its exact finite-atlas Figure 9 route-tail record word. -/
def directSourceFinalClauseRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  retainedDirectClauseRouteTailRecordStream
    (retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
      (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
