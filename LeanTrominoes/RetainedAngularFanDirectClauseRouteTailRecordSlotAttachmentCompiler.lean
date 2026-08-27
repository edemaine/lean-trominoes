/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordCompiler
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachment
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling occurrence-slot attachment for direct clause records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Matching finite direction queries and occurrence slots attach in one
fixed finite-state pass. -/
noncomputable def
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      retainedDirectClauseRouteTailRecordQueriesOfSlotInputs :=
  FiniteBlockTransducer.computableInPolyTime fun input =>
    (retainedDirectClauseRouteTailRecordQueryOfSlotInput input).toList

/-- Slot attachment followed by finite route lookup and exact record
formatting remains polynomial time. -/
noncomputable def
    retainedDirectClauseRouteTailRecordTokensOfSlotInputsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun inputs : List RetainedDirectClauseRouteTailRecordSlotInput =>
        retainedDirectClauseRouteTailRecordStream
          (retainedDirectClauseRouteTailRecordQueriesOfSlotInputs inputs)) :=
  TM2CompositionMachine.computableInPolyTime
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputsComputableInPolyTime
    retainedDirectClauseRouteTailRecordStreamComputableInPolyTime

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
