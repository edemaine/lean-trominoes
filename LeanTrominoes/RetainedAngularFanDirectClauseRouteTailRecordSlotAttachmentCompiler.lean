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

/-- Any polynomial-time producer of exact slot inputs composes directly to
the exact direct-clause Figure 9 record stream. -/
noncomputable def
    retainedDirectClauseRouteTailRecordTokensComputableInPolyTimeOf
    {Source InputSymbol : Type}
    (encodeInput : Source → List InputSymbol)
    (slotInputs : Source →
      List RetainedDirectClauseRouteTailRecordSlotInput)
    (compiler : @TM2ComputableInPolyTime
      Source (List RetainedDirectClauseRouteTailRecordSlotInput)
      InputSymbol RetainedDirectClauseRouteTailRecordSlotInput
      encodeInput id slotInputs) :
    @TM2ComputableInPolyTime
      Source (List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token)
      InputSymbol
      PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token
      encodeInput id
      (fun input =>
        retainedDirectClauseRouteTailRecordStream
          (retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
            (slotInputs input))) := by
  let attached := TM2CompositionMachine.computableInPolyTime compiler
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputsComputableInPolyTime
  exact TM2CompositionMachine.computableInPolyTime attached
    retainedDirectClauseRouteTailRecordStreamComputableInPolyTime

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
