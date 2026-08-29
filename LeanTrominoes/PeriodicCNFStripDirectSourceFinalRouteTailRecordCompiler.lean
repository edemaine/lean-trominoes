/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteTailRecordData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachmentCompiler

/-! # Compiler for final direct-clause Figure 9 route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRouteTailRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The grouped slot-input compiler composes with finite slot attachment,
route lookup, and exact route-tail record formatting. -/
noncomputable def
    directSourceFinalClauseRouteTailRecordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List HorizontalRoutedRouteTailRecord.Token)
      encoding.Γ HorizontalRoutedRouteTailRecord.Token
      id id
      (directSourceFinalClauseRouteTailRecordTokens decider) := by
  unfold directSourceFinalClauseRouteTailRecordTokens
  exact retainedDirectClauseRouteTailRecordTokensComputableInPolyTimeOf
    id
    (directSourceFinalClauseRouteTailRecordSlotInputs decider)
    (directSourceFinalClauseRouteTailRecordSlotInputsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
