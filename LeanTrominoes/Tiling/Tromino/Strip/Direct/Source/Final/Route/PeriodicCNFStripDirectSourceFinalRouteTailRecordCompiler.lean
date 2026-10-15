/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Route.PeriodicCNFStripDirectSourceFinalRouteTailRecordData
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachmentCompiler

/-! # Compiler for final direct-clause Figure 9 route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
