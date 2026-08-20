/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedRecordSplit
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Direct sparse retained-input record-appender interfaces -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRecordAppenderDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

abbrev DirectSparseRecordWorkspace :=
  encoding.Γ ⊕ GadgetSparseAssignmentTokens.Token

/-- A vertex-record pass retains the original source word on the left and
appends its vertex-record prefix on the right. -/
abbrev DirectSparseVertexRecordAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appended
      (directSparseComputedVertexRecordsOfSymbols decider))

/-- A route-record pass scans a retained workspace, ignores already appended
records, and appends the route-record suffix computed from the retained
source. -/
abbrev DirectSparseRouteRecordAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedRouteRecordsOfSymbols decider))

end PeriodicCNFStripReduction
end LeanTrominoes
