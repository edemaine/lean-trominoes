/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteOffsetSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderData

/-! # Exact-offset compiler boundary for direct sparse routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteOffsetCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Remaining native machine target after replacing route materialization by
the exact first-cell/offset cursor. -/
abbrev DirectSparseRouteOffsetRecordCompiler :=
  TM2ComputableInPolyTime id id
    (directSparseRouteOffsetOutput decider)

/-- Consequently the offset target directly supplies the retained-workspace
route appender consumed by the completed sparse closure. -/
noncomputable def directSparseRouteRecordAppenderOfOffsets
    (compiler : DirectSparseRouteOffsetRecordCompiler decider) :
    DirectSparseRouteRecordAppender decider := by
  let opaqueAppender :=
    RetainedInputAppendPipeline.appendFromWorkspaceComputableInPolyTimeOfCompiler
      (directSparseRouteOffsetOutput decider)
      compiler
  exact RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseRouteOffsetOutput decider))
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedRouteRecordsOfSymbols decider))
    (fun workspace => by
      unfold RetainedInputAppendPipeline.appendFromWorkspace
      rw [directSparseRouteOffsetOutput_eq_routeRecords])
    opaqueAppender

end PeriodicCNFStripReduction
end LeanTrominoes

end
