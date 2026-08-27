/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderData

/-! # Direct finite-direction route compiler boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteDirectionCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Native compiler target after replacing final coordinate routes by their
affine starts and finite three-round direction words. -/
abbrev DirectSparseRouteDirectionRecordCompiler :=
  TM2ComputableInPolyTime id id
    (directSparseRouteDirectionRecordOutput decider)

/-- Any exact finite-direction record compiler supplies the retained-workspace
route appender used by the final sparse closure. -/
noncomputable def directSparseRouteRecordAppenderOfDirections
    (compiler : DirectSparseRouteDirectionRecordCompiler decider) :
    DirectSparseRouteRecordAppender decider := by
  let opaqueAppender :=
    RetainedInputAppendPipeline.appendFromWorkspaceComputableInPolyTimeOfCompiler
      (directSparseRouteDirectionRecordOutput decider) compiler
  exact RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseRouteDirectionRecordOutput decider))
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedRouteRecordsOfSymbols decider))
    (fun workspace => by
      unfold RetainedInputAppendPipeline.appendFromWorkspace
      rw [directSparseRouteDirectionRecordOutput_eq_routeRecords])
    opaqueAppender

end PeriodicCNFStripReduction
end LeanTrominoes

end
