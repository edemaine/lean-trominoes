/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRecordData

/-! # Route-triple compiler boundary for the direct sparse strip reduction -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Native compiler target for the canonical route-record suffix.  The
`directSparseComputedRouteRecordsOfSymbols_eq_tripleRecords` theorem exposes
this target as the edge-major local-triple word without forcing machine-record
elaboration to normalize that large geometric expression. -/
abbrev DirectSparseCanonicalRouteRecordCompiler :=
  TM2ComputableInPolyTime id id
    (directSparseComputedRouteRecordsOfSymbols decider)

/-- An exact native compiler for the canonical route word automatically
supplies the retained-workspace route appender used by the final two-pass
sparse record pipeline. -/
noncomputable def directSparseRouteRecordAppenderOfCompiler
    (compiler : DirectSparseCanonicalRouteRecordCompiler decider) :
    DirectSparseRouteRecordAppender decider :=
  RetainedInputAppendPipeline.appendFromWorkspaceComputableInPolyTimeOfCompiler
    (directSparseComputedRouteRecordsOfSymbols decider) compiler

end PeriodicCNFStripReduction
end LeanTrominoes
