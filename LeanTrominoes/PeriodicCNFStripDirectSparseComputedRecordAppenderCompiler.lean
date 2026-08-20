/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderData

/-! # Composition of proof-free direct sparse record appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseComputedRecordAppenderStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Sequential retained-input appenders emit the exact proof-free complete
record word. -/
def directSparseComputedRecordEmitterOfAppenders
    (vertices : DirectSparseVertexRecordAppender decider)
    (routes : DirectSparseRouteRecordAppender decider) :
    TM2ComputableInPolyTime id id
      (directSparseComputedAssignmentRecordsOfSymbols decider) := by
  exact RetainedInputAppendPipeline.computableInPolyTimeOfAppendersEq
    (directSparseComputedVertexRecordsOfSymbols decider)
    (directSparseComputedRouteRecordsOfSymbols decider)
    (directSparseComputedAssignmentRecordsOfSymbols decider)
    (fun symbols =>
      (directSparseComputedAssignmentRecordsOfSymbols_eq_split
        decider symbols).symm)
    vertices routes

end PeriodicCNFStripReduction
end LeanTrominoes
