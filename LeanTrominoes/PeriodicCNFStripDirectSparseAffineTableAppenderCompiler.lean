/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTableAppenderData
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexIndexedAppenderCompiler

/-! # Transport from table-driven affine vertex appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineTableAppenderCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A first pass that retains source symbols and appends the table-driven
triple request word. -/
abbrev DirectSparseAffineTableTripleAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appended
      (directSparseComputedAffineTableTripleRequestsOfSymbols decider))

/-- A later pass that appends one table-driven retained clause-element block
from the source symbols retained in the workspace. -/
abbrev DirectSparseAffineTableElementAppender (color : WireColor) :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedAffineTableElementRequestsOfSymbols
        decider color))

/-- A table-driven triple appender implements the original indexed triple
contract. -/
def directSparseAffineIndexedTripleAppenderOfTable
    (table : DirectSparseAffineTableTripleAppender decider) :
    DirectSparseAffineIndexedTripleAppender decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (RetainedInputAppendPipeline.appended
      (directSparseComputedAffineTableTripleRequestsOfSymbols decider))
    (RetainedInputAppendPipeline.appended
      (directSparseComputedAffineIndexedTripleRequestsOfSymbols decider))
    (fun symbols => by
      unfold RetainedInputAppendPipeline.appended
      rw [directSparseComputedAffineIndexedTripleRequestsOfSymbols_eq_table])
    table

/-- A table-driven color appender implements the corresponding original
indexed color contract. -/
def directSparseAffineIndexedElementAppenderOfTable
    (color : WireColor)
    (table : DirectSparseAffineTableElementAppender decider color) :
    DirectSparseAffineIndexedElementAppender decider color :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedAffineTableElementRequestsOfSymbols
        decider color))
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedAffineIndexedElementRequestsOfSymbols
        decider color))
    (fun workspace => by
      unfold RetainedInputAppendPipeline.appendFromWorkspace
      rw [directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table])
    table

/-- Four independently verified table-driven passes satisfy the complete
compact affine vertex-request appender boundary. -/
def directSparseAffineVertexRequestAppenderOfTableAppenders
    (triples : DirectSparseAffineTableTripleAppender decider)
    (red : DirectSparseAffineTableElementAppender decider .red)
    (green : DirectSparseAffineTableElementAppender decider .green)
    (blue : DirectSparseAffineTableElementAppender decider .blue) :
    DirectSparseAffineVertexRequestAppender decider :=
  directSparseAffineVertexRequestAppenderOfIndexedAppenders decider
    (directSparseAffineIndexedTripleAppenderOfTable decider triples)
    (directSparseAffineIndexedElementAppenderOfTable decider .red red)
    (directSparseAffineIndexedElementAppenderOfTable decider .green green)
    (directSparseAffineIndexedElementAppenderOfTable decider .blue blue)

end PeriodicCNFStripReduction
end LeanTrominoes
