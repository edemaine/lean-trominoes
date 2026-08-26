/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectPreparedHeaderEmitter
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenCompiler
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Direct sparse prepared-token emitter compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparsePreparedTokenEmitterCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compose the independently streamed prepared header with the fixed parser
expansion of a sparse assignment-record stream. -/
def directSparseCompiledTrominoStripPreparedTokensOfSymbolsComputableInPolyTimeOfRecordEmitter
    (tromino : Tromino)
    (recordEmitter : TM2ComputableInPolyTime id id
      (directSparseAssignmentRecordsOfSymbols decider)) :
    TM2ComputableInPolyTime id id
      (directSparseCompiledTrominoStripPreparedTokensOfSymbols
        decider tromino) := by
  let headerAppender :=
    RetainedInputAppendPipeline.appendedComputableInPolyTimeOfCompiler
      (directPreparedHeaderOfSymbols decider)
      (directPreparedHeaderOfSymbolsComputableInPolyTime decider)
  let motif := fun symbols =>
    GadgetSparseExpandedMotifFiniteTokens.preparedSparseExpandedMotif
      tromino (directSparseAssignmentsOfSymbols decider symbols)
  let motifAppender :=
    RetainedInputAppendPipeline.appendFromWorkspaceComputableInPolyTimeOfCompiler
      motif
      (directSparsePreparedMotifComputableInPolyTimeOfRecordEmitter
        decider tromino recordEmitter)
  exact RetainedInputAppendPipeline.computableInPolyTimeOfAppendersEq
    (directPreparedHeaderOfSymbols decider)
    motif
    (directSparseCompiledTrominoStripPreparedTokensOfSymbols decider tromino)
    (fun _ => rfl)
    headerAppender motifAppender

/-- Sparse assignment-record emitters discharge the remaining prepared-token
emitter contract for the direct Theorem 5.2 reduction. -/
theorem directSparseCompiledTrominoStripPreparedTokenEmitters_of_assignmentRecordEmitters
    (emitters : DirectSparseAssignmentRecordEmitters) :
    DirectSparseCompiledTrominoStripPreparedTokenEmitters := by
  intro Input encoding language decider tromino
  exact (emitters encoding language decider).map
    (directSparseCompiledTrominoStripPreparedTokensOfSymbolsComputableInPolyTimeOfRecordEmitter
      decider tromino)

end PeriodicCNFStripReduction
end LeanTrominoes
