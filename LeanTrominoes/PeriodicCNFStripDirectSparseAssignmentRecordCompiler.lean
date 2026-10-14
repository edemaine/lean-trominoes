/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.GadgetSparseAssignmentTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentRecordData

/-! # Direct sparse assignment-record compiler boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- A polynomial-time direct record emitter composes with the fixed parser to
emit the exact prepared sparse motif (without its independently streamed
header). -/
def directSparsePreparedMotifComputableInPolyTimeOfRecordEmitter
    (tromino : Tromino)
    (emitter : TM2ComputableInPolyTime id id
      (directSparseAssignmentRecordsOfSymbols decider)) :
    TM2ComputableInPolyTime id id
      (fun symbols =>
        GadgetSparseExpandedMotifFiniteTokens.preparedSparseExpandedMotif
          tromino (directSparseAssignmentsOfSymbols decider symbols)) := by
  exact GadgetSparseAssignmentTokenCompiler.computableInPolyTimeOfEmitter
    tromino emitter

/-- Uniform remaining geometry-emitter contract after fixed record expansion
has been discharged. -/
def DirectSparseAssignmentRecordEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.LeanTrominoes.FiniteEncoding Input)
      (language : Input → Prop)
      (decider : PeriodicCNF.ProgramSource encoding language),
    Nonempty
      (TM2ComputableInPolyTime id id
        (directSparseAssignmentRecordsOfSymbols decider))

end PeriodicCNFStripReduction
end LeanTrominoes
