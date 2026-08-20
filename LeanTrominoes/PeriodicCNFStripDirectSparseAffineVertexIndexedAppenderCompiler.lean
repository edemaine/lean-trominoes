/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexIndexedAppenderData

/-! # Composition of four indexed affine vertex appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineIndexedAppenderCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Four independently verified indexed scanners satisfy the compact affine
vertex-request appender boundary. -/
def directSparseAffineVertexRequestAppenderOfIndexedAppenders
    (triples : DirectSparseAffineIndexedTripleAppender decider)
    (red : DirectSparseAffineIndexedElementAppender decider .red)
    (green : DirectSparseAffineIndexedElementAppender decider .green)
    (blue : DirectSparseAffineIndexedElementAppender decider .blue) :
    DirectSparseAffineVertexRequestAppender decider := by
  exact
    RetainedInputAppendPipeline.appendedComputableInPolyTimeOfFourAppendersEq
    (directSparseComputedAffineIndexedTripleRequestsOfSymbols decider)
    (directSparseComputedAffineIndexedElementRequestsOfSymbols decider .red)
    (directSparseComputedAffineIndexedElementRequestsOfSymbols decider .green)
    (directSparseComputedAffineIndexedElementRequestsOfSymbols decider .blue)
    (directSparseComputedAffineVertexRequestsOfSymbols decider)
    (fun symbols => by
      rw [directSparseComputedAffineVertexRequestsOfSymbols_eq_indexed,
        directSparseComputedAffineIndexedVertexRequestsOfSymbols_eq_blocks]
      simp only [List.append_assoc])
    triples red green blue

end PeriodicCNFStripReduction
end LeanTrominoes
