/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineIndexedEmitterPipelineCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTablePhaseData

/-! # Generated five-phase affine table compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open GadgetSparseAffineIndexedEmitter

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineTableGeneratedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compose the verified uniform unary-program generator with the shared
five-phase indexed affine-record pipeline. -/
noncomputable def directSparseAffineTablePhaseOutputComputableInPolyTime
    (phases : DirectSparseAffineTablePhaseFamilies decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List GadgetSparseAffineVertexTokens.Token)
      encoding.Γ GadgetSparseAffineVertexTokens.Token id id
      (DirectSparseAffineTablePhaseFamilies.output decider phases) := by
  unfold DirectSparseAffineTablePhaseFamilies.output
  exact TM2CompositionMachine.computableInPolyTime
    (PeriodicCNF.PolySpaceRequestEmitter.sourceTokensComputableInPolyTime
      decider)
    (emittedPhasesComputableInPolyTime phases.families)

end PeriodicCNFStripReduction
end LeanTrominoes
