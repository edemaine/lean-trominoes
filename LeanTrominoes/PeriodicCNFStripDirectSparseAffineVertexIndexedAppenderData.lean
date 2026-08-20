/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestIndexedData
import LeanTrominoes.RetainedInputAppendFourPipeline

/-! # Four retained-input indexed vertex-appender interfaces -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineIndexedAppenderDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Indexed triple request block generated from direct source symbols. -/
def directSparseComputedAffineIndexedTripleRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  directSparseComputedAffineIndexedTripleRequests source input

/-- One indexed constant-color element block generated from source symbols. -/
def directSparseComputedAffineIndexedElementRequestsOfSymbols
    (color : WireColor) (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  directSparseComputedAffineIndexedElementRequests source input color

@[simp] theorem directSparseComputedAffineIndexedVertexRequestsOfSymbols_eq_blocks
    (symbols : List encoding.Γ) :
    directSparseComputedAffineIndexedVertexRequestsOfSymbols
        decider symbols =
      directSparseComputedAffineIndexedTripleRequestsOfSymbols
          decider symbols ++
        (directSparseComputedAffineIndexedElementRequestsOfSymbols
            decider .red symbols ++
          (directSparseComputedAffineIndexedElementRequestsOfSymbols
              decider .green symbols ++
            directSparseComputedAffineIndexedElementRequestsOfSymbols
              decider .blue symbols)) := by
  rfl

abbrev DirectSparseAffineIndexedWorkspace :=
  encoding.Γ ⊕ GadgetSparseAffineVertexTokens.Token

/-- First pass: retain source symbols and append indexed triple requests. -/
abbrev DirectSparseAffineIndexedTripleAppender :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appended
      (directSparseComputedAffineIndexedTripleRequestsOfSymbols decider))

/-- Later pass: retain the shared workspace and append one indexed color
block, reading only the retained source symbols. -/
abbrev DirectSparseAffineIndexedElementAppender (color : WireColor) :=
  TM2ComputableInPolyTime id id
    (RetainedInputAppendPipeline.appendFromWorkspace
      (directSparseComputedAffineIndexedElementRequestsOfSymbols
        decider color))

end PeriodicCNFStripReduction
end LeanTrominoes
