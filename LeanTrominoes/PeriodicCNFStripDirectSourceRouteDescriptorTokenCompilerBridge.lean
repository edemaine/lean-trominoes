/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceUnliftedRouteDescriptorTokens
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteTokenSourceCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct route-token compiler from a generic flat-CNF emitter -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteTokenCompilerBridgeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A generic polynomial-time emitter on flat source CNFs composes with the
already verified PSPACE source-formula compiler to supply the direct route
token boundary. -/
noncomputable def directSourceRouteDescriptorTokenCompilerOfSourceSplit
    (sourceCompiler :
      PeriodicCNF.SourceSplitRouteDescriptorTokens.Compiler) :
    DirectSourceRouteDescriptorTokenCompiler decider := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteTokenSourceComputableInPolyTime decider)
    sourceCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed fun symbols => by
      simpa [PeriodicCNF.SourceSplitRouteDescriptorTokens.tokens] using
        (directSourceRouteDescriptorTokens_eq_sourceSplitDescriptors
          decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction
