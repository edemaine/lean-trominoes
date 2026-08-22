/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordTokenData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compiler for binary route-descriptor word tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorBinaryWordTokenCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct source symbols are compiled to binary descriptor words in
polynomial time. -/
noncomputable def directSourceRouteDescriptorBinaryWordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token
      id id (fun symbols =>
        directSourceRouteDescriptorBinaryWordTokens decider symbols) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorScanTokensComputableInPolyTime decider)
    PeriodicOrthocrossing.RouteDescriptorBinaryWords.tokensComputableInPolyTime
  simpa only [directSourceRouteDescriptorBinaryWordTokens] using composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
