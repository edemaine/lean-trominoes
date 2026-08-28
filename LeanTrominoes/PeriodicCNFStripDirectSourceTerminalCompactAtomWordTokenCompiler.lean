/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCompactAtomWordTokenData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compiler for source-terminal compact atom-word tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceTerminalCompactTokenCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceTerminalCompactAtomWordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token
      id id (directSourceTerminalCompactAtomWordTokens decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List DelimitedBinaryWords.Token)
    encoding.Γ DelimitedBinaryWords.Token id id
    (fun symbols =>
      PeriodicOrthocrossing.RouteDescriptorSourceTerminalCompactWords.tokens
        (directSourceRouteDescriptorScanTokens decider symbols))
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorScanTokensComputableInPolyTime decider)
    PeriodicOrthocrossing.RouteDescriptorSourceTerminalCompactWords.tokensComputableInPolyTime
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
