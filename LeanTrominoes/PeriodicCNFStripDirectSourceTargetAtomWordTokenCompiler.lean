/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceTargetAtomWordTokenData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compiler for target-vertex atom-word tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTargetAtomWordTokenCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct symbols compile to one indexed source-atom word per route
descriptor in polynomial time. -/
noncomputable def directSourceTargetAtomWordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List DelimitedBinaryWords.Token)
      encoding.Γ DelimitedBinaryWords.Token
      id id (fun symbols =>
        directSourceTargetAtomWordTokens decider symbols) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorScanTokensComputableInPolyTime decider)
    PeriodicOrthocrossing.RouteDescriptorTargetAtomWords.tokensComputableInPolyTime
  simpa only [directSourceTargetAtomWordTokens] using composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
