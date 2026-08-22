/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorTokenCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct compiler for normalized route-descriptor scan tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorScanTokenCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact direct route descriptors followed by the fixed normalizer yield
the minimal crossing-scan input in polynomial time. -/
noncomputable def directSourceRouteDescriptorScanTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicOrthocrossing.RouteDescriptorScanTokens.Token)
      encoding.Γ
      PeriodicOrthocrossing.RouteDescriptorScanTokens.Token
      id id (fun symbols =>
        directSourceRouteDescriptorScanTokens decider symbols) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorTokenCompiler decider)
    PeriodicOrthocrossing.RouteDescriptorScanTokens.normalizeComputableInPolyTime
  simpa only [directSourceRouteDescriptorScanTokens] using composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
