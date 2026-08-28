/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordData

/-! # Target-vertex atom-word tokens for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTargetAtomWordTokenDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Physical source-atom words projected from direct numeric descriptors. -/
def directSourceTargetAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  PeriodicOrthocrossing.RouteDescriptorTargetAtomWords.tokens
    (directSourceRouteDescriptorScanTokens decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
