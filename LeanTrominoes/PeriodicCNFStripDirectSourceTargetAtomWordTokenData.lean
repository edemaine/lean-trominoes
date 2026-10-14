/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordData

/-! # Target-vertex atom-word tokens for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Physical source-atom words projected from direct numeric descriptors. -/
def directSourceTargetAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  PeriodicOrthocrossing.RouteDescriptorTargetAtomWords.tokens
    (directSourceRouteDescriptorScanTokens decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
