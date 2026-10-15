/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorTokenData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorScanTokens

/-! # Normalized route-descriptor scan tokens for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Minimal record-delimited unary input for the descriptor crossing scan. -/
def directSourceRouteDescriptorScanTokens (symbols : List encoding.Γ) :
    List PeriodicOrthocrossing.RouteDescriptorScanTokens.Token :=
  PeriodicOrthocrossing.RouteDescriptorScanTokens.normalize
    (directSourceRouteDescriptorTokens decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
