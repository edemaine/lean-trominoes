/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordData

/-! # Source-terminal compact atom-word tokens for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


def directSourceTerminalCompactAtomWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  PeriodicOrthocrossing.RouteDescriptorSourceTerminalCompactWords.tokens
    (directSourceRouteDescriptorScanTokens decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
