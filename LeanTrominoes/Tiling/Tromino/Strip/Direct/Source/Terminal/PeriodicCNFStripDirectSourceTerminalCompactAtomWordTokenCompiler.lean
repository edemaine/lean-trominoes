/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorScanTokenCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Terminal.PeriodicCNFStripDirectSourceTerminalCompactAtomWordTokenData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Direct compiler for source-terminal compact atom-word tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
