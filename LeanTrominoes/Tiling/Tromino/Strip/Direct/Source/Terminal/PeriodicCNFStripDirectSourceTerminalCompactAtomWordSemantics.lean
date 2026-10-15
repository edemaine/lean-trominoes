/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Terminal.PeriodicCNFStripDirectSourceTerminalCompactAtomWordData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorScanTokenSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordSemantics

/-! # Exact semantics of direct-source source-terminal compact words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directSourceTerminalCompactSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceTerminalCompactAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceTerminalCompactAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceTerminalCompactAtomWords decider symbols) := by
  unfold directSourceTerminalCompactAtomWords
  have physicalEq :
      directSourceTerminalCompactAtomWordTokens decider symbols =
        DelimitedBinaryWords.encode
          (RouteDescriptorSourceTerminalCompactWords.words
            (numericRouteDescriptors
              (directSourceFormula decider symbols))) := by
    unfold directSourceTerminalCompactAtomWordTokens
      directSourceRouteDescriptorScanTokens
      directSourceRouteDescriptorTokens
    rw [RouteDescriptorScanTokens.normalize_routeDescriptorTokens]
    exact RouteDescriptorSourceTerminalCompactWords.tokens_encode _
  rw [physicalEq]
  simp

end PeriodicCNFStripReduction
end LeanTrominoes

end
