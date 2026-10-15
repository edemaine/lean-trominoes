/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorBinaryWordData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorBinaryWordSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorScanTokenSemantics

/-! # Exact semantics of direct-source descriptor words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable local instance directSourceRouteDescriptorBinaryWordSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct physical token stream is precisely the canonical encoding of
the semantic descriptor-word list. -/
theorem directSourceRouteDescriptorBinaryWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorBinaryWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceRouteDescriptorBinaryWords decider symbols) := by
  unfold directSourceRouteDescriptorBinaryWordTokens
    directSourceRouteDescriptorScanTokens
    directSourceRouteDescriptorTokens
    directSourceRouteDescriptorBinaryWords
  rw [RouteDescriptorScanTokens.normalize_routeDescriptorTokens]
  exact RouteDescriptorBinaryWords.tokens_encode _

end PeriodicCNFStripReduction
end LeanTrominoes

end
