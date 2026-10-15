/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorWordPairData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairFieldTags

/-! # Tagged descriptor-pair fields for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Side-and-field-tagged unary units for every ordered direct descriptor
pair. -/
def directSourceRouteDescriptorPairFieldTags
    (symbols : List encoding.Γ) :
    List PeriodicOrthocrossing.RouteDescriptorPairFieldTags.Token :=
  PeriodicOrthocrossing.RouteDescriptorPairFieldTags.inputTokens
    (directSourceRouteDescriptorWordPairs decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
