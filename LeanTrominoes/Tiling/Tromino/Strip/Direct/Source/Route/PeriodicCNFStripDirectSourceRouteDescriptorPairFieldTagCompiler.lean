/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorWordPairCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Direct compiler for tagged descriptor-pair fields -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Direct source symbols compile to the exact tagged unary descriptor-pair
stream in polynomial time. -/
noncomputable def directSourceRouteDescriptorPairFieldTagsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List PeriodicOrthocrossing.RouteDescriptorPairFieldTags.Token)
      encoding.Γ
      PeriodicOrthocrossing.RouteDescriptorPairFieldTags.Token
      id id
      (fun symbols =>
        directSourceRouteDescriptorPairFieldTags decider symbols) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorWordPairsComputableInPolyTime decider)
    PeriodicOrthocrossing.RouteDescriptorPairFieldTags.inputTokensComputableInPolyTime
  simpa only [directSourceRouteDescriptorPairFieldTags] using composed

end PeriodicCNFStripReduction
end LeanTrominoes

end
