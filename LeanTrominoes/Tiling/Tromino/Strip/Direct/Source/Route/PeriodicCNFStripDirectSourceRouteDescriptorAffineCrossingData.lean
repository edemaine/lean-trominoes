/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingStreamCompiler

/-! # Direct affine crossing-marker data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Direct-source symbols interpreted by the affine descriptor-pair crossing
scan. -/
def directSourceAffineCrossingMarkers
    {Marker : Type} (marker : Marker)
    (symbols : List encoding.Γ) :
    List Marker :=
  RouteDescriptorPairAffine.compiledAffineCrossingMarkerStream
    marker
    (directSourceRouteDescriptorPairFieldTags decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
