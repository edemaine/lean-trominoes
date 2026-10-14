/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorAffineCrossingData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct affine crossing-marker compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The direct affine descriptor-pair crossing scan is polynomial-time. -/
noncomputable def directSourceAffineCrossingMarkersComputableInPolyTime
    {Marker : Type} [Fintype Marker] [Inhabited Marker]
    (marker : Marker) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List Marker)
      encoding.Γ Marker
      id id (directSourceAffineCrossingMarkers decider marker) := by
  let fields :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let crossings :=
    RouteDescriptorPairAffine.compiledAffineCrossingMarkerStreamComputableInPolyTime
      marker
  let complete :=
    TM2CompositionMachine.computableInPolyTime fields crossings
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List Marker) encoding.Γ Marker id id
    (fun symbols =>
      RouteDescriptorPairAffine.compiledAffineCrossingMarkerStream marker
        (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact complete

end PeriodicCNFStripReduction
end LeanTrominoes

end
