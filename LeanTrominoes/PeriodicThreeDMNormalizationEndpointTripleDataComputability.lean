/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointDataComputability

/-!
# Primitive-recursive normalized endpoint-triple data

Assemble the side/color records for the three endpoints at one vertex.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- Side/color records for all three members of an endpoint triple. -/
def endpointTripleData
    (input : Input × EndpointTriple) : EndpointTripleData :=
  (endpointSideColor (input.1, input.2.1),
    endpointSideColor (input.1, input.2.2.1),
    endpointSideColor (input.1, input.2.2.2))

theorem endpointTripleData_primrec :
    Primrec endpointTripleData := by
  have compilerInput : Primrec (fun input : Input × EndpointTriple =>
      input.1) := Primrec.fst
  have firstEndpoint : Primrec (fun input : Input × EndpointTriple =>
      input.2.1) := Primrec.fst.comp Primrec.snd
  have secondEndpoint : Primrec (fun input : Input × EndpointTriple =>
      input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have thirdEndpoint : Primrec (fun input : Input × EndpointTriple =>
      input.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have first := endpointSideColor_primrec.comp
    (Primrec.pair compilerInput firstEndpoint)
  have second := endpointSideColor_primrec.comp
    (Primrec.pair compilerInput secondEndpoint)
  have third := endpointSideColor_primrec.comp
    (Primrec.pair compilerInput thirdEndpoint)
  exact (Primrec.pair first (Primrec.pair second third)).of_eq
    fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
