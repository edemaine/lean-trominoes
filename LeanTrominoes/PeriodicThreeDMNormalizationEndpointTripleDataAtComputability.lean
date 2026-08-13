/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationColorSelectionComputability

/-!
# Primitive-recursive endpoint-triple data lookup

Look up the optional endpoint triple at a vertex and immediately compress it
to the finite side/color data used by the remaining normalization controls.
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

def endpointTripleDataAt
    (input : Input × PeriodicThreeDMVertex) : Option EndpointTripleData :=
  match input.1.problem.endpointTripleAt input.2 with
  | none => none
  | some endpoints => some (endpointTripleData (input.1, endpoints))

theorem endpointTripleDataAt_primrec :
    Primrec endpointTripleDataAt := by
  let AtVertex := Input × PeriodicThreeDMVertex
  have problemAndVertex : Primrec (fun input : AtVertex =>
      (input.1.problem, input.2)) :=
    Primrec.pair
      (Input.problem_primrec.comp Primrec.fst) Primrec.snd
  have triple : Primrec (fun input : AtVertex =>
      input.1.problem.endpointTripleAt input.2) := by
    exact (endpointTripleAt_primrec.comp problemAndVertex).of_eq
      fun _ => rfl
  have selected : Primrec₂ fun (input : AtVertex)
      (endpoints : EndpointTriple) =>
      some (endpointTripleData (input.1, endpoints)) := by
    exact (Primrec.option_some.comp
      (endpointTripleData_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂
  exact (Primrec.option_casesOn triple (Primrec.const none)
    selected).of_eq fun input => by
      unfold endpointTripleDataAt
      cases input.1.problem.endpointTripleAt input.2 <;> rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
