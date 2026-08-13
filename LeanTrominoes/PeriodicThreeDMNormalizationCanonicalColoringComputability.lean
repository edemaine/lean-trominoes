/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointTripleDataAtComputability

/-!
# Computability of canonical normalized port colors

Transport each old-side endpoint color through the finite first-round
boundary permutation.
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

/-- Canonical port color computed solely from the compressed fan data. -/
def canonicalColorFromData
    (input : Option EndpointTripleData × CanonicalVertexPort) : WireColor :=
  match input.1 with
  | none => .red
  | some data =>
      let omitted := omittedSide data.1.1 data.2.1.1 data.2.2.1
      colorFromTripleData (boundarySide omitted input.2, data)

theorem canonicalColorFromData_primrec :
    Primrec canonicalColorFromData :=
  Primrec.dom_finite _

theorem canonicalColorFromData_endpointTripleDataAt
    (input : Input × PeriodicThreeDMVertex)
    (port : CanonicalVertexPort) :
    canonicalColorFromData (endpointTripleDataAt input, port) =
      canonicalColoringAt input.1 input.2 port := by
  unfold canonicalColorFromData endpointTripleDataAt
    canonicalColoringAt endpointColorAtSide omittedSideAt
  cases input.1.problem.endpointTripleAt input.2 with
  | none => rfl
  | some endpoints =>
      rcases endpoints with ⟨first, second, third⟩
      rfl

theorem canonicalColoringAt_primrec :
    Primrec fun input :
      (Input × PeriodicThreeDMVertex) × CanonicalVertexPort =>
      canonicalColoringAt input.1.1 input.1.2 input.2 := by
  have data : Primrec (fun input :
      (Input × PeriodicThreeDMVertex) × CanonicalVertexPort =>
      endpointTripleDataAt input.1) :=
    endpointTripleDataAt_primrec.comp Primrec.fst
  exact (canonicalColorFromData_primrec.comp
    (Primrec.pair data Primrec.snd)).of_eq fun input =>
      canonicalColorFromData_endpointTripleDataAt input.1 input.2

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
